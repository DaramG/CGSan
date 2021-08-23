namespace Analyzer

open LLVM
open LLIR
open LLIR.Core
open Common

type Target =
  | V8
  | MOZ
  | TEST

type Conf = {
  Target: Target
  IsGC: ID -> bool
  CheckTimeout: int // ms
  VerifyTimeout: int
  Cores: int
  GetHeapMDs: Program -> Metadatas
}

type InstPos = BlockID * int

module InstPos =
  let toStr (bID, idx) = sprintf "Block Pos: %d, Inst Pos: %d" bID idx

module Conf =
  let v8Whites = [|"_ZTSN2v88internal6ObjectE"|]
  let v8Blacks = [|"_ZTSN2v88internal3SmiE"|]

  let private getHeapMDs whites blacks prog =
    let choose (ptr, md) =
      match md with
      | CompositeType (Class, _, id, _, _, _)
      | CompositeType (Structure, _, id, _, _, _)
        when Array.contains id whites ->
        Some ptr
      | _ -> None

    let mds = Program.getMDs prog |> Map.toArray
    let objects = Array.Parallel.choose choose mds
    let filter (ptr, md) =
      match md with
      | CompositeType (Class, _, id, _, _, _)
      | CompositeType (Structure, _, id, _, _, _)
      | DerivedType (TypeDef, id, _, _)
      | DerivedType (Inherit, id, _, _)
        when Array.contains id blacks |> not
             && Array.exists (fun o -> Metadata.isSubMD prog o ptr) objects ->
        Some (ptr, md)
      | _ -> None

    Array.Parallel.choose filter mds |> Map.ofArray

  let v8 = {
    Target = V8
    IsGC = (fun x -> x.Contains("CollectGarbage"))
    CheckTimeout = 10*1000
    VerifyTimeout = 10*60*1000
    Cores = 20
    GetHeapMDs = getHeapMDs v8Whites v8Blacks
  }

  let private mozGCs =
    [|
      "_ZN2js2gc9GCRuntime2gcE18JSGCInvocationKindN2JS8GCReasonE"
      "_ZN2js2gc9GCRuntime13gcIfRequestedEv"
    |] |> Set.ofArray

  let getMozHeapMDs prog =
    let mozBlacks = [|"_ZTSN2JS5RealmE"|]
    let mozWhites = [|"_ZTSN2JS5ValueE"; "_ZTSN2JS11PropertyKeyE"|]
    let mozWhitePtrs = [|"_ZTSN2js2gc4CellE"|]
    let ret1 = getHeapMDs mozWhites mozBlacks prog
    let ptrs = getHeapMDs mozWhitePtrs mozBlacks prog
    let ret2 =
      let filter _ = function
        | DerivedType (Ptr, _, base_, _) when Map.containsKey base_ ptrs -> true
        | _ -> false
      Program.getMDs prog |> Map.filter filter
    Map.union [|ret1; ret2|]

  let private moz = {
    Target = MOZ
    IsGC = (fun x -> Set.contains x mozGCs)
    CheckTimeout = 100*1000
    VerifyTimeout = 10*60*1000
    Cores = 20
    GetHeapMDs = getMozHeapMDs
  }

  let private testGCs = [| "_Z2GCP7Context" |] |> Set.ofArray
  let private testType = [| "_ZTS6Object" |]
  let private getTestHeapMDs prog =
    let bases = getHeapMDs testType [||] prog
    let filter ptr md =
      match md with
      | DerivedType (kind, _, r, _) when Metadata.isReducedKind kind |> not ->
        Map.containsKey r bases
      | _ -> false
    Program.getMDs prog |> Map.filter filter

  let private test = {
    Target = TEST
    IsGC = (fun x -> Set.contains x testGCs)
    CheckTimeout = 10*1000
    VerifyTimeout = 600*1000
    Cores = 1
    GetHeapMDs = getTestHeapMDs
  }

  let ofEngine = function
    | "v8" -> v8
    | "moz" -> moz
    | "test" -> test
    | engine -> failwithf "Not support %s" engine
