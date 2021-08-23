namespace Analyzer

open LLVM
open LLIR
open LLIR.Core
open Common

type Edges = Map<BlockID, Set<BlockID>>

type Info = {
  Prog: Program
  GcCalls: Map<ID, Set<InstPos * ID>>
  BasicGCs: Set<ID>
  CandEdges: Map<ID * InstPos, Set<BlockID * BlockID>>
  ToGcEdges: Map<ID, Edges>
  GcRetEdges: Map<ID, Edges>
  GcNodes: Map<ID, Set<BlockID>>
  HeapMDs: Metadatas
  Methods: Set<ID>
  GcLoops: Map<ID, Set<ID>>
}

type LoopCtx = {
  Stack: ID list
  InStack: Set<ID>
  IdxMap: Map<ID, int>
  LowMap: Map<ID, int>
  Idx: int
  Ret: Map<ID, Set<ID>>
}

module LoopCtx =
  let empty = {
    Stack = []
    InStack = Set.empty
    IdxMap = Map.empty
    LowMap = Map.empty
    Idx = 0
    Ret = Map.empty
  }

  let getRet ctx = ctx.Ret

  let updateIdx id idx ctx = { ctx with IdxMap = Map.add id idx ctx.IdxMap }

  let updateLow id low ctx = { ctx with LowMap = Map.add id low ctx.LowMap }

  let updateMinLow dst src ctx =
    let d = Map.find dst ctx.LowMap
    let s = Map.find src ctx.LowMap
    updateLow dst (min d s) ctx

  let updateMinLow2 dst idx ctx =
    let d = Map.find dst ctx.LowMap
    updateLow dst (min d idx) ctx

  let push id ctx =
    { ctx with Stack = id :: ctx.Stack; InStack = Set.add id ctx.InStack }

  let pop ctx =
    let ret = List.head ctx.Stack
    ret,
    { ctx with Stack = List.tail ctx.Stack
                       InStack = Set.remove ret ctx.InStack }

  let incIdx ctx = { ctx with Idx = ctx.Idx + 1}

  let nxt fID ctx =
    let idx = ctx.Idx
    updateIdx fID idx ctx |> updateLow fID idx |> push fID |> incIdx

  let tryFindIdx fID ctx = Map.tryFind fID ctx.IdxMap

  let inStack fID ctx = Set.contains fID ctx.InStack
  let hasIdx fID ctx = Map.containsKey fID ctx.IdxMap

  let popUntil fID ctx =
    let rec loop (ret, ctx) =
      let cur, ctx = pop ctx
      let ret = Set.add cur ret
      if cur = fID then ret, ctx
      else loop (ret, ctx)
    loop (Set.empty, ctx)

  let fini fID ctx =
    if Map.find fID ctx.LowMap = Map.find fID ctx.IdxMap then
      let curRet, ctx = popUntil fID ctx
      let fold (ret: Map<ID, Set<ID>>) (id: ID) = Map.add id curRet ret
      let ret = Set.fold fold ctx.Ret curRet
      { ctx with Ret = ret }
    else ctx

module Info =
  let private calcBasicGCs conf funcs =
    Map.toArray funcs |> Array.map fst |> Array.filter conf.IsGC |> Set.ofArray

  let private collectCalleesByBlock func =
    let choose (varID, targets) =
      match targets with
      | Some [|target|] -> Some (varID, target)
      | _ -> None
    Function.getCalls func |> Map.toArray |> Array.choose choose

  let private collectCalls funcs =
    let map _ f = collectCalleesByBlock f |> Set.ofArray
    Map.map map funcs

  let private revCalls calls =
    let fold1 caller map (_, callee) =
      let set = Map.findSet callee map
      Map.add callee (Set.add caller set) map
    let fold2 map caller callees = Set.fold (fold1 caller) map callees
    Map.fold fold2 Map.empty calls

  let private contain (dst: string) (src: string) = dst.Contains src

  let private collectGcCalls calls gcs =
    let rev = revCalls calls
    let rec loop ret = function
      | [] -> ret
      | cur :: remain ->
        if Set.contains cur ret then loop ret remain
        else
          let callers = Map.findSet cur rev
          let ret = loop (Set.add cur ret) (Set.toList callers)
          loop ret remain
    let gcs = loop Set.empty (Set.toList gcs)
    let filter (_, x) = Set.contains x gcs
    let fold ret gc =
      let callee = Map.findSet gc calls |> Set.filter filter
      if Set.isEmpty callee then ret
      else Map.add gc callee ret
    Set.fold fold Map.empty gcs

  let private getHeapMD prog heapMDs md =
    let ptr = Metadata.reduceMD prog md |> fst
    Map.tryFind ptr heapMDs

  let private _isHeapMD prog heapMDs md =
    getHeapMD prog heapMDs md |> Option.isSome

  let private _isHeapPtrMD prog heapMDs md =
    match Metadata.reduceMD prog md |> snd with
    | DerivedType (kind, _, r, _) when Metadata.isReducedKind kind |> not ->
      _isHeapMD prog heapMDs (r, Program.getMD prog r)
    | _ -> false

  let private calcCandEdges prog heapMDs gcCalls =
    let isHeapRelated md =
      _isHeapPtrMD prog heapMDs md || _isHeapMD prog heapMDs md

    let filterUse fID =
      let func = Program.getFunc prog fID
      let args = Function.getArgsMD func
      let mds =
        match Function.getRetMD func with
        | Some md -> Array.append args [|md|]
        | _ -> args
      Array.exists isHeapRelated mds

    let calcNodes fID func =
      let callNodes = collectCalleesByBlock func
      let filter f =
        let choose ((bID, iID), id) = if f id then Some (bID, iID) else None
        Array.choose choose callNodes |> Set.ofArray
      let defNodes =
        if Function.getArgsMD func |> Array.exists isHeapRelated then Set.init 0
        else Set.empty
      let nodes = filter filterUse |> Set.map fst
      Set.unionMany [|defNodes; nodes |], Map.findSet fID gcCalls |> Set.map fst

    let fold (ret1, ret2, ret3, ret4) fID gcs =
      let func = Program.getFunc prog fID
      let defNodes, gcPosSet = calcNodes fID func
      let gcNodes = Set.map fst gcPosSet
      let fold2 ret1 gcPos =
        let gcNodes = fst gcPos |> Set.init
        let edges =
          Function.getEdges func |> Function.reduceDirectedEdge gcNodes
          |> Function.reduceReachableEdge defNodes
        let key = fID, gcPos
        Map.add key (Function.edgesToSet edges) ret1
      let gcRetEdges =
        Function.getEdges func |> Function.reduceReachableEdge gcNodes
      let gcEdges =
        Function.getEdges func |> Function.reduceDirectedEdge gcNodes
      Set.fold fold2 ret1 gcPosSet,
      Map.add fID gcEdges ret2,
      Map.add fID gcRetEdges ret3,
      Map.add fID gcNodes ret4
    Map.fold fold (Map.empty, Map.empty, Map.empty, Map.empty) gcCalls

  let private getMethods prog heapMDs =
    let choose ptr =
      match Program.getMD prog ptr with
      | SubProgram (_, fID, _, _) -> Some fID
      | _ -> None

    let getMethod = function
      | CompositeType (_, _, _, _, elems, _) -> Array.choose choose elems
      | DerivedType (kind, _, ptr, _) when Metadata.isReducedKind kind |> not ->
        match Program.getMD prog ptr with
        | CompositeType (_, _, _, _, elems, _) -> Array.choose choose elems
        | _ -> [||]
      | _ -> [||]
    Map.toArray heapMDs |> Array.map (snd >> getMethod) |> Array.concat
    |> Set.ofArray

  let init prog conf =
    let funcs = Program.getFuncs prog
    let heapMDs = conf.GetHeapMDs prog
    let basicGCs = calcBasicGCs conf funcs
    let calls = collectCalls funcs
    let gcCalls = collectGcCalls calls basicGCs
    let cands, gcs, gcRets, gcNodes = calcCandEdges prog heapMDs gcCalls
    {
      Prog = prog
      GcCalls = gcCalls
      BasicGCs = basicGCs
      CandEdges = cands
      ToGcEdges = gcs
      GcRetEdges = gcRets
      GcNodes = gcNodes
      HeapMDs = heapMDs
      Methods = getMethods prog heapMDs
      GcLoops = Map.empty
    }

  let getGcCalls info fID = Map.findSet fID info.GcCalls
  let getCandEdges info fID gcPos = Map.findSet (fID, gcPos) info.CandEdges
  let getCands conf info = Map.toArray info.CandEdges |> Array.map fst

  let isMethod info fID = Set.contains fID info.Methods
  let isBasicGC info fID = Set.contains fID info.BasicGCs
  let getBasicGCs info = info.BasicGCs
  let isGC info fID = Map.containsKey fID info.GcCalls
  let getFuncArgs info fID = Program.getFunc info.Prog fID |> Function.getArgsMD

  let getEdges info fID = Program.getFunc info.Prog fID |> Function.getEdges

  let getToGcEdges info fID =
    if isGC info fID then Map.find fID info.ToGcEdges
    else Program.getFunc info.Prog fID |> Function.getEdges

  let getGcRetEdges info fID =
    if isBasicGC info fID then Map.empty
    else
      match Map.tryFind fID info.GcRetEdges with
      | Some edges -> edges
      | _ -> Program.getFunc info.Prog fID |> Function.getEdges

  let getProg info = info.Prog

  let getHeapMDName info md =
    match getHeapMD info.Prog info.HeapMDs md with
    | Some (CompositeType (_, name, _, _, _, _)) -> Some name
    | Some (DerivedType (_, _, ptr, _)) ->
      match Program.getMD info.Prog ptr with
      | CompositeType (_, name, _, _, _, _) -> Some (name + "*")
      | _ -> None
    | _ -> None

  let getHeapPtrMDName info md =
    let prog = info.Prog
    let heapMDs = info.HeapMDs
    match Metadata.reduceMD prog md |> snd with
    | DerivedType (kind, _, r, _) when Metadata.isReducedKind kind |> not ->
      getHeapMDName info (r, Program.getMD prog r)
    | _ -> None

  let getGcNodes info name = Map.findSet name info.GcNodes

  let calcGcLoops info fIDs =
    let edges = info.GcCalls
    let rec calc ctx fID =
      if LoopCtx.hasIdx fID ctx then ctx
      else
        let ctx = LoopCtx.nxt fID ctx
        let fold ctx (_, fID_) =
          match LoopCtx.tryFindIdx fID_ ctx with
          | None -> calc ctx fID_ |> LoopCtx.updateMinLow fID fID_
          | Some idx ->
            if LoopCtx.inStack fID_ ctx then LoopCtx.updateMinLow2 fID idx ctx
            else ctx
        Map.findSet fID edges |> Set.fold fold ctx |> LoopCtx.fini fID
    { info with GcLoops = Set.fold calc LoopCtx.empty fIDs |> LoopCtx.getRet }

  let isLoopGc info fID gcID =
    let set = Map.findSet gcID info.GcLoops
    Set.contains fID set

  let debug info =
    let printGC caller sets =
      printfn "%s ->" caller
      Set.map snd sets |> Set.iter (printfn "    | %s")
    printfn "---------------------------------"
    Map.iter printGC info.GcCalls
    printfn "---------------------------------"
