namespace Analyzer

open System.Collections

open LLIR
open LLIR.Core
open Common
open PathOptimizer
open Analyzer.Reducer

type VStateType =
  | Start
  | Def
  | GcStart
  | GcCalled

type GcLevel =
  | MustGC
  | MayGC
  | NoGC

type VState = {
  ID: ID
  UseInstr: InstPos
  GcInstr: InstPos
  GcEdges: (Edges * Edges) list
  GcNodes: Set<BlockID> list
  GcLevels: GcLevel list
  Type: VStateType
  ICFGs: (ICFG<bool> option) list
  Cache: Cache
}

module VState =
  let DKEY = false

  let empty cache = {
    ID = ""
    Type = Start
    GcInstr = -1, -1
    UseInstr = -1, -1
    ICFGs = []
    GcEdges = []
    GcNodes = []
    GcLevels = []
    Cache = cache
  }

  let private addEdge cur nxt edges =
    let set = Map.findSet cur edges |> Set.add nxt
    Map.add cur set edges

  let private inStart vstate =
    match vstate.ICFGs with
    | [_] -> true
    | _ -> false

  let init useOpt info prog cache result =
    let fID = Result.getFuncID result
    let gcID, gcInstr = Result.getGcInstr result
    let defNode = Result.getDefNode result
    let useInstr = Result.getUseInstr result
    let cfg =
      if useOpt then
        reduceOpt prog info cache fID defNode useInstr gcInstr gcID
      else reduceNonOpt prog info cache fID defNode useInstr gcInstr gcID
    let toGcEdges =
      Function.reduceDirectedEdge (fst gcInstr |> Set.init) cfg.Edges
    let retGcEdges =
      Function.calcReachableEdges (fst gcInstr |> Set.init) cfg.Edges
      |> Function.reduceDirectedEdge (fst useInstr |> Set.init)
    {
      ID = fID
      GcInstr = gcInstr
      UseInstr = useInstr
      Type = Start
      ICFGs = [Some cfg]
      GcLevels = [MustGC]
      GcEdges = [toGcEdges, retGcEdges]
      GcNodes = [Set.init (fst gcInstr)]
      Cache = cache
    }

  let hasEdge vstate fr to_ =
    let b1 =
      match vstate.ICFGs with
      | Some cfg :: _ -> ICFG.hasEdge cfg fr to_
      | _ -> true
    let b2 =
      match vstate.Type, vstate.GcLevels with
      | GcStart, MustGC :: _ ->
        List.head vstate.GcEdges |> fst |> Map.findSet fr |> Set.contains to_
      | GcCalled, _ when inStart vstate ->
        List.head vstate.GcEdges |> snd |> Map.findSet fr |> Set.contains to_
      | _ when inStart vstate ->
        List.head vstate.GcEdges |> fst |> Map.findSet fr |> Set.contains to_
      | _ -> true
    b1 && b2

  let isReachable vstate inStart fr to_ =
    if hasEdge vstate fr to_ then Some vstate
    else None

  let rec toEdge ret bf = function
    | cur :: remain ->
      let ret =
        if bf >= 0 then Map.add bf (Map.findSet bf ret |> Set.add cur) ret
        else ret
      toEdge ret cur remain
    | [] -> ret

  let check info cache conf vstate =
    match vstate.ICFGs with
    | [Some cfg] ->
      let b1 = ICFG.hasRet cfg
      let b2 = ICFG.isReachable cfg vstate.GcInstr vstate.UseInstr
      if b1 && b2 then Some vstate
      else None
    | _ -> Some vstate

  let callGC (vstate: VState) = { vstate with Type = GcCalled }

  let gcCalled vstate = vstate.Type = GcCalled

  let isEnd inStart iID vstate =
    inStart && gcCalled vstate && iID = vstate.UseInstr

  let isGC inStart iID vstate =
    inStart && (gcCalled vstate |> not) && iID = vstate.GcInstr

  let getNxt vstate bID iID =
    match vstate.ICFGs with
    | [] -> failwith "error"
    | Some cfg :: _ ->
      match ICFG.tryGetCall cfg (bID, iID) with
      | Some cfg -> ICFG.resolve vstate.Cache cfg
      | _ -> None
    | _ -> None

  let callHasGC info cache cfg instPos =
    match ICFG.tryGetCall cfg instPos with
    | Some cfg -> Reducer.hasGC info cache Set.empty cfg
    | _ -> false

  let isMustGC info cache bID iID fID cfg =
    let nodes = Function.getReachables (Set.init bID) cfg.Edges
    let exists (instPos, _) =
      let bID_, iID_ = instPos
      if Set.contains bID_ nodes then
        if bID = bID_ && iID >= iID_ then false
        else callHasGC info cache cfg instPos
      else false
    Info.getGcCalls info cfg.ID |> Set.exists exists |> not

  let call info bID iID fID vstate =
    let cache = vstate.Cache
    let nxt = getNxt vstate bID iID
    let gcEdge = Info.getToGcEdges info fID, Info.getGcRetEdges info fID
    let gcNodes =
      let gcs = Info.getGcCalls info fID
      match nxt with
      | Some nxt -> Set.filter (fst >> callHasGC info cache nxt) gcs
      | _ -> gcs
      |> Set.filter (snd >> Info.isLoopGc info fID >> not)
      |> Set.map (fst >> fst)
    //printfn "%s: %A %A" fID (Set.map (fst >> fst) gcNodes) gcNodes2
    let isStart = inStart vstate
    let preGcNodes = List.head vstate.GcNodes
    let aloneGC = Set.count preGcNodes = 1 && Set.contains bID preGcNodes
    let isGC =
      if isStart then
        if (bID, iID) = vstate.GcInstr then true else false
      else
        match vstate.Type, nxt with
        | GcStart, Some nxt -> Reducer.hasGC info vstate.Cache Set.empty nxt
        | _ -> false
    let level =
      if isGC then
        let cur = List.head vstate.ICFGs |> Option.get
        match vstate.Type, List.head vstate.GcLevels with
        | GcStart, MustGC
          when isStart || aloneGC
               || isMustGC info vstate.Cache bID iID fID cur ->
          MustGC
        | _ -> MayGC
      else NoGC
    { vstate with ICFGs = nxt :: vstate.ICFGs
                  GcLevels = level :: vstate.GcLevels
                  GcNodes = gcNodes :: vstate.GcNodes
                  GcEdges = gcEdge :: vstate.GcEdges }

  let pop vstate =
    { vstate with ICFGs = List.tail vstate.ICFGs
                  GcLevels = List.tail vstate.GcLevels
                  GcNodes = List.tail vstate.GcNodes
                  GcEdges = List.tail vstate.GcEdges }

  let startGC (vstate: VState) = { vstate with Type = GcStart }
  let gcStart (vstate: VState) = vstate.Type = GcStart

  let debug (vstate: VState) =
    match vstate.ICFGs with
    | [Some cfg] -> ICFG.debug cfg
    | _ -> ()
