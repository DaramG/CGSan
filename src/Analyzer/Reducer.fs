module Analyzer.Reducer

open System.Collections

open LLIR
open LLIR.Core
open Common
open PathOptimizer
open PathOptimizer.ConstantFolding

type Cache = CacheICFG<bool>

let mkNonOptCache () = new Cache ()
let mkOptCache () = new Cache ()

let reduceEdges nodes edges =
  let fold edges node = Function.reduceReachableEdge (Set.init node) edges
  Array.fold fold edges nodes

let getDirectedCFG prog info fID defNode useInstr gcInstr gcID =
  let cfg = Program.getFunc prog fID |> ICFG.ofFunc false
  let nodes = [| defNode; fst useInstr; fst gcInstr |]
  let edges = ICFG.getEdges cfg |> reduceEdges nodes
  ICFG.setEdges edges cfg

let doReduceNonOpt prog cache info gcInstr gcID cfg = cfg

let reduceNonOpt prog info cache fID defNode useInstr gcInstr gcID =
  getDirectedCFG prog info fID defNode useInstr gcInstr gcID
  |> doReduceNonOpt prog cache info gcInstr gcID

let reduceCFG cfg targets =
  ICFG.setEdges (ICFG.getEdges cfg |> reduceEdges targets) cfg

let gcCache = new Concurrent.ConcurrentDictionary<ID * ConstArgs, ICFG<bool>> ()
let hasCache = new Concurrent.ConcurrentDictionary<ID * ConstArgs, bool> ()

let hasGC info cache inProc cfg =
  let rec hasGC inProc cfg =
    let key = cfg.ID, cfg.Args
    if ICFG.isMerged cfg then calcHasGC inProc cfg
    elif Set.contains key inProc then false
    else
      match hasCache.TryGetValue key with
      | true, ret -> ret
      | false, _ -> calcHasGC inProc cfg

  and calcHasGC inProc cfg =
    let fID = ICFG.getID cfg
    if Info.isBasicGC info fID then true
    else
      let inProc = Set.add (cfg.ID, cfg.Args) inProc
      match ICFG.resolve cache cfg with
      | Some cfg -> Info.getGcCalls info fID |> Set.exists (existGC inProc cfg)
      | _ -> false

  and existGC inProc cfg (instPos, _) =
    match ICFG.tryGetCall cfg instPos with
    | Some cfg -> hasGC inProc cfg
    | _ -> false

  hasGC inProc cfg

let doReduceOpt prog fID cache info gcInstr gcID nodes cfg =
  let state = State.init prog false cache
  let hasGC = hasGC info cache

  let merge fID = function
    | [||] -> ICFG.empty fID true
    | [|cfg|] -> cfg
    | cfgs -> Array.pop cfgs ||> Array.fold ICFG.merge

  let checkHasGC cfg gcInstr =
    match ICFG.tryGetCall cfg gcInstr with
    | Some ccfg ->
      let key = ccfg.ID, ccfg.Args
      hasCache.GetOrAdd (key, fun _ -> hasGC Set.empty ccfg)
    | _ -> false

  let rec getGcCFG inProc gcID cArgs =
    let key = gcID, cArgs
    if Set.contains key inProc then ICFG.dummyRec gcID false cArgs None
    else gcCache.GetOrAdd (key, calcGcCFG (Set.add key inProc))

  and addGetNxtCFG inProc gcInstr gcID =
    let getter state instrPos fID cArgs =
      if gcInstr = instrPos && gcID = fID then
        getGcCFG inProc gcID cArgs |> Some
      else State.defaultGetNxtCFG state instrPos fID cArgs
    State.setGetNxtCFG state getter

  and calcGcCFG inProc (gcID, cArgs) =
    let cfg = Program.getFunc prog gcID |> ICFG.ofFunc true
    let cfg = ICFG.setArgs cfg cArgs
    let rec choose cfg (gcInstr, gcID2) =
      let cfg = reduceCFG cfg [|fst gcInstr|]
      let state = addGetNxtCFG inProc gcInstr gcID2
      let cfg = ConstantFolding.start state gcID cfg
      let ret = reduceCFG cfg [|fst gcInstr|]
      if ICFG.isEqual cfg ret then
        if checkHasGC ret gcInstr then Some cfg else None
      else choose ret (gcInstr, gcID2)

    if Info.isBasicGC info gcID then cfg
    else
      Info.getGcCalls info gcID |> Set.toArray |> Array.choose (choose cfg)
      |> merge gcID

  let rec loop cfg =
    let state = addGetNxtCFG Set.empty gcInstr gcID
    let cfg = ConstantFolding.start state fID cfg
    let ret = reduceCFG cfg nodes
    if ICFG.isEqual cfg ret then
      if checkHasGC ret gcInstr then ret else ICFG.empty (ICFG.getID cfg) true
    else loop ret
  loop cfg

let reduceOpt prog info cache fID defNode useInstr gcInstr gcID =
  let nodes = [|defNode; fst useInstr; fst gcInstr|]
  getDirectedCFG prog info fID defNode useInstr gcInstr gcID
  |> doReduceOpt prog fID cache info gcInstr gcID nodes
