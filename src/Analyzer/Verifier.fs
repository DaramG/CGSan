namespace Analyzer

open LLIR
open LLIR.Core
open Common
open SymExecutor
open SymExecutor.SymFunc
open PathOptimizer

open System

exception EndException

module Verifier =


  let gc fID info state iID retID args size =
    //printfn "GC!! %s" fID
    let state =
      let vstate = State.getUserState state
      if VState.gcStart vstate then
        State.setUserState (VState.callGC vstate) state
      else state
    skip fID state iID retID args size

  let mkGC info fID = fID, gc fID info

  let private mkSymMap info =
    Info.getBasicGCs info |> Set.toArray
    |> Array.map (mkGC info)
    |> Map.ofArray

  let private skips = [|
    "stream"
    "basic_"
  |]

  let private getSymFunc info symMap state (fID: ID) =
    match Map.tryFind fID symMap with
    | Some func -> Some func
    | _ -> if Array.exists (fID.Contains) skips then skip fID |> Some else None

  let private isReachable state bID iID =
    let f = State.getCurFunc state
    let cID = State.getCurBB state
    if cID = -1 || iID > 0 then Some state
    elif Function.hasEdge f cID bID then
      let vstate = State.getUserState state
      let inStart = State.inStartFunc state
      match VState.isReachable vstate inStart cID bID with
      | Some vstate -> State.setUserState vstate state |> Some
      | _ -> None
    else None

  let private stmtCb state iID =
    let inStart = State.inStartFunc state
    let vstate = State.getUserState state
    let bID = State.getCurBB state
    let pos = bID, iID
    if VState.isEnd inStart pos vstate then raise EndException
    elif VState.isGC inStart pos vstate then
      State.setUserState (VState.startGC vstate) state
    else state

  let private callCb info state iID fID =
    let bID = State.getCurBB state
    try
      let vstate = State.getUserState state |> VState.call info bID iID fID
      State.setUserState vstate state
    with
      | e ->
        State.debug state
        failwithf "%A" e

  let private returnCb state _ =
    let vstate = State.getUserState state |> VState.pop
    State.setUserState vstate state

  let private handleFlags prog =
    let map (id: string) glob =
      let expr = glob.Value
      let rw = glob.IsWritable
      if id.Contains ("FLAG_") then
        { glob with Value = Builder.mkUndef (Builder.getSize expr) }
      else glob
    Program.getGlobals prog |> Map.map map |> Program.setGlobals prog

  let prepare useOpt conf info prog cache result =
    let vstate = VState.init useOpt info prog cache result
    VState.check info cache conf vstate, result

  let private checkResult info = function
    | Some true, result, time -> Result.show info "Reachable" result time
    | Some false, result, time -> Result.show info "Unreachable" result time
    | None, result, time -> Result.show info "Timeout" result time

  let chooseTarget info target =
    match target with
    | Some vstate, result -> Some (vstate, result)
    | None, result ->
      Result.show info "Unreachable" result 0L
      None

  let minDistance = 0
  let maxDistance = 0xffffff
  let getMinDistance edges src dsts =
    let rec calc vNodes cur =
      if Set.contains cur dsts then 0
      elif Set.contains cur vNodes then maxDistance
      else
        match Map.tryFind cur edges with
        | Some nxts ->
          (Set.map (calc (Set.add cur vNodes)) nxts |> Set.minElement) + 1
        | _ -> maxDistance
    calc Set.empty src

  let forRet (state, _, bID, _) =
    let vstate = State.getUserState state
    match vstate.ICFGs with
    | Some icfg :: _ -> getMinDistance icfg.Edges bID icfg.RetNodes
    | _ ->
      let func = State.getCurFunc state
      getMinDistance func.Edges bID func.RetNodes

  let forTarget target task =
    let state, _, bID, _ = task
    let vstate = State.getUserState state
    match vstate.ICFGs with
    | Some icfg :: _ -> getMinDistance icfg.Edges bID (Set.init target)
    | _ -> maxDistance

  let forGc info task =
    let state, _, bID, _ = task
    let fID = State.getCurFname state
    let vstate = State.getUserState state
    let noGcNodes = (Info.getGcNodes info fID) - (List.head vstate.GcNodes)
    if Set.contains bID noGcNodes then maxDistance
    else minDistance

  let forNotGc info (state, _, bID, _) =
    let fID = State.getCurFname state
    let gcNodes = Info.getGcNodes info fID
    if Set.contains bID gcNodes then maxDistance
    else minDistance

  let forLoop (state, _, bID, iID) =
    if iID = 0 then
      let cbID = State.getCurBB state
      if cbID = bID then maxDistance
      else
        //let n = (State.getPathCnt state bID) + 1
        //Math.Log (float n, 2.) |> Math.Round |> int
        State.getPathCnt state bID
    else 0

  let debugSchedule state tasks =
    let iter (state, _, bID, iID) =
      let fname = State.getCurFname state
      let vstate = State.getUserState state
      List.head vstate.GcLevels
      |> Logger.info "%s %d %d %A %A" fname bID iID vstate.Type

    //Logger.info "debugSchedule.."
    //List.iter iter tasks
    //State.debug state
    tasks

  let schedule info state tasks =
    let vstate = State.getUserState state
    let tasks =
      match vstate.Type with
      //| GcCalled -> List.sortBy (forNotGc info) tasks
      //| GcStart -> List.sortBy (forGc info) tasks
      | _ -> tasks
    let tasks = List.sortBy forLoop tasks
    debugSchedule state tasks

  let finder (ret, (state, _, bID, _)) =
    let vstate = State.getUserState state
    AddTaskCode.isUnSAT ret && State.inStartFunc state
    && fst vstate.GcInstr = bID

  let reschedule mgr tasks =
    match List.tryFind finder tasks with
    | Some (_, task) ->
      let first, last = Manager.findSubSatTasks task mgr.Tasks
      Manager.setTasks mgr (first @ last)
    | _ -> mgr

  let verifyOne info state timeout (vstate, result) =
    async {
      let target = Result.getFuncID result
      let state = State.prepare state target vstate
      let timer = new Diagnostics.Stopwatch ()
      timer.Start ()
      Result.show info "Start SymExec" result timer.ElapsedMilliseconds
      try
        Manager.init state timeout
        |> Manager.setScheduleTasks (schedule info)
        |> Manager.setReschedule reschedule
        |> Executor.start |> ignore
        return Some false, result, timer.ElapsedMilliseconds
      with
        | EndException ->
          Result.show info "Reachable" result timer.ElapsedMilliseconds
          return Some true, result, timer.ElapsedMilliseconds
        | TimeEndException ->
          Result.show info "Timeout" result timer.ElapsedMilliseconds
          return None, result, timer.ElapsedMilliseconds
        //| e -> return None, result, -1L
    }

  let verify useOpt conf info results =
    Logger.info "Start verify, useOpt %A" useOpt
    let info = Array.map Result.getFuncID results |> Set.ofArray
               |> Info.calcGcLoops info
    let prog = Info.getProg info |> handleFlags
    let timeout = conf.VerifyTimeout
    let cache =
      if useOpt then Reducer.mkOptCache () else Reducer.mkNonOptCache ()
    let state =
      State.init prog (VState.empty cache)
      |> State.setIsReachable isReachable
      |> State.setGetSymFunc (getSymFunc info (mkSymMap info))
      |> State.setCallCb (callCb info)
      |> State.setReturnCb returnCb
      |> State.setStmtCb stmtCb
    let vstates =
      Array.map (prepare useOpt conf info prog cache) results
      |> Array.choose (chooseTarget info)

    Logger.info "Start symbolic execution, useOpt %A" useOpt
    Array.map (verifyOne info state timeout) vstates
    |> Utils.doParallel2 conf.Cores
    |> Array.iter (checkResult info)
