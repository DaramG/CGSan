namespace Analyzer

open System

open LLIR
open LLIR.Core
open Common
open SymExecutor
open PathOptimizer

module Analyzer =

  let private useAfterGC state ty id expr =
    let useLoc = State.getLastBB state, State.getInstrID state
    let gcstate = State.getUserState state
    let ptr = GcState.getPtr id gcstate
    let fname = GcState.getID gcstate
    State.getPaths state |> List.head |> List.rev
    |> Result.init ty fname id ptr.DefLoc ptr.FreeLog useLoc expr
    |> UseAfterGC |> raise

  let private checkExpr ty state expr =
    let ustate = State.getUserState state
    match expr with
    | Addr (SymVar (id, _), _, _)
    | SymVar (id, _) when GcState.isFreed id ustate ->
      useAfterGC state ty id expr
    | _ -> state

  let private getSymFunc info _ fID =
    let ty = FuncArg fID
    let checkMems state args =
      let checkOne arg =
        let (state, arg), succ =
          try State.rawLoad Builder.ptrSizeInt state arg, true
          with | _ -> (state, arg), false
        if succ then checkExpr ty state arg |> ignore
      if Array.length args > 0 && Info.isMethod info fID then
        Array.pop args |> fst |> checkOne

    let checkArgs state args = Array.iter (checkExpr ty state >> ignore) args

    let evalIfGC pos state =
      if Info.isGC info fID || Info.isBasicGC info fID then
        let gcstate = State.getUserState state
        if GcState.isGC gcstate (State.getCurPos state) then
          State.setUserState (GcState.freePtrs gcstate fID pos) state
        else state
      else state

    let evalOuts pos args state =
      let addMemPtr (state, gcstate) arg md =
        match Info.getHeapPtrMDName info md with
        | Some name ->
          let gcstate, value = GcState.addPtr gcstate name fID pos
          State.rawStore state arg value, gcstate
        | _ -> state, gcstate
      let gcstate = State.getUserState state
      let argTy = Info.getFuncArgs info fID
      if Array.length args = Array.length argTy then
        let args, argTy =
          if Array.length args > 0 && Info.isMethod info fID then
            Array.pop args |> snd, Array.pop argTy |> snd
          else args, argTy
        let state, gcstate = Array.fold2 addMemPtr (state, gcstate) args argTy
        State.setUserState gcstate state
      else state

    let evalRet pos retID retSize args state =
      let retMD = Program.getFunc info.Prog fID |> Function.getRetMD
      match Option.map (Info.getHeapMDName info) retMD with
      | Some (Some name) ->
        let gcstate, ret =
          GcState.addPtr (State.getUserState state) name fID pos
        let state = State.setUserState gcstate state
        State.addVar retID state ret
      | _ -> Builder.mkUnIntCall fID args retSize |> State.addVar retID state

    let symFunc state iID retID args retSize =
      let pos = State.getCurBB state, iID
      checkMems state args
      checkArgs state args
      evalIfGC pos state
      |> evalOuts pos args
      |> evalRet pos retID retSize args
      |> Some

    Some symFunc

  let private loadCb state addr size value = checkExpr MemLoad state addr

  let private isLocal = function
    | LocalAddr _
    | Addr (LocalAddr _, _, _) -> true
    | _ -> false

  let private storeCb state addr value =
    checkExpr MemStoreAddr state addr |> ignore
    checkExpr MemStoreValue state value

  let private returnCb state = function
    | Some expr -> checkExpr (UseType.Return) state expr
    | _ -> state

  let private isReachable state nID iID =
    let cID = State.getCurBB state
    if cID = -1 then Some state
    elif GcState.isReachable (State.getUserState state) cID nID
         && State.checkPathCnt 2 state nID iID then Some state
    else None

  let private initArgsFold info (state, gcstate, ret) md (idx, size) =
    match Info.getHeapPtrMDName info md with
    | Some name ->
      let arg = Builder.mkArg idx size
      let gcstate, value = GcState.addArgPtr gcstate (name + "*") idx
      State.rawStore state arg value, gcstate, arg :: ret
    | _ ->
      match Info.getHeapMDName info md with
      | Some name ->
        let gcstate, value = GcState.addArgPtr gcstate name idx
        state, gcstate, value :: ret
      | _ -> state, gcstate, Builder.mkArg idx size :: ret

  let private initArgs (info: Info) state fID =
    let func = Program.getFunc info.Prog fID
    let gcstate = State.getUserState state
    let argsMD = Info.getFuncArgs info fID
    let args = Function.getArgs func
    let state, gcstate, args =
      let l1 = Array.length argsMD
      let l2 = Array.length args
      if l1 > 0 && l1 >= l2 then
        let argsMD = Array.sub argsMD 0 l2
        Array.fold2 (initArgsFold info) (state, gcstate, []) argsMD args
      else
        state, gcstate,
        Array.map (fun (i, s) -> Builder.mkArg i s) args |> Array.toList
    State.setUserState gcstate state, Array.revList args

  let private checkOne info timeout state (fID, gcPos) =
    let edges = Info.getCandEdges info fID gcPos
    let state = State.setUserState (GcState.init fID gcPos edges) state
    let state, args = initArgs info state fID
    async {
      try
        let state = State.initFunc state fID State.endAddr State.endAddr args
        Manager.init state timeout |> Executor.start |> ignore
        return Some None, fID
      with
        | UseAfterGC result -> return Some (Some result), fID
        | TimeEndException -> return None, fID
    }

  let private checkResults info rets =
    let chooseBug = function
      | Some (Some result), _ -> Some result
      | _ -> None

    let chooseTimeout = function
      | None, fID -> Some fID
      | _ -> None

    let timeouts = Array.choose chooseTimeout rets
    Logger.info "Timeout: %d / %d" (Array.length timeouts) (Array.length rets)
    Array.iter (printfn "%s") timeouts

    let ret = Array.choose chooseBug rets
    Array.iter (Result.print info >> printfn "%s") ret
    ret

  let check conf prog =
    Logger.info "Start GcCheck"
    let timeout = conf.CheckTimeout
    let prog = Program.stripUnreachable prog
    let info = Info.init prog conf
    Logger.info "Start Execute"
    let state =
      State.init prog GcState.empty
      |> State.setUseSAT false
      |> State.setIsReachable isReachable
      |> State.setGetSymFunc (getSymFunc info)
      |> State.setLoadCb loadCb
      |> State.setStoreCb storeCb
      |> State.setReturnCb returnCb
    let tasks = Info.getCands conf info |> Array.map (checkOne info timeout state)
    Logger.info "# of Cands: %d" (Array.length tasks)
    info, Utils.doParallel2 conf.Cores tasks |> checkResults info

  let analyze conf prog =
    let info, cands = check conf prog
    //Verifier.verify false conf info cands
    Verifier.verify true conf info cands

  let test conf prog = Info.init prog conf |> Info.debug
