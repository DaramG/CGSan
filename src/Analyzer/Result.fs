namespace Analyzer

open LLIR
open Common

type DefLoc =
  | Arg of int
  | Instr of ID * InstPos

type UseType =
  | FuncArg of ID
  | MemLoad
  | MemStoreAddr
  | MemStoreValue
  | Return

type PtrInfo = {
  Type: ID
  DefLoc: DefLoc
  FreeLog: (ID * InstPos) list
}

type Result = {
  FuncID: ID
  PtrType: ID
  Type: UseType
  DefLoc: DefLoc
  Gc: (ID * InstPos) list
  Use: InstPos
  FuncPath: BlockID list
  Expr: Expr
}

exception UseAfterGC of Result

module DefLoc =
  let demangle fID = LLVM.Reader.demangle fID |> sprintf "%s [%s]" fID

  let toStr = function
    | Arg idx -> sprintf "Arg[%d]" idx
    | Instr (fID, pos) ->
      demangle fID |> sprintf "%s, Func: %s" (InstPos.toStr pos)

module UseType =
  let toStr = function
    | FuncArg fID -> DefLoc.demangle fID |> sprintf "Used as argment of %s"
    | MemLoad -> "MemLoad"
    | MemStoreAddr -> "MemStoreAddr"
    | MemStoreValue -> "MemStoreValue"
    | Return -> "Return"

module PtrInfo =
  let init ty loc = {
    Type = ty
    DefLoc = DefLoc.Instr loc
    FreeLog = []
  }

  let initArg ty idx = {
    Type = ty
    DefLoc = DefLoc.Arg idx
    FreeLog = []
  }

  let isFreed ptr = ptr.FreeLog = [] |> not

  let free freeLog _ ptr = { ptr with FreeLog = freeLog :: ptr.FreeLog }

module Result =
  type SB = System.Text.StringBuilder

  let addStr (sb: SB) (str: string) = sb.Append (str) |> ignore

  let init ty func ptrTy def gc useLoc expr path = {
    FuncID = func
    PtrType = ptrTy
    Type = ty
    DefLoc = def
    Gc = gc
    Use = useLoc
    FuncPath = path
    Expr = expr
  }

  let private printGC sb info (id, pos) =
    (*
    let rec loop lv doneSet fID =
      if (Set.contains fID doneSet |> not) && Info.isGC info fID then
        let doneSet = Set.add fID doneSet
        DefLoc.demangle fID |> sprintf "%s| %s\n" (String.replicate lv " ")
        |> addStr sb
        if Info.isBasicGC info fID then doneSet
        else Info.getGcCalls info fID |> Set.fold (loop (lv + 1)) doneSet
      else doneSet
    *)
    DefLoc.demangle id |> sprintf "GC in %s, %s\n" (InstPos.toStr pos)
    |> addStr sb
    //loop 1 Set.empty id |> ignore

  let print info result =
    let sb = new SB ()
    DefLoc.demangle result.FuncID |> sprintf "UseAfterGC in %s\n"
    |> addStr sb
    sprintf "Def in %s\n" (DefLoc.toStr result.DefLoc) |> addStr sb
    sprintf "Ptr Type: %s\n" result.PtrType |> addStr sb
    UseType.toStr result.Type
    |> sprintf "Use in %s, %s, %s\n" (InstPos.toStr result.Use)
    <| Pp.printExpr result.Expr |> addStr sb
    Array.revList result.Gc |> Array.iter (printGC sb info)
    sb.ToString ()

  let getFuncID result = result.FuncID
  let getPath result = result.FuncPath
  let getUseInstr result = result.Use
  let getGcInstr result = List.head result.Gc
  let getDefNode result =
    match result.DefLoc with
    | Arg _ -> 0
    | Instr (_, (n, _)) -> n

  let show info str result time =
    print info result
    |> Logger.info "========== %s ==========\nTime: %A\n%s" str time
