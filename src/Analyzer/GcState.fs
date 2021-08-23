namespace Analyzer

open LLIR

type GcState = {
  ID: ID
  Ptrs: Map<ID, PtrInfo>
  GcPos: InstPos
  Edges: Set<BlockID * BlockID>
  DefAndGC: bool
}

module GcState =
  let empty = {
    ID = ""
    Ptrs = Map.empty
    GcPos = -1, -1
    Edges = Set.empty
    DefAndGC = false
  }

  let init fID gcPos edges = {
    ID = fID
    Ptrs = Map.empty
    GcPos = gcPos
    Edges = edges
    DefAndGC = false
  }

  let getID state = state.ID

  let mkSymName state ty bID iID =
    sprintf "ptr_%d_%d_%d_%s" bID iID (Map.count state.Ptrs) ty

  let addPtr state ty fID pos =
    let bID, iID = pos
    let name = mkSymName state ty bID iID
    let ptr = PtrInfo.init ty (fID, pos)
    { state with Ptrs = Map.add name ptr state.Ptrs },
    Builder.mkSymVar name Builder.ptrSizeInt

  let addArgPtr state ty idx =
    let name = mkSymName state ty -1 idx
    let ptr = PtrInfo.initArg ty idx
    { state with Ptrs = Map.add name ptr state.Ptrs },
    Builder.mkSymVar name Builder.ptrSizeInt

  let freePtrs state fID pos =
    let freeLog = fID, pos
    { state with Ptrs = Map.map (PtrInfo.free freeLog) state.Ptrs
                 DefAndGC = Map.count state.Ptrs > 0 }

  let isReachable state cID nID =
    state.DefAndGC || Set.contains (cID, nID) state.Edges

  let isFreed id state =
    match Map.tryFind id state.Ptrs with
    | Some info -> PtrInfo.isFreed info
    | _ -> false

  let getPtr id state = Map.find id state.Ptrs

  let isGC state pos = state.GcPos = pos
