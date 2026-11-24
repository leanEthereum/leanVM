/-
  LeanVM.Guest.Bridge.JumpCellsDeployed

  The jump cells on the deployed guest's reference run, from every function's data check, and the trace of the tree track along the whole run.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsOf
public import LeanVM.Guest.Bridge.JumpCells.All
public import LeanVM.Guest.Bridge.StepRule
public import LeanVM.Guest.Bridge.TrackHonest
public import LeanVM.Prover.ExecuteComplete

/-!
# The jump cells on the deployed guest

`jumpCells_deployed`: `jumpCells_of` with every function's data check (`JumpCells.jcData_all`), the chained `match`es' arms (`ChainArm`) the one premise left.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (Budget work hdrOf bytecode mainEntry)
open LeanVM.Guest.Budget (MainCompleteP)

public section

variable {hdr : E × E} {rd rd0 : Reader} {T : Tree} {κ : ℕ} {L : MemoryImage κ} {M : ℕ → E}

/-- **The jump cells of the deployed guest**, the chained `match`es' arms given. -/
theorem jumpCells_deployed (hT : T.name = "main")
    (hH : HonestAt coreProgram B2C.fs B2C.H B2C.C hdr T B2C.cert rd [] [])
    (hL : Covers coreProgram B2C.fs B2C.H B2C.C hdr T L)
    (hCh : ChainArm rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M alignA) {pc fp : ℕ} {done : List Pop}
    {e : Ent} {st : List Ent}
    (h : RefOk coreProgram rd0 (honestInsts coreProgram B2C.fs B2C.H hdr T) T M (entOf alignA) (alOf alignA) pc fp
      (done, e :: st)) : JumpCells L alignA e pc :=
  jumpCells_of hT hH hL (fun j h1 h2 ↦ JumpCells.jcData_all j h1 (by have : nFns = fn_count% := rfl; omega)) hCh h

end

end LeanVM.Guest.Bridge
