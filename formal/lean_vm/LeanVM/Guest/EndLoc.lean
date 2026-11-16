/-
  LeanVM.Guest.EndLoc

  B2, located: a valid execution's memory holds `main`'s body at its frame, its calls located.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.Located.Basic

/-!
# `main` at its frame

B2 is the back end's correctness at the guest (`Backend.guest_main_body`, `Backend.contracts`),
given that the back end compiles the guest to the statement's bytecode (`guest_compiles`):

* `globSpec`: every function's contract on the guest's world `Located.guestW L` (entry
  `World.ent`, precondition `World.Pre`, postcondition `World.Post`), on the run from `(g^0, 1)`,
  for runs of any length;
* `mainBodyL_of_safe`, `mainBodyL_of`: on a halting run from `(g^0, 1)`, `main`'s body under the
  valuation by places at `fp = 1` (`Located.mainVal`), each call located at a frame the run
  entered the callee at, its precondition holding there and its argument and return words the
  call's (`Located.RLg`, the back end's `World.C`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **Every function's contract** on the guest's world, on the run from `(g^0, 1)`, for runs of any
length (`Backend.contracts`, with every function's obligations `Backend.Obl.guest_obligations`). -/
theorem globSpec {κ : ℕ} {L : MemoryImage κ} (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    (g : String) :
    FunSpecReached guestProgram L ((Located.guestW L).ent g) ((Located.guestW L).Pre g)
      ((Located.guestW L).Post g) := by
  have hW := Backend.guestWorld_compiled (L := L) (U := Backend.Obl.guestU L.read)
    Backend.guest_compiles
  have h := Backend.contracts hW (lt_of_le_of_lt h32 Backend.maxLogMem_lt)
    (Backend.Obl.guest_obligations hW Backend.guestTraced_core ⟨h16, h32⟩ rfl) g
  rw [Backend.guestWorld_prog Backend.guest_compiles] at h
  exact h

/-- **B2 at `main`, located, for a halting run from `(g^0, 1)`** (`Backend.guest_main_body`). -/
theorem mainBodyL_of_safe {κ : ℕ} {L : MemoryImage κ} (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem)
    {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex 0, 1⟩) :
    Stmt.HoldsList (Located.RLg L) L.read (Located.mainVal L) Data.core0.body False
      (fun rs ↦ rs = []) :=
  Backend.guest_main_body Backend.guest_compiles κ L h16 h32 k hs

/-- **B2 at `main`, located, for a valid execution**: `main`'s body under its frame's valuation,
its calls located, and the public input's cells at `g^0`, `g^1`. -/
theorem mainBodyL_of {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    Stmt.HoldsList (Located.RLg t.memory) t.memory.read (Located.mainVal t.memory) Data.core0.body
      False (fun rs ↦ rs = []) ∧
    LoadHolds t.memory.read 1 0 (digestHalves (publicInputDigest input)).1 ∧
    LoadHolds t.memory.read 1 1 (digestHalves (publicInputDigest input)).2 :=
  ⟨mainBodyL_of_safe hv.1.1 hv.1.2.1 (safe_of_validExecution hv), pub_loads hv⟩

end
end LeanVM.Guest.End
