/-
  LeanVM.Guest.Backend.Guest.Cpl.Whole

  Whole-program completeness at the guest: the compiled guest runs from `main`'s entry to the
  final registers on the honest memory of every run of its core IR, within the budget.
-/

module

public import LeanVM.Guest.Backend.Complete.ProgramDone
public import LeanVM.Guest.Backend.Guest.Cpl.Eval.All
public import LeanVM.Guest.Backend.Guest.Cpl.Placed

/-!
# Whole-program completeness at the guest

`guestConds`: every function of the guest passes the per-function conditions of
`ProgramCompleteStmt`, from the per-function test `cplOkAll` (its scoped, no-self-call and
temporaries-apart components and its static test's loop component). Then
`guest_run_complete` is `program_complete` at `W0`, the guest compiled by the back end
(`guest_compiles`), counting no arms separately.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A function of a compiled program has one placement. -/
theorem placedAs_unique {κ : ℕ} {W : World κ} (hW : W.Compiled) {tf : TracedFn} {pf pf' : Placed}
    (h : Complete.World.PlacedAs W tf pf) (h' : Complete.World.PlacedAs W tf pf') : pf = pf' := by
  obtain ⟨hn, hnd⟩ := Complete.placed_names hW
  exact List.inj_on_of_nodup_map (hn ▸ hnd) h.1 h'.1 (h.2.trans h'.2.symm)

/-- **Every function of the guest passes the per-function conditions.** -/
theorem guestConds : ∀ tf ∈ W0.p, Complete.FnConds W0 tf := by
  intro tf htf
  rw [W0_p] at htf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htf
  have hi' : i < 1601 := GuestPiece.guestTraced_length ▸ hi
  obtain ⟨hat, hpa, -⟩ := guest_placed hi
  have hF := cplOkWith_spec (cplOkWith_of hat (CplEval.cplOkAll i hi'))
  rw [← List.getD_eq_getElem _ default hi]
  exact ⟨hF.isScoped, hF.noSelf, hF.sfacts.loop,
    fun pf hp => placedAs_unique W0_compiled hpa hp ▸ hF.apart⟩

/-- **The guest is complete through the back end**: on the honest memory of every run of its
core IR at the back end's frame sizes and cells, the compiled guest runs from `main`'s entry at
frame `g^0` to the final registers, within each running instance's placed path maxima summed
over the call tree. -/
theorem guest_run_complete : ∀ (hdr : E × E) (rd : Reader) (T : Tree), T.name = "main" →
    HonestAt W0.core W0.fsB W0.hdrB W0.cellsB hdr T W0.cellB rd [] [] →
    ∃ c : Opcode → ℕ, RunC W0.prog (W0.honestB hdr T) ⟨addressOfIndex (W0.ent "main"), 1⟩
      (Registers.final W0.prog) c ∧ ∀ op, c op ≤ W0.progCost (fun _ => false) T op :=
  Complete.program_complete W0 W0_compiled guestConds (fun _ => false)

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_run_complete
