/-
  LeanVM.Guest.CoreMode.Fam.TermOk

  A certificate's termination facts: none, or a loop helper's `[2] < end`.
-/

module

public import LeanVM.Guest.CoreMode.Fam.LoopDefs
public import LeanVM.Guest.Mode.InvCert
public import LeanVM.Guest.Glob

/-!
# A certificate's termination facts

`TermOk K`: a certificate has no termination fact, or is compiled function `j`'s, a loop helper,
with the one fact `[2] < end` of its shape's end (`endIdx`: its second argument, cell `3`, or a
constant). `termOkB` decides it at a given `j`; `scripts/core-mode/certs.py` passes each routed
function's index (`core_cert%`). `Fam/ResTA.lean` turns it into `TermNodeA`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest
open LeanVM.Guest.Res (endOfFn)

@[expose] public section

/-- A loop helper's end as an exponent: its second argument's (cell `3`), or the constant. -/
def endIdx : Option ℕ → Mode.Idx
  | none => .ex (.fr 3) 0
  | some N => .num N

/-- **A certificate's termination facts**: none, or it is function `j`'s, a loop helper, with the
one fact `[2] < end` of its shape's end. -/
def TermOk (K : Mode.Cert) : Prop :=
  K.F.sig.term = [] ∨ ∃ j, 1 ≤ j ∧ j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ (coreOf j).loop = true ∧
    K.F.sig.term = [(.ex (.fr 2) 0, endIdx ((endOfFn (coreOf j)).getD none))]

/-- `TermOk` at function `j`, decided. -/
noncomputable def termOkB (K : Mode.Cert) (j : ℕ) : Bool :=
  K.F.sig.term.isEmpty || (decide (1 ≤ j) && decide (j < nFns) && (fnOf j).entryPc == K.F.entry &&
    (coreOf j).loop && decide (K.F.sig.term = [(.ex (.fr 2) 0, endIdx ((endOfFn (coreOf j)).getD none))]))

theorem termOk_of {K : Mode.Cert} {j : ℕ} (h : termOkB K j = true) : TermOk K := by
  simp only [termOkB, Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, h1, h2, h3, h4, h5⟩

end

end LeanVM.Guest.EndExec
