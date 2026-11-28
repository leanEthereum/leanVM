/-
  LeanVM.Guest.CoreMode.Fam.NzOnly

  A certificate's residuals, listed parameters' nonzero values: the check each routed certificate
  passes at its compiled index.
-/

module

public import LeanVM.Guest.CoreMode.Fam.SelDefs
public import LeanVM.Guest.Mode.InvCert
public import LeanVM.Guest.Glob

/-!
# Residuals: listed parameters' nonzero values

The bus era's `Assemble.{nzOnlyB, NzOnly}`. A residual a core-route certificate may carry at
function `j`: a listed parameter's nonzero value (`Res.nzB`), or a name. `NzOnly nzs K`: `K` has no
residual, or each is one of these at its function's index (`nzOnly_of`, decided per routed function
in `core_cert%`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- A residual a core-route certificate may carry at function `j`: a listed parameter's nonzero
value (`nzB`), or a name. -/
noncomputable def nzOnlyB (nzs : List (String × V)) (j : ℕ) : Mode.Res → Bool
  | .nz o => nzB nzs j o
  | .name _ => true
  | _ => false

/-- **A certificate's residuals are listed parameters' nonzero values**: it has none, or each is,
at its function's index `j`. -/
def NzOnly (nzs : List (String × V)) (K : Mode.Cert) : Prop :=
  K.F.res = .nil ∨ ∃ j, j < nFns ∧ (fnOf j).entryPc = K.F.entry ∧ allV (fun l ↦ l.all (nzOnlyB nzs j)) K.F.res = true

/-- `NzOnly`'s check at function `j`: no residual, or each a listed parameter's nonzero value at `j`. -/
noncomputable def nzOnlyChk (nzs : List (String × V)) (K : Mode.Cert) (j : ℕ) : Bool :=
  match K.F.res with
  | .nil => true
  | .node _ _ _ => decide (j < nFns) && (fnOf j).entryPc == K.F.entry &&
      allV (fun l ↦ l.all (nzOnlyB nzs j)) K.F.res

theorem nzOnly_of {nzs : List (String × V)} {K : Mode.Cert} {j : ℕ} (h : nzOnlyChk nzs K j = true) :
    NzOnly nzs K := by
  unfold nzOnlyChk at h
  split at h
  · exact .inl ‹_›
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact .inr ⟨j, h.1.1, h.1.2, h.2⟩

end

end LeanVM.Guest.Res
