/-
  LeanVM.Guest.B1.Tables.Vt.Forms

  The guest's baked coordinate terms (`COORD_TERM_*`, `TERM_*`) are the specification's flush
  forms: every table block's coordinate, evaluated at any table row, is the value of its terms.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Base
public import LeanVM.Guest.B1.Tables.CoordPadding
public import LeanVM.Protocol.EndToEnd.Complete.Flushes

/-!
# The forms' terms (G:2620-2647)

`verify_tables` evaluates each table block's coordinate as the sum of its baked terms over the
table's column evaluations (`vtCoordTerms`). The specification's flushes are the symbolic tables of
`Protocol.EndToEnd.Complete.Flushes` (`refSide_eq`); their coefficients evaluate in `K`, so the
canonical forms of both sides are compared by kernel evaluation (`vtForms_check`). `vt_coord_eval`:
the specification's coordinate, evaluated at any assignment of the columns in `E`, is the value of
the guest's terms.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (Terms termsEval canon FormC Coef insertTerm monoSort
  monoSort_perm termsEval_cons flushesC refSideC refSide refSide_eq evaluate_eq_termsEval)

@[expose] public section

/-- Terms over `K`, lifted to `E`. -/
def liftT (l : Terms K) : Terms E := l.map fun u ↦ (u.1, ofK u.2)

theorem termsEval_liftT_insertTerm (r : ℕ → E) (t : List ℕ × K) :
    ∀ l : Terms K, termsEval r (liftT (insertTerm t l)) =
      ofK t.2 * (t.1.map r).prod + termsEval r (liftT l)
  | [] => by simp [insertTerm, liftT, termsEval]
  | u :: us => by
    unfold insertTerm
    split_ifs with h1 h2
    · simp only [liftT, List.map_cons, termsEval_cons, h1, ofK_add]; ring
    · simp [liftT, termsEval]
    · simp only [liftT, List.map_cons, termsEval_cons] at *
      rw [show termsEval r (List.map (fun u ↦ (u.1, ofK u.2)) (insertTerm t us)) =
        termsEval r (liftT (insertTerm t us)) from rfl, termsEval_liftT_insertTerm r t us]
      simp only [liftT]; ring

/-- **Evaluation in `E` is invariant under the canonical form.** -/
theorem termsEval_liftT_canon (r : ℕ → E) (l : Terms K) :
    termsEval r (liftT (canon l)) = termsEval r (liftT l) := by
  have hf : ∀ m : Terms K, termsEval r (liftT (m.filter fun t ↦ decide (t.2 ≠ 0))) =
      termsEval r (liftT m) := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih =>
      rw [List.filter_cons]
      split
      · simp only [liftT, List.map_cons, termsEval_cons] at ih ⊢; rw [ih]
      · rename_i h
        have h0 : t.2 = 0 := by simpa using h
        simp only [liftT, List.map_cons, termsEval_cons] at ih ⊢
        rw [ih, h0, ofK_zero, zero_mul, zero_add]
  have hfold : ∀ m : Terms K, termsEval r (liftT (m.foldr insertTerm [])) = termsEval r (liftT m) := by
    intro m
    induction m with
    | nil => rfl
    | cons t m ih =>
      rw [List.foldr_cons, termsEval_liftT_insertTerm, ih]
      simp [liftT, termsEval]
  rw [canon, hf, hfold]
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [liftT, List.map_cons, termsEval_cons] at ih ⊢
    rw [ih]
    congr 2
    exact ((monoSort_perm t.1).map r).prod_eq

/-- A symbolic form's value at any assignment in `E`. -/
theorem toForm_evaluate (f : FormC) (r : ℕ → E) :
    f.toForm.evaluate r = termsEval r (liftT f.termsK) := by
  have ht : f.toForm.terms = liftT f.termsK := by
    simp [FormC.toForm, FormC.termsK, liftT, Coef.ev_eq]
  rw [evaluate_eq_termsEval, ht]

end
end LeanVM.Guest.B1.Tables
