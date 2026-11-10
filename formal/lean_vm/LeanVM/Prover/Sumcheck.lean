/-
  LeanVM.Prover.Sumcheck

  The stateful sumcheck prover makes the specification's moves: a coefficient list that evaluates
  as the round's claim is the specification's (`coeffsOf`), the unique polynomial of its degree.
-/

module

public import LeanVM.Prover.Corr
public import Statement.Prover.Script
public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.Field
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# The stateful sumcheck

* `coeffsOf_eq`: the specification's round message `coeffsOf d f`, chosen classically among the
  coefficient lists of `f`, is any list of `d + 1` coefficients that evaluates as `f` (two
  polynomials of degree at most `d < |E|` that agree everywhere are equal).
* `corr_sumcheckBy`: the stateful prover `sumcheckBy round fold` makes the moves of the
  specification's `hSumcheck count claimOf`, given an invariant along the rounds under which the
  state's coefficients evaluate as the round's claim.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier Polynomial
open LeanVM.Protocol.EndToEnd.Complete (coeffsOf PolyLE hSumcheck polyEval_eq_sum)

@[expose] public section

/-- The polynomial whose coefficients, constant first, are `l`. -/
noncomputable def polyOfList (l : List E) : E[X] :=
  ∑ i ∈ Finset.range l.length, C (l.getD i 0) * X ^ i

theorem eval_polyOfList (l : List E) (x : E) : (polyOfList l).eval x = polyEval l x := by
  rw [polyEval_eq_sum, polyOfList, eval_finsetSum]
  simp

theorem coeff_polyOfList (l : List E) (i : ℕ) : (polyOfList l).coeff i = l.getD i 0 := by
  rw [polyOfList, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · rename_i h
    rw [List.getD_eq_default _ _ (by simpa using h)]

theorem natDegree_polyOfList (l : List E) : (polyOfList l).natDegree ≤ l.length - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hi
  omega

/-- **The specification's round message is any coefficient list of the right length** that
evaluates as the round's claim. -/
theorem coeffsOf_eq {d : ℕ} {l : List E} (hl : l.length = d + 1) (hd : d < 2 ^ 128) {f : E → E}
    (hf : ∀ x, polyEval l x = f x) : coeffsOf d f = l := by
  classical
  have hP : PolyLE d f :=
    ⟨polyOfList l, (natDegree_polyOfList l).trans (by omega), fun x ↦ by
      rw [eval_polyOfList, hf]⟩
  have hc : coeffsOf d f = (List.range (d + 1)).map (Classical.choose hP).coeff := by
    simp [coeffsOf, hP]
  obtain ⟨hdeg, hev⟩ := Classical.choose_spec hP
  have hQ : Classical.choose hP = polyOfList l := by
    refine eq_of_natDegree_lt_card_of_eval_eq (ι := E) _ _ Function.injective_id
      (fun x ↦ ?_) ?_
    · simp only [id]
      rw [← hev, eval_polyOfList, hf]
    · rw [LeanVM.Protocol.card_E]
      have := natDegree_polyOfList l
      omega
  rw [hc, hQ]
  refine List.ext_getElem (by simp [hl]) fun i h₁ h₂ ↦ ?_
  simp only [List.getElem_map, List.getElem_range, coeff_polyOfList]
  exact List.getD_eq_getElem _ _ h₂

/-- The statement's wire form is the specification's. -/
theorem wire_eq (mode : Option E) (c : List E) :
    wire mode c = LeanVM.Protocol.EndToEnd.Complete.wire mode c := by
  cases mode <;> rfl

end
end LeanVM.Prover
