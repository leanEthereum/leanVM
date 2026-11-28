/-
  LeanVM.Prover.Complete.WhirOpening

  Completeness of the stacked WHIR opening: the honest levels win `verifyStackedOpening` on claims
  that hold of the committed stack.
-/

module

public import LeanVM.Protocol.Whir.Complete.Levels
public import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Prover.Ntt

/-!
# The stacked opening wins

`follows_stackedOpening` (the bus era's `openingComplete`, `formal-bus-archive`'s
`Whir/Complete/OpeningProof.lean`, with the batching challenge drawn by ring switching): for an
admissible `(μ, R)` and at most `maxStackedClaims` claims that hold of the stack `q` with
multilinear weights, the statement's levels (`levelsA`) on the stack table and any weight table
equal to the claims' batched basis table follow `verifyStackedOpening` from the stack's
commitment. The invariant at level `0` is the archive's: the batched value is the pairing of the
two tables (`dot_values_eq_dot`), the batched basis at the rotated point is the extension of the
weight table (`multilinearEval_basisTable`), and the stack's rows are the stack table's lanes
(`readRow_stackWord`).
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Prover LeanVM.Prover.Enc Finset
open LeanVM.Protocol.Tables

@[expose] public section

/-- The stack's commitment, as a `Committed`. -/
def stackCommitted (μ R : ℕ) (q : Column μ) : Committed :=
  ⟨μ - laneBits + R, 2 ^ laneBits, stackWordFast μ R q.values.toArray⟩

/-- **The stacked opening wins**, from the stack's commitment. -/
theorem follows_stackedOpening {μ R : ℕ} (hadm : Whir.Admissible μ R) (q : Column μ)
    (claims : List StackClaim) (batching : E) (hlen : claims.length ≤ maxStackedClaims)
    (hholds : ∀ c ∈ claims, StackClaim.Holds μ c q) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1)
    (w : Array E) (hw : w.toList = basisTable μ (powers batching claims.length) claims) :
    Follows (fun _ _ _ ↦ True)
      (match Whir.ladder μ R with
        | none => (return () : Script Unit)
        | some config => levelsA μ config (stackTableA μ q.values.toArray) w)
      (verifyStackedOpening μ R claims batching) [stackCommitted μ R q] := by
  obtain ⟨q₀, rest, hc, -⟩ := exists_ladder hadm
  have hμ6 : laneBits ≤ μ := le_trans (by decide) hadm.1
  have hμ30 : μ ≤ 30 := hadm.2.1
  rw [verifyStackedOpening, VerifierProgram.bind_eq, require_bind_of hlen]
  simp only [verifyWhir, hc, Verifier.liftOption, VerifierProgram.bind_eq, VerifierProgram.ret_bind,
    List.head?_cons, Option.map_some, Option.getD_some]
  set scales := powers batching claims.length
  have hst : (stackTableA μ q.values.toArray).size = (2 ^ (μ - laneBits) + 0) * 2 ^ laneBits := by
    simp [stackTableA, ← pow_add, Nat.sub_add_cancel hμ6]
  have hbs : w.size = 2 ^ (μ - laneBits) * 2 ^ laneBits := by
    rw [← Array.length_toList, hw]
    simp [basisTable, ← pow_add, Nat.sub_add_cancel hμ6]
  have hstl := toList_stackTableA q
  refine follows_levelsA μ laneBits _ (⟨laneBits, R, q₀⟩ :: rest) 0 μ _ _ _ _
    (stackWordFast μ R q.values.toArray) (2 ^ laneBits) (ladderOK_of_ladder hadm hc) rfl ?_
  intro level hl
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
  subst hl
  refine ⟨rfl, hbs, hst, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 ^ (μ - laneBits) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 30 + 6 ≤ 2 ^ 61 := by norm_num
    simp only [laneBits] at *
    omega
  · rw [dot_values_eq_dot hμ6 q scales claims hholds, ← hw, ← hstl,
      dot_eq_sum _ _ (by rw [Array.length_toList, Array.length_toList, hbs, hst]; simp)]
    simp only [Array.length_toList, Enc.array_getD_toList]
  · simp only [List.length_nil]; omega
  · intro x hx
    simp only [runW, List.nil_append, List.foldl_nil]
    simp only at hx
    rw [hw, multilinearEval_basisTable hμ6 scales claims hml x (by rw [hx]; omega)]
    rfl
  · intro p hp
    have h := laneCodes_eq (μ - laneBits) laneBits (stackTable μ q)
      (by simp [← pow_add, Nat.sub_add_cancel hμ6]) p
    have hrow := readRow_stackWord (R := R) hμ6 q hp
    rw [← stackWordFast_eq (by omega)] at hrow
    have hf : stackTableA μ q.values.toArray = (stackTable μ q).toArray := by
      rw [← hstl, Array.toArray_toList]
    simp only [vfold, List.foldl_nil, lanesOfV, ite_true, hrow, hf]
    exact h

end
end LeanVM.Protocol.Whir.Complete
