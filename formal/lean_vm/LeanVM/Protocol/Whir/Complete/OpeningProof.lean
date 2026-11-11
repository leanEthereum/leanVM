/-
  LeanVM.Protocol.Whir.Complete.OpeningProof

  Perfect completeness of the stacked WHIR opening: `OpeningComplete`.
-/

module

public import LeanVM.Protocol.Whir.Complete.Levels

/-!
# Completeness of the stacked opening

`openingComplete`: the honest opening (`honestOpening`, the statement's `levelsA` on the stack's
and the claims' tables) follows `verifyStackedOpening` from the stack's honest commitment, for an
admissible `(μ, R)` and at most `maxStackedClaims` claims that hold of the stack with multilinear
weights. The claim count's `require` holds by hypothesis; the levels are `follows_levelsA`, from
the invariant at level `0`: the claims' batched value is the pairing of the basis and stack tables
(`dot_values_eq_dot`), the batched basis at the rotated point is the extension of the basis table
(`multilinearEval_basisTable`), and the stack's rows are the stack table's lanes
(`readRow_stackWord`).
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  LeanVM.Protocol.Whir LeanVM.Protocol.EndToEnd LeanVM.Prover LeanVM.Prover.Enc Finset

@[expose] public section

/-- **Perfect completeness of the stacked opening.** -/
theorem openingComplete : OpeningComplete := by
  intro μ R hadm q claims hlen hholds hml
  obtain ⟨q₀, rest, hc, -⟩ := exists_ladder hadm
  have hμ6 : laneBits ≤ μ := le_trans (by decide) hadm.1
  have hμ28 : μ ≤ 30 := hadm.2.1
  rw [verifyStackedOpening_eq, require_bind_of hlen]
  unfold honestOpening
  simp only [Script.bind_eq]
  refine Follows.bind (fun cs c c' h ↦ ?_) _ _ _ (Follows.sampleE_sampleE _)
  obtain ⟨rfl, rfl⟩ := h
  simp only [verifyWhir, hc, Verifier.liftOption, VerifierProgram.bind_eq, VerifierProgram.ret_bind,
    List.head?_cons, Option.map_some, Option.getD_some]
  set scales := powers c claims.length
  have hst : (stackTable μ q).toArray.size = (2 ^ (μ - laneBits) + 0) * 2 ^ laneBits := by
    simp [← pow_add, Nat.sub_add_cancel hμ6]
  have hbs : (basisTable μ scales claims).toArray.size = 2 ^ (μ - laneBits) * 2 ^ laneBits := by
    simp [basisTable, ← pow_add, Nat.sub_add_cancel hμ6]
  refine follows_levelsA μ laneBits _ (⟨laneBits, R, q₀⟩ :: rest) 0 μ _ _ _ _ (stackWord μ R q)
    (2 ^ laneBits) (ladderOK_of_ladder hadm hc) rfl ?_
  intro level hl
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hl
  subst hl
  refine ⟨rfl, hbs, hst, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 ^ (μ - laneBits) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 30 + 6 ≤ 2 ^ 61 := by norm_num
    simp only [laneBits] at *
    omega
  · rw [dot_values_eq_dot hμ6 q scales claims hholds,
      dot_eq_sum _ _ (by simp [basisTable])]
    simp only [List.size_toArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      ← List.getD_eq_getElem?_getD]
  · simp only [List.length_nil]; omega
  · intro x hx
    simp only [runW, List.nil_append, List.foldl_nil]
    simp only at hx
    rw [multilinearEval_basisTable hμ6 scales claims hml x (by rw [hx]; omega)]
    rfl
  · intro p hp
    have h := laneCodes_eq (μ - laneBits) laneBits (stackTable μ q)
      (by simp [← pow_add, Nat.sub_add_cancel hμ6]) p
    simp only [vfold, List.foldl_nil, lanesOfV, ite_true]
    rw [readRow_stackWord hμ6 q hp]
    exact h

end
end LeanVM.Protocol.Whir.Complete
