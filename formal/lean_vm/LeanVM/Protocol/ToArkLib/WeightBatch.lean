/-
  LeanVM.Protocol.ToArkLib.WeightBatch

  Weights of the inner-product interface combined by the powers of one value, and the answer to
  the combination. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.InnerProduct
public import LeanVM.Protocol.ToCompPoly.PowerBatching

/-!
# Batched weights

`Weight.batch W ρ` combines `k` weights on the cube by the powers of `ρ`: its values are
`Σ_j ρ^j·W_j(x)` and its extension, the one the asker evaluates, is `Σ_j ρ^j·W̃_j(r)`, from the
weights' own evaluators. The answer of a table to the combination is the combination of its
answers (`Weight.pair_batch`): the inner product is linear in the weight. So when `k` claims
`⟨W_j, t⟩ = c_j` hold, the answer at the combined weight is the combined value at every `ρ`.
The converse is a count, not an equivalence: a false family's combination meets the true one at
at most `k - 1` values of `ρ` (`card_false_batch_le`, the bound `batchSecurity` charges), and in
a field of fewer than `k` elements that can be every value.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The weights `W_j` combined by the powers of `ρ`: values and extension both `Σ_j ρ^j·W_j`. -/
def Weight.batch {k n : ℕ} (W : Fin k → Weight S n) (ρ : S) : Weight S n where
  onCube := batchWeight (fun j ↦ (W j).onCube) ρ
  mle := fun r ↦ powerBatch (fun j ↦ (W j).mle r) ρ
  mle_eq := fun r ↦ by
    rw [evalMle_batchWeight]
    exact congrArg (powerBatch · ρ) (funext fun j ↦ (W j).mle_eq r)

/-- The answer of a table to combined weights is the combination of its answers. -/
theorem Weight.pair_batch {k n : ℕ} (φ : R →+* S) (W : Fin k → Weight S n) (ρ : S)
    (t : CMlPolynomialEval R n) :
    (Weight.batch W ρ).pair φ t = powerBatch (fun j ↦ (W j).pair φ t) ρ := by
  simp only [Weight.pair, Weight.batch, batchWeight, powerBatch, Fin.getElem_fin,
    Vector.getElem_ofFn]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

end
end LeanVM.Protocol
