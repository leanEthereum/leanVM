import Whir.AdditiveNormalization
import Whir.FieldModel

/-! The exact polynomial basis of the machine words is binary-independent
under any injective, XOR-preserving field representation. -/
namespace Whir.AdditiveCode
open Whir.Concrete Whir.FieldModel Polynomial
noncomputable section
variable {F : Type*} [Field F]

private theorem representation_zero (f : BaseRepresentation F) : f.map 0 = 0 := by
  have h := f.add 0 0
  simp only [UInt64.xor_self] at h
  linear_combination -h

/-- A span element is represented by an actual word whose polynomial has no
coefficient at or above the span dimension. This proves independence from the
machine bit basis, rather than assuming an RS encoder property. -/
private theorem binarySpan_preimage (f : BaseRepresentation F) (n : Nat) (hn : n ≤ 64)
    (x : F) (hx : x ∈ binarySpan (bitBasis f.map) n) :
    ∃ a : K, f.map a = x ∧ ∀ i, n ≤ i → (wordPoly a).coeff i = 0 := by
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := hx
    subst x
    exact ⟨0, representation_zero f, by simp⟩
  | succ n ih =>
    rcases hx with hx | ⟨y, hy, rfl⟩
    · obtain ⟨a, ha, hc⟩ := ih (by omega) x hx
      exact ⟨a, ha, fun i hi => hc i (by omega)⟩
    · obtain ⟨a, ha, hc⟩ := ih (by omega) y hy
      refine ⟨a ^^^ ((1 : K) <<< UInt64.ofNat n), ?_, ?_⟩
      · rw [f.add, ha]; rfl
      · intro i hi
        rw [wordPoly_xor, coeff_add, hc i (by omega), wordPoly_basis n (by omega)]
        simp [coeff_X_pow, show i ≠ n by omega]

/-- All first 64 actual bit-basis words remain binary independent. Multiplicative
or inverse correctness is not used in this argument. -/
theorem bitBasis_independent (f : BaseRepresentation F) (hinj : Function.Injective f.map)
    (n : Nat) (hn : n ≤ 64) : Independent (bitBasis f.map) n := by
  intro i hi hmem
  obtain ⟨a, ha, hc⟩ := binarySpan_preimage f i (by omega) (bitBasis f.map i) hmem
  have hae : a = (1 : K) <<< UInt64.ofNat i := hinj ha
  have hz := hc i le_rfl
  rw [hae, wordPoly_basis i (by omega), coeff_X_pow_self] at hz
  exact one_ne_zero hz

end
end Whir.AdditiveCode
