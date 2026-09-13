import SphincsSecurity.Proof.Forced.SecretGuessPairBound
import SphincsSecurity.Proof.Forced.FtsGuessBudget
import SphincsSecurity.Proof.Forced.FtsGuessReferenceWitness
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State lazyRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

noncomputable def pairRate (budget : Nat) : ENNReal :=
  (budget.choose 2 : ENNReal) * ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ ^ 2

theorem pairRate_le_quadratic (budget : Nat) :
    pairRate budget ≤ (budget : ENNReal) ^ 2 / (2 * ((2 ^ 128 - budget : Nat) : ENNReal) ^ 2) := by
  have hchoose : budget.choose 2 * 2 ≤ budget * budget := by
    rw [Nat.choose_two_right]
    exact (Nat.div_mul_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hcast : (budget.choose 2 : ENNReal) ≤ (budget : ENNReal) ^ 2 / 2 := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
    simpa only [pow_two, Nat.cast_mul, Nat.cast_ofNat] using (show ((budget.choose 2 * 2 : Nat) : ENNReal) ≤
      ((budget * budget : Nat) : ENNReal) by exact_mod_cast hchoose)
  calc
    _ ≤ (budget : ENNReal) ^ 2 / 2 * ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ ^ 2 := mul_le_mul' hcast le_rfl
    _ = _ := by
      rw [div_eq_mul_inv, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (by norm_num : (2 : ENNReal) ≠ 0)) (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤)),
        ENNReal.inv_pow, mul_assoc]

theorem pairRate_le_normalized (budget : Nat) :
    pairRate budget ≤ ((budget : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (budget : ENNReal) / 2 ^ 128) ^ 2) := by
  have hsub : 1 - (budget : ENNReal) / 2 ^ 128 = ((2 ^ 128 - budget : Nat) : ENNReal) / 2 ^ 128 := by
    rw [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.sub_div (fun _ _ => by positivity), ENNReal.div_self (by positivity) (by finiteness)]
  have hpow (value : ENNReal) : (value / 2 ^ 128) ^ 2 = value ^ 2 * ((2 ^ 128 : ENNReal)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, mul_pow]
  calc
    _ ≤ (budget : ENNReal) ^ 2 / (2 * ((2 ^ 128 - budget : Nat) : ENNReal) ^ 2) := pairRate_le_quadratic budget
    _ = _ := by
      rw [hsub, hpow, hpow, ← mul_assoc]
      exact (ENNReal.mul_div_mul_right _ _ (pow_ne_zero _ (by simp)) (by finiteness)).symm

theorem lazy_original_two_guesses (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)] ≤ pairRate budget := by
  have hbound := SecretGuessObservation.lazyRun_two_guesses
    (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
    (completedRun parameter (canonicalGraphRoot labels) labels adversary) PUnit.unit budget
    (fun result hr => (Nat.le_add_left _ _).trans
      (lazy_original_completedRun_probes dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary result hr))
  simpa only [pairRate, show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using hbound

end SphincsSecurity.Concrete.FtsGuessHash
