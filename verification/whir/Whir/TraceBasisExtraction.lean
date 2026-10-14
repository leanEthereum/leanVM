import Whir.TraceExtraction
import CompPoly.Univariate.Roots.Shoup.Basic

/-! The 192 canonical bit vectors of the source's three-word extension. Basis correctness uses literal bit coordinates, not a chosen or enumerated field basis. -/
namespace Whir.TraceBasisExtraction
open Concrete TraceExtraction
open scoped BigOperators
local instance : Field E := ExtractionField.field

abbrev BitIndex := Fin 3 × Fin 64

def component (word : E) (part : Fin 3) : K :=
  if part.val = 0 then word.c0 else if part.val = 1 then word.c1 else word.c2

def bits (word : E) (index : BitIndex) : ZMod 2 :=
  if (component word index.1).toBitVec.getLsbD index.2.val then 1 else 0

def bitVector (index : BitIndex) : E :=
  let word := (1 : K) <<< UInt64.ofNat index.2.val
  if index.1.val = 0 then ⟨word, 0, 0⟩ else
    if index.1.val = 1 then ⟨0, word, 0⟩ else ⟨0, 0, word⟩

theorem bits_add (a b : E) (index : BitIndex) : bits (a + b) index = bits a index + bits b index := by
  rcases index with ⟨part, bit⟩
  change bits (E.add a b) (part, bit) = _
  fin_cases part <;> simp only [bits, component, E.add, Nat.reduceEqDiff,
    Nat.reduceEqDiff, if_true, if_false, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  all_goals
    split <;> split <;> simp_all <;> decide

noncomputable def readBits : E →ₗ[ZMod 2] (BitIndex → ZMod 2) where
  toFun := bits
  map_add' a b := funext (bits_add a b)
  map_smul' scalar word := by
    fin_cases scalar
    · change bits ((0 : ZMod 2) • word) = (0 : ZMod 2) • bits word
      rw [zero_smul, zero_smul]
      funext index
      change bits E.zero index = 0
      simp [bits, component, E.zero]
    · change bits ((1 : ZMod 2) • word) = (1 : ZMod 2) • bits word
      rw [one_smul, one_smul]

private theorem word_bits_injective (a b : K)
    (same : ∀ bit : Fin 64,
      (if a.toBitVec.getLsbD bit.val then (1 : ZMod 2) else 0) =
        (if b.toBitVec.getLsbD bit.val then (1 : ZMod 2) else 0)) : a = b := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro index bound
  have observed := same ⟨index, bound⟩
  cases ha : a.toBitVec.getLsbD index <;> cases hb : b.toBitVec.getLsbD index <;> simp_all

theorem readBits_injective : Function.Injective readBits := by
  intro a b same
  have c0 : a.c0 = b.c0 := word_bits_injective _ _ (fun bit => by
    simpa [readBits, bits, component] using congrFun same ((0 : Fin 3), bit))
  have c1 : a.c1 = b.c1 := word_bits_injective _ _ (fun bit => by
    simpa [readBits, bits, component] using congrFun same ((1 : Fin 3), bit))
  have c2 : a.c2 = b.c2 := word_bits_injective _ _ (fun bit => by
    simpa [readBits, bits, component] using congrFun same ((2 : Fin 3), bit))
  cases a
  cases b
  simp_all

private theorem bitWord_values (bit observed : Fin 64) :
    (if (((1 : K) <<< UInt64.ofNat bit.val).toBitVec.getLsbD observed.val) then
      (1 : ZMod 2) else 0) = if observed = bit then 1 else 0 := by
  rw [← FieldModel.coeff_bitPoly]
  change (FieldModel.wordPoly ((1 : K) <<< UInt64.ofNat bit.val)).coeff observed.val = _
  rw [FieldModel.wordPoly_basis bit.val bit.isLt]
  simp only [Polynomial.coeff_X_pow, Fin.ext_iff, eq_comm]

theorem readBits_bitVector (index : BitIndex) : readBits (bitVector index) = Pi.single index 1 := by
  funext observed
  rcases index with ⟨part, bit⟩
  rcases observed with ⟨otherPart, otherBit⟩
  fin_cases part <;> fin_cases otherPart <;>
    simp only [readBits, LinearMap.coe_mk, AddHom.coe_mk, bits, component, bitVector,
      Nat.reduceEqDiff, ite_true, ite_false, bitWord_values, Pi.single_apply,
      UInt64.toBitVec_zero, BitVec.getLsbD_zero, Bool.false_eq_true,
      Prod.mk.injEq, Fin.ext_iff, Nat.reduceEqDiff, true_and, false_and]

theorem readBits_surjective : Function.Surjective readBits := by
  intro values
  refine ⟨∑ index, values index • bitVector index, ?_⟩
  rw [map_sum]
  simp only [map_smul, readBits_bitVector]
  exact (pi_eq_sum_univ' values).symm

noncomputable def coordinateEquiv : E ≃ₗ[ZMod 2] (BitIndex → ZMod 2) :=
  LinearEquiv.ofBijective readBits ⟨readBits_injective, readBits_surjective⟩

noncomputable def binaryBasis : Module.Basis BitIndex (ZMod 2) E :=
  Module.Basis.ofEquivFun coordinateEquiv

theorem binaryBasis_value (index : BitIndex) : binaryBasis index = bitVector index := by
  apply readBits_injective
  rw [readBits_bitVector]
  change coordinateEquiv (binaryBasis index) = _
  simp [binaryBasis, Module.Basis.coe_ofEquivFun]

def canonicalBasis : Array E := Array.ofFn fun index : Fin 192 =>
  bitVector (finProdFinEquiv.symm index : BitIndex)

theorem canonicalBasis_trace_separates {a b : E} (different : a ≠ b) :
    ∃ beta, beta ∈ canonicalBasis.toList ∧ trace (beta * (a - b)) ≠ 0 := by
  let basis : Module.Basis (Fin 192) (ZMod 2) E := binaryBasis.reindex finProdFinEquiv
  obtain ⟨index, separated⟩ := basis_trace_separates basis different
  refine ⟨basis index, ?_, separated⟩
  simp only [canonicalBasis, Array.toList_ofFn]
  apply List.mem_ofFn.mpr
  refine ⟨index, ?_⟩
  simp [canonicalBasis, basis, binaryBasis_value]

/-- Source-specialized trace metadata for the certified, non-enumerating Shoup splitter. Executing the generic splitter still requires a fast scalar-power refinement, separately from this bounded trace function. -/
def traceContext : CompPoly.CPolynomial.Roots.FiniteField.SmallPrimeTraceContext E where
  q := 2 ^ 192
  finite := inferInstance
  card_eq := FieldModel.natCard_E
  frobenius_fixed word := by simpa only [FieldModel.card_E] using FiniteField.pow_card word
  p := 2
  k := 192
  p_prime := by decide
  q_eq := rfl
  baseConstants := #[0, 1]
  baseConstants_size := rfl
  basis := canonicalBasis
  basis_size := Array.size_ofFn
  traceValue := trace
  traceValue_eq_powerSum word := by
    rw [CompPoly.CPolynomial.Roots.FiniteField.tracePowerSum_eq_sum_range]
    exact trace_eq_powerSum word
  traceValue_mem_base word := by
    rcases trace_base_values word with h | h <;> simp [h]
  trace_separates := canonicalBasis_trace_separates

#print axioms bits_add
#print axioms readBits_injective
#print axioms readBits_bitVector
#print axioms readBits_surjective
#print axioms binaryBasis_value
#print axioms canonicalBasis_trace_separates
end Whir.TraceBasisExtraction
