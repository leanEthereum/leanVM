import Whir.ExtractionField
import Mathlib.FieldTheory.Finite.Trace

/-! A bounded executable characteristic-two trace kernel for source extension words. It squares iteratively, never computes scalar powers using an exponential exponent loop, and never enumerates the field. The canonical 192-word binary basis bridge and the efficient Shoup/Roth backend refinement remain separate from these trace identities. -/
namespace Whir.TraceExtraction
open Concrete
open scoped BigOperators

structure TraceResult (F : Type*) where
  value : F
  nextPower : F
  fieldOps : Nat

section Kernel
variable {F : Type*} [CommRing F]

def traceLoop : Nat → F → F → TraceResult F
  | 0, term, total => ⟨total, term, 0⟩
  | count + 1, term, total =>
    let rest := traceLoop count (term * term) (total + term)
    ⟨rest.value, rest.nextPower, rest.fieldOps + 2⟩

theorem traceLoop_value (count : Nat) (term total : F) :
    (traceLoop count term total).value = total + ∑ i ∈ Finset.range count, term ^ (2 ^ i) := by
  induction count generalizing term total with
  | zero => simp [traceLoop]
  | succ count ih =>
    rw [traceLoop, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_one]
    have shifted : ∑ i ∈ Finset.range count, (term * term) ^ (2 ^ i) =
        ∑ i ∈ Finset.range count, term ^ (2 ^ (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_two, ← pow_mul, Nat.pow_succ]
      congr 1
      omega
    rw [shifted]
    ring

theorem traceLoop_nextPower (count : Nat) (term total : F) :
    (traceLoop count term total).nextPower = term ^ (2 ^ count) := by
  induction count generalizing term total with
  | zero => simp [traceLoop]
  | succ count ih =>
    rw [traceLoop, ih, ← pow_two, ← pow_mul, Nat.pow_succ]
    congr 1
    omega

theorem traceLoop_fieldOps (count : Nat) (term total : F) :
    (traceLoop count term total).fieldOps = 2 * count := by
  induction count generalizing term total with
  | zero => rfl
  | succ count ih => simp [traceLoop, ih]; omega

end Kernel

/-- The actual 192-bit extension trace uses 192 squares and 192 additions, with canonical ring operations. -/
def trace (word : E) : E := (traceLoop 192 word 0).value

theorem trace_eq_powerSum (word : E) :
    trace word = ∑ i ∈ Finset.range 192, word ^ (2 ^ i) := by
  simp only [trace, traceLoop_value, zero_add]

theorem trace_384_fieldOps (word : E) : (traceLoop 192 word 0).fieldOps = 384 := by
  rw [traceLoop_fieldOps]

section FieldTrace
local instance : Field E := ExtractionField.field
noncomputable instance binaryAlgebra : Algebra (ZMod 2) E :=
  (ZMod.castHom (dvd_refl 2) E).toAlgebra

theorem binary_finrank : Module.finrank (ZMod 2) E = 192 := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  simpa only [ZMod.card, FieldModel.card_E] using
    (Module.card_eq_pow_finrank (K := ZMod 2) (V := E)).symm

theorem trace_eq_algebraTrace (word : E) :
    trace word = algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E word) := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow, binary_finrank]
  simpa using trace_eq_powerSum word

theorem trace_base_values (word : E) : trace word = 0 ∨ trace word = 1 := by
  rw [trace_eq_algebraTrace]
  generalize Algebra.trace (ZMod 2) E word = result
  fin_cases result
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

/-- Nondegeneracy is supplied by the proved finite-field trace form, not by a guessed concrete trace-one word. -/
theorem trace_pair_separates {a b : E} (different : a ≠ b) :
    ∃ beta : E, trace (beta * (a - b)) ≠ 0 := by
  have nonzero : a - b ≠ 0 := sub_ne_zero.mpr different
  have nondegenerate := (traceForm_nondegenerate (ZMod 2) E).1 (a - b)
  by_contra! vanished
  apply nonzero
  apply nondegenerate
  intro beta
  have zeroTrace := vanished beta
  rw [trace_eq_algebraTrace] at zeroTrace
  have zero : Algebra.trace (ZMod 2) E (beta * (a - b)) = 0 :=
    (algebraMap (ZMod 2) E).injective (by simpa using zeroTrace)
  simpa [Algebra.traceForm_apply, mul_sub, map_sub, mul_comm] using zero

/-- Any actual binary basis reduces field-wide trace separation to only its 192 vectors. This theorem does not construct or execute a classical chosen basis. -/
theorem basis_trace_separates (basis : Module.Basis (Fin 192) (ZMod 2) E)
    {a b : E} (different : a ≠ b) :
    ∃ index, trace (basis index * (a - b)) ≠ 0 := by
  by_contra! vanished
  let map : E →ₗ[ZMod 2] ZMod 2 :=
    (Algebra.trace (ZMod 2) E).comp (LinearMap.mulRight (ZMod 2) (a - b))
  have zeroMap : map = 0 := by
    apply basis.ext
    intro index
    have zeroTrace := vanished index
    rw [trace_eq_algebraTrace] at zeroTrace
    have zero : Algebra.trace (ZMod 2) E (basis index * (a - b)) = 0 :=
      (algebraMap (ZMod 2) E).injective (by simpa using zeroTrace)
    simpa [map] using zero
  obtain ⟨beta, separated⟩ := trace_pair_separates different
  apply separated
  rw [trace_eq_algebraTrace]
  have : Algebra.trace (ZMod 2) E (beta * (a - b)) = 0 := by
    simpa [map] using DFunLike.congr_fun zeroMap beta
  simp [this]

end FieldTrace

#print axioms traceLoop_value
#print axioms traceLoop_nextPower
#print axioms traceLoop_fieldOps
#print axioms trace_eq_powerSum
#print axioms trace_384_fieldOps
#print axioms binary_finrank
#print axioms trace_eq_algebraTrace
#print axioms trace_base_values
#print axioms trace_pair_separates
#print axioms basis_trace_separates
end Whir.TraceExtraction
