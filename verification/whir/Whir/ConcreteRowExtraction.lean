import Whir.ReedSolomonExtraction
import Whir.ExtractionField
import CompPoly.Univariate.ToPoly.Degree
import Whir.TriangularExtraction

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-! Concrete WHIR row decoding in the unique radius, on the actual source nodes
and novel encoding. `extractRow_recovers` recovers literal base words and rejects
non-base coefficients rather than projecting arbitrary extension words.
`countedExtractRow` includes Gao preprocessing, full novel preparation and
peeling; its value equals `extractRow`. Its coefficient-arithmetic count is
bounded by the explicit single-variable polynomial `rowArithmeticPolynomial N`
for the no-wrap source profile. This counts extension-field arithmetic,
including 382 multiplications per inverse, not comparisons or memory traffic.
All decoders require access to an entire received row. They are not extractors
for a Merkle digest and do not themselves establish a PCS access hypothesis. -/
namespace Whir.ConcreteRowExtraction
open Concrete CompPoly

/-- The machine's actual no-wrap evaluation nodes, not a substituted RS domain. -/
def domain (depth : Nat) (noWrap : depth ≤ 64) : CompPoly.ReedSolomon.Domain E :=
  ⟨Array.ofFn (fun i : Fin (2 ^ depth) => E.ofK (UInt64.ofNat i.val)), by
    simp only [Array.toList_ofFn]
    exact List.nodup_ofFn_ofInjective (AdditiveCode.concreteDomain depth noWrap).injective⟩

@[simp] theorem domain_size (depth : Nat) (noWrap : depth ≤ 64) :
    (domain depth noWrap).n = 2 ^ depth := by simp [domain, CompPoly.ReedSolomon.Domain.n]

/-- The dictionary is local and computational. Public input does not gain free access to a hashed root's preimage. -/
def decode (n rate : Nat) (noWrap : n + rate ≤ 64)
    (received : Vector E (domain (n + rate) noWrap).n) : Option (CPolynomial E) :=
  @ReedSolomonExtraction.decode E ExtractionField.field inferInstance inferInstance
    (2 ^ n) (domain (n + rate) noWrap) received

section Correctness
local instance : Field E := ExtractionField.field

private theorem prepared_subspace (v : Nat → E) (n : Nat) :
    (TriangularExtraction.subspace v n).toPoly =
      @AdditiveCode.subspace E FieldModel.instFieldE v n := by
  induction n with
  | zero => simp [TriangularExtraction.subspace, AdditiveCode.subspace, CPolynomial.X_toPoly]
  | succ n ih =>
    simp [TriangularExtraction.subspace, AdditiveCode.subspace, CPolynomial.toPoly_mul,
      CPolynomial.toPoly_add, CPolynomial.C_toPoly, CPolynomial.eval_toPoly, ih]

private theorem prepared_normalized (v : Nat → E) (n : Nat) :
    (TriangularExtraction.normalized v n).toPoly =
      @AdditiveCode.normalized E FieldModel.instFieldE v n := by
  rw [TriangularExtraction.normalized, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    CPolynomial.eval_toPoly, prepared_subspace]
  change Polynomial.C (ExtractionField.inverse
    ((@AdditiveCode.subspace E FieldModel.instFieldE v n).eval (v n))) *
    (@AdditiveCode.subspace E FieldModel.instFieldE v n) = _
  rw [ExtractionField.inverse_eq]
  rfl

private theorem prepared_novel (v : Nat → E) (n j : Nat) :
    (TriangularExtraction.novel v n j).toPoly =
      @AdditiveCode.novel E FieldModel.instFieldE v n j := by
  induction n generalizing j with
  | zero => simp [TriangularExtraction.novel, AdditiveCode.novel, CPolynomial.toPoly_one]
  | succ n ih =>
    simp only [TriangularExtraction.novel, AdditiveCode.novel]
    split_ifs <;> simp [CPolynomial.toPoly_mul, prepared_normalized, ih]

/-- Executable inversion of the actual novel basis. -/
def coefficients (n : Nat) (p : CPolynomial E) : Array E :=
  TriangularExtraction.recover
    (TriangularExtraction.novel (AdditiveCode.bitBasis E.ofK) n) (2 ^ n) p

/-- Instrumented coefficient peeling with the actual extension inverse charged
at 382 extension multiplications. The novel basis is the real WHIR basis;
preparing that basis and allocating/reversing the result are not charged here. -/
def countedCoefficients (n : Nat) (p : CPolynomial E) : Array E × Nat :=
  let result := TriangularExtraction.countedPeel 382
    (TriangularExtraction.novel (AdditiveCode.bitBasis E.ofK) n) (2 ^ n) p
  (result.1.reverse.toArray, result.2)

theorem countedCoefficients_value (n : Nat) (p : CPolynomial E) :
    (countedCoefficients n p).1 = coefficients n p := by
  simp [countedCoefficients, coefficients, TriangularExtraction.recover,
    TriangularExtraction.countedPeel_value]

/-- A quadratic arithmetic bound for the actual post-Gao coefficient-peeling
phase. The support bound follows from the decoded degree and the proved
triangular WHIR basis, not from an assumed internal-loop resource counter.
This does not claim a full decoder machine-time bound. -/
theorem countedCoefficients_cost (n : Nat) (noWrap : n ≤ 64) (p : CPolynomial E)
    (degree : p.degree < 2 ^ n) :
    (countedCoefficients n p).2 ≤ 2 ^ n * (4 * 2 ^ n + 384) := by
  apply TriangularExtraction.countedPeel_cost 382
    (TriangularExtraction.novel (AdditiveCode.bitBasis E.ofK) n) (2 ^ n) (2 ^ n) p
  · exact CPolynomial.mem_degreeLT_iff_size_le.mp (CPolynomial.mem_degreeLT.mpr degree)
  · intro i hi
    apply CPolynomial.mem_degreeLT_iff_size_le.mp
    apply CPolynomial.mem_degreeLT.mpr
    rw [CPolynomial.degree_lt_iff_coeff_zero]
    intro j hj
    rw [CPolynomial.coeff_toPoly, prepared_novel]
    have novelDegree := @AdditiveCode.novel_degree E FieldModel.instFieldE
      (AdditiveCode.bitBasis E.ofK) inferInstance n
      (AdditiveCode.concrete_bitBasis_independent n noWrap) i hi
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [novelDegree.1]; omega)

/-- Base-word projection is guarded. An extension coefficient with nonzero higher components fails rather than being silently truncated. -/
def baseWords (n : Nat) (p : CPolynomial E) : Option (Array K) :=
  let recovered := coefficients n p
  if recovered.all (fun e => e.c1 == 0 && e.c2 == 0) then
    some (recovered.map E.c0)
  else none

/-- Successful projection certifies every recovered extension coefficient is
literally the embedding of the returned base word, rather than a truncation. -/
theorem baseWords_sound (n : Nat) (p : CPolynomial E) (a : Array K)
    (success : baseWords n p = some a) :
    coefficients n p = a.map E.ofK := by
  dsimp only [baseWords] at success
  split_ifs at success with guard
  · have output : (coefficients n p).map E.c0 = a := Option.some.inj success
    rw [← output, Array.map_map]
    apply Array.ext
    · simp
    · intro i left right
      have components := Array.all_eq_true.mp guard i left
      simp only [Bool.and_eq_true, beq_iff_eq] at components
      have low : (coefficients n p)[i].c1 = 0 := components.1
      have high : (coefficients n p)[i].c2 = 0 := components.2
      simp only [Array.getElem_map, Function.comp_apply, E.ofK]
      cases equal : (coefficients n p)[i]
      simp_all

def extractRow (n rate : Nat) (noWrap : n + rate ≤ 64)
    (received : Vector E (domain (n + rate) noWrap).n) : Option (Array K) :=
  (decode n rate noWrap received).bind (baseWords n)

theorem coefficients_recovers (n : Nat) (noWrap : n ≤ 64)
    (a : Array E) (shape : a.size = 2 ^ n) (p : CPolynomial E)
    (polynomial : p.toPoly = AdditiveCode.concretePolynomial n a) :
    coefficients n p = a := by
  have representation : p.toPoly = ∑ i ∈ Finset.range (2 ^ n),
      Polynomial.C (a[i]!) *
        @AdditiveCode.novel E FieldModel.instFieldE (AdditiveCode.bitBasis E.ofK) n i := by
    rw [polynomial]
    unfold AdditiveCode.concretePolynomial AdditiveCode.arrayPolynomial AdditiveCode.polynomial
    rw [Finset.sum_range]
    simp [AdditiveCode.concreteBaseRepresentation, QueryRefinement.concreteRepresentation,
      Polynomial.smul_eq_C_mul]
  have equal : p = ∑ i ∈ Finset.range (2 ^ n), CPolynomial.C (a[i]!) *
      TriangularExtraction.novel (AdditiveCode.bitBasis E.ofK) n i := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro j
    rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, representation]
    apply congrArg (fun q : Polynomial E => q.coeff j)
    rw [CPolynomial.toPoly_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, prepared_novel]
  have recovered := TriangularExtraction.recover_recovers
    (TriangularExtraction.novel (AdditiveCode.bitBasis E.ofK) n) (2 ^ n) (fun i => a[i]!)
    (by
      intro i j hi hij
      rw [CPolynomial.coeff_toPoly, prepared_novel]
      have degree := @AdditiveCode.novel_degree E FieldModel.instFieldE
        (AdditiveCode.bitBasis E.ofK) inferInstance n
        (AdditiveCode.concrete_bitBasis_independent n noWrap) i hi
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (degree.1.trans_lt hij))
    (by
      intro i hi
      rw [CPolynomial.coeff_toPoly, prepared_novel]
      have degree := @AdditiveCode.novel_degree E FieldModel.instFieldE
        (AdditiveCode.bitBasis E.ofK) inferInstance n
        (AdditiveCode.concrete_bitBasis_independent n noWrap) i hi
      have leading : (@AdditiveCode.novel E FieldModel.instFieldE
          (AdditiveCode.bitBasis E.ofK) n i).coeff i =
          (@AdditiveCode.novel E FieldModel.instFieldE (AdditiveCode.bitBasis E.ofK) n i).leadingCoeff := by
        simpa only [degree.1] using
          (Polynomial.coeff_natDegree (p := @AdditiveCode.novel E FieldModel.instFieldE
            (AdditiveCode.bitBasis E.ofK) n i))
      rw [leading]
      exact degree.2)
  rw [coefficients, equal, recovered]
  apply Array.ext
  · simp [shape]
  · intro i left right
    simp [getElem!_pos, right]

theorem baseWords_recovers (n : Nat) (noWrap : n ≤ 64)
    (a : Array K) (shape : a.size = 2 ^ n) (p : CPolynomial E)
    (polynomial : p.toPoly = AdditiveCode.concretePolynomial n (a.map E.ofK)) :
    baseWords n p = some a := by
  rw [baseWords, coefficients_recovers n noWrap (a.map E.ofK) (by simp [shape]) p polynomial]
  simp [E.ofK, Array.map_map, Function.comp_def]

/-- For a supplied supported row inside the exact Gao radius, the actual decoder returns its actual dense-encoder polynomial. This is stronger than uniqueness or existence alone, but still does not prove verifier acceptance implies this radius. -/
theorem decode_actual_row (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (a : Array E) (shape : a.size = 2 ^ n)
    (received : Vector E (domain (n + rate) noWrap).n)
    (radius : 2 * hammingDist received.get (fun i => (encode n rate a)[i.val]!) ≤
      2 ^ (n + rate) - 2 ^ n) :
    ∃ p, decode n rate noWrap received = some p ∧
      p.toPoly = AdditiveCode.concretePolynomial n a := by
  let p : CPolynomial E := CPolynomial.toPolyLinearEquiv.symm
    (AdditiveCode.concretePolynomial n a)
  have polynomial : p.toPoly = AdditiveCode.concretePolynomial n a :=
    CPolynomial.toPolyLinearEquiv.apply_symm_apply _
  have degree : p.degree < 2 ^ n := by
    rw [CPolynomial.degree_toPoly, polynomial]
    exact AdditiveCode.concrete_polynomial_degree_lt n (by omega) a
  have node (i : Fin (domain (n + rate) noWrap).n) :
      p.toPoly.eval ((domain (n + rate) noWrap).val[i]) = (encode n rate a)[i.val]! := by
    rw [polynomial]
    have within : i.val < 2 ^ (n + rate) := by simpa using i.isLt
    rw [AdditiveCode.concrete_encode_eval n rate a shape i.val within]
    rw [show (domain (n + rate) noWrap).val[i] = E.ofK (UInt64.ofNat i.val) from by
      change (Array.ofFn (fun q : Fin (2 ^ (n + rate)) => E.ofK (UInt64.ofNat q.val)))[i.val] = _
      rw [Array.getElem_ofFn]]
  refine ⟨p, ?_, polynomial⟩
  change ReedSolomonExtraction.decode (2 ^ n) (domain (n + rate) noWrap) received = some p
  apply ReedSolomonExtraction.decode_recovers (2 ^ n) (domain (n + rate) noWrap)
    received p (by simpa using redundancy) degree
  simpa only [domain_size, node] using radius

/-- A returned polynomial identifies at most one valid extension coefficient array. This theorem is not an executable novel-basis inversion algorithm. -/
theorem returned_row_identifies_coefficients (n : Nat) (noWrap : n ≤ 64)
    (a b : Array E) (aShape : a.size = 2 ^ n) (bShape : b.size = 2 ^ n)
    (p : CPolynomial E)
    (aPolynomial : p.toPoly = AdditiveCode.concretePolynomial n a)
    (bPolynomial : p.toPoly = AdditiveCode.concretePolynomial n b) : a = b :=
  AdditiveCode.concrete_polynomial_injective n noWrap a b aShape bShape
    (aPolynomial.symm.trans bPolynomial)


/-- A complete row decoder endpoint, returning actual occupied base words. The radius concerns one supported row and the input is an explicitly available received word, not a digest. -/
theorem extractRow_recovers (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (a : Array K) (shape : a.size = 2 ^ n)
    (received : Vector E (domain (n + rate) noWrap).n)
    (radius : 2 * hammingDist received.get (fun i => (encode n rate (a.map E.ofK))[i.val]!) ≤
      2 ^ (n + rate) - 2 ^ n) :
    extractRow n rate noWrap received = some a := by
  obtain ⟨p, decoded, polynomial⟩ :=
    decode_actual_row n rate noWrap redundancy (a.map E.ofK) (by simp [shape]) received radius
  rw [extractRow, decoded, Option.bind_some]
  exact baseWords_recovers n (by omega) a shape p polynomial

/-- Include the actual recursively recomputed novel-basis preparation in the
field-arithmetic cost of projection, before performing the same guarded
base-word conversion. Coefficient lookups and component comparisons are not
field arithmetic; they are not silently charged as multiplications. -/
def countedBaseWords (n : Nat) (p : CPolynomial E) : Option (Array K) × Nat :=
  let result := TriangularExtraction.countedPreparedPeel 382
    (AdditiveCode.bitBasis E.ofK) n (2 ^ n) p
  let recovered := result.1.reverse.toArray
  (if recovered.all (fun e => e.c1 == 0 && e.c2 == 0) then
    some (recovered.map E.c0) else none, result.2)

theorem countedBaseWords_value (n : Nat) (p : CPolynomial E) :
    (countedBaseWords n p).1 = baseWords n p := by
  simp only [countedBaseWords, TriangularExtraction.countedPreparedPeel_value,
    baseWords, coefficients, TriangularExtraction.recover]
  rfl

def projectionBudget (n : Nat) : Nat :=
  2 ^ n * (TriangularExtraction.novelBudget 382 n (2 ^ (n + 1)) +
    4 * 2 ^ (n + 1) + 384)

theorem countedBaseWords_cost (n : Nat) (p : CPolynomial E) (degree : p.degree < 2 ^ n) :
    (countedBaseWords n p).2 ≤ projectionBudget n := by
  apply TriangularExtraction.countedPreparedPeel_cost 382
    (AdditiveCode.bitBasis E.ofK) n (2 ^ n) (2 ^ (n + 1)) p (Nat.le_refl _)
  exact (CPolynomial.mem_degreeLT_iff_size_le.mp
    (CPolynomial.mem_degreeLT.mpr degree)).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : Nat)) (Nat.le_succ n))

/-- Instrument the whole executable source-row decoder. Its input remains an
explicit received word; this is not an oracle for a hashed commitment.
The concrete domain constructor writes `N` embedded UInt64 coordinates and
uses no extension-field arithmetic. The field counter includes Gao's nodal
product, Lagrange interpolation, fueled Euclidean loop with actual degree
drop, final remainder/division, original novel-basis preparation, coefficient
peeling and the guarded projection. -/
def countedExtractRow (n rate : Nat) (noWrap : n + rate ≤ 64)
    (received : Vector E (domain (n + rate) noWrap).n) : Option (Array K) × Nat :=
  let decoded := ReedSolomonExtraction.countedDecode 382 (2 ^ n) (domain (n + rate) noWrap) received
  match decoded.1 with
  | none => (none, decoded.2)
  | some p =>
    let projected := countedBaseWords n p
    (projected.1, decoded.2 + projected.2)

theorem countedExtractRow_value (n rate : Nat) (noWrap : n + rate ≤ 64)
    (received : Vector E (domain (n + rate) noWrap).n) :
    (countedExtractRow n rate noWrap received).1 = extractRow n rate noWrap received := by
  simp only [countedExtractRow, ReedSolomonExtraction.countedDecode_value, extractRow, decode]
  split <;> simp_all [countedBaseWords_value]

/-- Explicit polynomial field-arithmetic budget. `N=2^(n+rate)`, `k=2^n`;
the log-depth parameter `n` occurs only polynomially in the basis term.
No field-size enumeration, inverse-as-unit-cost assumption, or hidden
intermediate-width hypothesis appears in this budget. -/
def rowArithmeticBudget (n rate : Nat) : Nat :=
  ReedSolomonExtraction.decoderBudget 382 (2 ^ (n + rate)) + projectionBudget n

theorem countedExtractRow_cost (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate))
    (received : Vector E (domain (n + rate) noWrap).n) :
    (countedExtractRow n rate noWrap received).2 ≤ rowArithmeticBudget n rate := by
  have decoderCost := ReedSolomonExtraction.countedDecode_cost 382 (2 ^ n)
    (domain (n + rate) noWrap) received
  rw [domain_size] at decoderCost
  unfold countedExtractRow
  cases output : (ReedSolomonExtraction.countedDecode 382 (2 ^ n)
      (domain (n + rate) noWrap) received).1 with
  | none =>
    simp only [output]
    exact decoderCost.trans (Nat.le_add_right _ _)
  | some p =>
    have success : ReedSolomonExtraction.decode (2 ^ n) (domain (n + rate) noWrap)
        received = some p := by
      rw [← ReedSolomonExtraction.countedDecode_value 382]
      exact output
    have degree := (ReedSolomonExtraction.decode_proximity (2 ^ n)
      (domain (n + rate) noWrap) received p (by simpa using redundancy) success).1
    simp only [output]
    exact Nat.add_le_add decoderCost (countedBaseWords_cost n p degree)

theorem countedExtractRow_recovers (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate)) (a : Array K) (shape : a.size = 2 ^ n)
    (received : Vector E (domain (n + rate) noWrap).n)
    (radius : 2 * hammingDist received.get (fun i => (encode n rate (a.map E.ofK))[i.val]!) ≤
      2 ^ (n + rate) - 2 ^ n) :
    (countedExtractRow n rate noWrap received).1 = some a ∧
      (countedExtractRow n rate noWrap received).2 ≤ rowArithmeticBudget n rate := by
  exact ⟨(countedExtractRow_value n rate noWrap received).trans
    (extractRow_recovers n rate noWrap redundancy a shape received radius),
    countedExtractRow_cost n rate noWrap redundancy received⟩

/-- Written in the actual dimensions rather than their logarithms: this is a
polynomial in depth, message length and block length, with the concrete inverse
charged at 382. The decoder term has degree seven in block length; the
novel-preparation/projection term has degree three in message length. -/
def sourceRowPolynomialBudget (depth dimension blockLength : Nat) : Nat :=
  ReedSolomonExtraction.decoderBudget 382 blockLength +
    dimension * (TriangularExtraction.novelBudget 382 depth (2 * dimension) +
      8 * dimension + 384)

theorem rowArithmeticBudget_eq_polynomial (n rate : Nat) :
    rowArithmeticBudget n rate =
      sourceRowPolynomialBudget n (2 ^ n) (2 ^ (n + rate)) := by
  unfold rowArithmeticBudget projectionBudget sourceRowPolynomialBudget
  rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by rw [Nat.pow_succ, Nat.mul_comm]]
  congr 2
  ring

/-- A single-variable polynomial budget for the no-wrap source profile.
Taking depth 64 is conservative; no sampling, soundness, or access premise is
used to derive the coefficient-arithmetic bound. -/
def rowArithmeticPolynomial (blockLength : Nat) : Nat :=
  sourceRowPolynomialBudget 64 blockLength blockLength

theorem sourceRowPolynomialBudget_mono (depth dimension blockLength : Nat)
    (depthBound : depth ≤ 64) (dimensionBound : dimension ≤ blockLength) :
    sourceRowPolynomialBudget depth dimension blockLength ≤ rowArithmeticPolynomial blockLength := by
  unfold rowArithmeticPolynomial sourceRowPolynomialBudget
    TriangularExtraction.novelBudget TriangularExtraction.preparationUnit
  gcongr

theorem countedExtractRow_polynomial_cost (n rate : Nat) (noWrap : n + rate ≤ 64)
    (redundancy : 2 ^ n < 2 ^ (n + rate))
    (received : Vector E (domain (n + rate) noWrap).n) :
    (countedExtractRow n rate noWrap received).2 ≤
      rowArithmeticPolynomial (2 ^ (n + rate)) := by
  have bound := countedExtractRow_cost n rate noWrap redundancy received
  rw [rowArithmeticBudget_eq_polynomial] at bound
  exact bound.trans (sourceRowPolynomialBudget_mono _ _ _ (by omega) redundancy.le)

end Correctness
end Whir.ConcreteRowExtraction
