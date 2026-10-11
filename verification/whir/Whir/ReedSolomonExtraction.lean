import Whir.AdditiveColumn
import CompPoly.Univariate.ReedSolomon.GaoCorrectness
import CompPoly.Univariate.ToPoly.Degree

/-! Executable unique-radius decoding, separated from access to committed rows.
This invokes the proved CompPoly Gao algorithm, not a classical witness selector.
`countedDecode` composes actual nodal/Lagrange construction, coefficient
convolution, textbook division/remainder and Euclidean cofactors. Its value is
the original decoder and its field-arithmetic cost has a polynomial bound in
block length, deriving intermediate widths rather than assuming trace bounds.
An explicit parameter charges each field inverse. Comparisons, allocation,
copying and prover responses are not field arithmetic. A decoded polynomial
alone is not a base-word WHIR witness or an accessible committed row. -/
namespace Whir.ReedSolomonExtraction
open Polynomial CompPoly
open scoped BigOperators

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

abbrev Domain := CompPoly.ReedSolomon.Domain F

/-- The actual executable decoder on an explicitly supplied received word. -/
def decode (k : Nat) (domain : Domain (F := F)) (received : Vector F domain.n) :
    Option (CPolynomial F) :=
  CompPoly.ReedSolomon.Gao.decode k domain received

/-- Turn a bounded executable polynomial into the message format used by Gao. -/
def message (k : Nat) (p : CPolynomial F) : Vector F k :=
  Vector.ofFn fun i => p.coeff i

omit [DecidableEq F] in
theorem message_polynomial (k : Nat) (p : CPolynomial F) (degree : p.degree < k) :
    CompPoly.ReedSolomon.messagePoly (message k p) = p :=
  CompPoly.ReedSolomon.messagePoly_ofFn_coeff k p degree

/-- This interface requires the whole received word. It supplies no digest-to-word oracle. -/
theorem decode_recovers (k : Nat) (domain : Domain (F := F))
    (received : Vector F domain.n) (p : CPolynomial F)
    (dimension : k < domain.n) (degree : p.degree < k)
    (radius : 2 * hammingDist received.get (fun i => p.toPoly.eval domain.val[i]) ≤
      domain.n - k) : decode k domain received = some p := by
  have encoded : (CompPoly.ReedSolomon.encode domain (message k p)).get =
      fun i => p.toPoly.eval domain.val[i] := by
    funext i
    rw [CompPoly.ReedSolomon.encode_get, message_polynomial k p degree,
      CPolynomial.eval_toPoly]
  have result := CompPoly.ReedSolomon.Gao.decode_eq_some k domain received dimension
    (message k p) (by rwa [encoded])
  simpa [decode, message_polynomial k p degree] using result

/-- Success certifies unique-radius proximity, not the WHIR public-claim relation. -/
theorem decode_proximity (k : Nat) (domain : Domain (F := F))
    (received : Vector F domain.n) (p : CPolynomial F)
    (dimension : k < domain.n) (success : decode k domain received = some p) :
    p.degree < k ∧ hammingDist received.get (fun i => p.toPoly.eval domain.val[i]) ≤
      (domain.n - k) / 2 := by
  obtain ⟨msg, equal, distance⟩ :=
    CompPoly.ReedSolomon.Gao.decode_sound k domain received dimension p success
  have encoded : (CompPoly.ReedSolomon.encode domain msg).get =
      fun i => p.toPoly.eval domain.val[i] := by
    funext i
    rw [CompPoly.ReedSolomon.encode_get, equal, CPolynomial.eval_toPoly]
  refine ⟨?_, by rwa [encoded] at distance⟩
  rw [← equal]
  exact CompPoly.ReedSolomon.messagePoly_degree_lt msg

/-- Interleaved lanes share a domain. Decoding does not mix observations from different candidate words. -/
def decodeLanes (k lanes : Nat) (domain : Domain (F := F))
    (received : Fin lanes → Vector F domain.n) : Array (Option (CPolynomial F)) :=
  Array.ofFn fun lane => decode k domain (received lane)

theorem decodeLanes_recovers (k lanes : Nat) (domain : Domain (F := F))
    (received : Fin lanes → Vector F domain.n) (p : Fin lanes → CPolynomial F)
    (dimension : k < domain.n) (degree : ∀ lane, (p lane).degree < k)
    (radius : ∀ lane, 2 * hammingDist (received lane).get
      (fun i => (p lane).toPoly.eval domain.val[i]) ≤ domain.n - k) :
    decodeLanes k lanes domain received = Array.ofFn (fun lane => some (p lane)) := by
  unfold decodeLanes
  congr 1
  funext lane
  exact decode_recovers k domain (received lane) (p lane) dimension (degree lane) (radius lane)

omit [BEq F] [LawfulBEq F] in
/-- A single common error support implies every lane's decoder radius. No random lane aggregation is assumed. -/
theorem lane_radius_of_common_support (k lanes : Nat) (domain : Domain (F := F))
    (received : Fin lanes → Vector F domain.n) (p : Fin lanes → CPolynomial F)
    (errors : Finset (Fin domain.n))
    (outside : ∀ lane i, i ∉ errors → (received lane).get i = (p lane).toPoly.eval domain.val[i])
    (radius : 2 * errors.card ≤ domain.n - k) (lane : Fin lanes) :
    2 * hammingDist (received lane).get (fun i => (p lane).toPoly.eval domain.val[i]) ≤
      domain.n - k := by
  have subset : (Finset.univ.filter fun i =>
      (received lane).get i ≠ (p lane).toPoly.eval domain.val[i]) ⊆ errors := by
    intro i hi
    by_contra missing
    exact (Finset.mem_filter.mp hi).2 (outside lane i missing)
  have count := Finset.card_le_card subset
  simp only [hammingDist] at *
  omega

/-! Coefficient-level refinement of the actual naive multiplication backend.
The count includes every scalar multiplication and every padded coefficient
addition in `Raw.mulRaw`, including zero coefficients. Trimming comparisons,
allocation, copying and word-level field instructions are separate costs. -/

/-- Instrument the convolution fold without substituting a faster, different
polynomial multiplication algorithm. -/
def countedMulFold (q : CPolynomial.Raw F) :
    List (F × Nat) → CPolynomial.Raw F → CPolynomial.Raw F × Nat
  | [], acc => (acc, 0)
  | (a, i) :: rest, acc =>
    let shifted := (CPolynomial.Raw.smul a q).mulPowX i
    let tail := countedMulFold q rest (acc.addRaw shifted)
    (tail.1, q.size + max acc.size shifted.size + tail.2)

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedMulFold_value (q : CPolynomial.Raw F)
    (terms : List (F × Nat)) (acc : CPolynomial.Raw F) :
    (countedMulFold q terms acc).1 =
      terms.foldl (fun acc pair =>
        acc.addRaw ((CPolynomial.Raw.smul pair.1 q).mulPowX pair.2)) acc := by
  induction terms generalizing acc with
  | nil => rfl
  | cons term rest ih => simp [countedMulFold, ih]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- The width is an actual upper bound on indices in the convolution, not the
field cardinality or a unit-cost polynomial-operation counter. -/
theorem countedMulFold_cost (q : CPolynomial.Raw F)
    (terms : List (F × Nat)) (acc : CPolynomial.Raw F) (width : Nat)
    (indices : ∀ pair ∈ terms, pair.2 < width)
    (accSize : acc.size ≤ width + q.size) :
    (countedMulFold q terms acc).2 ≤ terms.length * (width + 2 * q.size) := by
  induction terms generalizing acc with
  | nil => simp [countedMulFold]
  | cons term rest ih =>
    have index := indices term (by simp)
    have shiftedSize :
        ((CPolynomial.Raw.smul term.1 q).mulPowX term.2).size = term.2 + q.size := by
      simp [CPolynomial.Raw.mulPowX, CPolynomial.Raw.smul]
    have nextSize : (acc.addRaw
        ((CPolynomial.Raw.smul term.1 q).mulPowX term.2)).size ≤ width + q.size := by
      rw [CPolynomial.Raw.add_size, shiftedSize]
      omega
    have tail := ih (acc.addRaw
      ((CPolynomial.Raw.smul term.1 q).mulPowX term.2))
      (fun pair hp => indices pair (by simp [hp])) nextSize
    simp only [countedMulFold, List.length_cons, Nat.add_mul, shiftedSize]
    omega

def countedRawMul (p q : CPolynomial.Raw F) : CPolynomial.Raw F × Nat :=
  countedMulFold q p.zipIdx.toList #[]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedRawMul_value (p q : CPolynomial.Raw F) :
    (countedRawMul p q).1 = CPolynomial.Raw.mulRaw p q := by
  rw [countedRawMul, countedMulFold_value]
  simp only [CPolynomial.Raw.mulRaw, Array.foldl_toList]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedRawMul_cost (p q : CPolynomial.Raw F) :
    (countedRawMul p q).2 ≤ p.size * (p.size + 2 * q.size) := by
  apply le_trans (countedMulFold_cost q p.zipIdx.toList #[] p.size ?_ (by simp)) ?_
  · intro pair hp
    obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp hp
    have bound : i < p.size := by simpa using hi
    have pairIndex : pair.2 = i := by
      rw [← equal]
      simp
    omega
  · simp

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedRawMul_cost_of_size (p q : CPolynomial.Raw F) (width : Nat)
    (left : p.size ≤ width) (right : q.size ≤ width) :
    (countedRawMul p q).2 ≤ 3 * width ^ 2 := by
  calc
    _ ≤ p.size * (p.size + 2 * q.size) := countedRawMul_cost p q
    _ ≤ width * (width + 2 * width) :=
      Nat.mul_le_mul left (Nat.add_le_add left (Nat.mul_le_mul_left 2 right))
    _ = 3 * width ^ 2 := by ring

/-- Instrumented canonical multiplication returns exactly the polynomial used
by Gao and triangular extraction. Its field count is the raw convolution count. -/
def countedMul (p q : CPolynomial F) : CPolynomial F × Nat :=
  let result := countedRawMul p.val q.val
  (⟨result.1.trim, CPolynomial.Raw.Trim.isCanonical_trim _⟩, result.2)

omit [DecidableEq F] in
theorem countedMul_value (p q : CPolynomial F) :
    (countedMul p q).1 = p * q := by
  apply CPolynomial.ext
  change (countedRawMul p.val q.val).1.trim = _
  rw [countedRawMul_value]
  rfl

omit [DecidableEq F] in
theorem countedMul_cost (p q : CPolynomial F) (width : Nat)
    (left : p.val.size ≤ width) (right : q.val.size ≤ width) :
    (countedMul p q).2 ≤ 3 * width ^ 2 :=
  countedRawMul_cost_of_size p.val q.val width left right

/-- Raw power uses the same repeated-multiplication specification as the
division backend, rather than pretending that constructing `X^k` is free. -/
def countedRawPow (p : CPolynomial.Raw F) : Nat → CPolynomial.Raw F × Nat
  | 0 => (CPolynomial.Raw.C 1, 0)
  | n + 1 =>
    let previous := countedRawPow p n
    let product := countedRawMul p previous.1
    (product.1.trim, previous.2 + product.2)

omit [LawfulBEq F] [DecidableEq F] in
theorem countedRawPow_value (p : CPolynomial.Raw F) (n : Nat) :
    (countedRawPow p n).1 = p ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [countedRawPow, countedRawMul_value, ih, CPolynomial.Raw.pow_succ]
    rfl

theorem countedRawPow_X_cost (n : Nat) :
    (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).2 ≤ n * (4 * n + 8) := by
  induction n with
  | zero => simp [countedRawPow]
  | succ n ih =>
    have sizePower :
        (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).1.size = n + 1 := by
      rw [countedRawPow_value, CPolynomial.Raw.X_pow_eq_monomial_one]
      simp [CPolynomial.Raw.monomial]
    have product := countedRawMul_cost (CPolynomial.Raw.X : CPolynomial.Raw F)
      (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).1
    change (countedRawMul (CPolynomial.Raw.X : CPolynomial.Raw F)
      (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).1).2 ≤
        2 * (2 + 2 * (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).1.size)
      at product
    rw [sizePower] at product
    change (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).2 +
      (countedRawMul CPolynomial.Raw.X
        (countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) n).1).2 ≤ _
    nlinarith

/-- Instrument the actual textbook long-division loop. Even the two powers
`X^k` in the source loop are charged, as are all coefficient negations and
padded additions. Fuel is the dividend's coefficient-array length. -/
def countedDivAux : Nat → CPolynomial.Raw F → CPolynomial.Raw F →
    (CPolynomial.Raw F × CPolynomial.Raw F) × Nat
  | 0, p, _ => ((0, p), 0)
  | n + 1, p, q =>
    if p.size < q.size then ((0, p), 0) else
      let k := p.size - q.size
      let power := countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) k
      let shifted := countedRawMul q power.1
      let scaled := countedRawMul (CPolynomial.Raw.C p.leadingCoeff) shifted.1.trim
      let residue := (p - scaled.1.trim).trim
      let tail := countedDivAux n residue q
      let term := countedRawMul (CPolynomial.Raw.C p.leadingCoeff) power.1
      ((tail.1.1 + term.1.trim, tail.1.2),
        2 * power.2 + shifted.2 + scaled.2 + term.2 +
        scaled.1.trim.size + max p.size scaled.1.trim.size +
        max tail.1.1.size term.1.trim.size + tail.2)

omit [LawfulBEq F] [DecidableEq F] in
theorem countedDivAux_value (fuel : Nat) (p q : CPolynomial.Raw F) :
    (countedDivAux fuel p q).1 =
      CPolynomial.Raw.divModByMonicAux.go fuel p q := by
  induction fuel generalizing p with
  | zero => rfl
  | succ fuel ih =>
    simp only [countedDivAux, CPolynomial.Raw.divModByMonicAux.go]
    split_ifs
    · rfl
    · simp only [countedRawPow_value, countedRawMul_value]
      rw [ih]
      rfl

omit [DecidableEq F] in
private theorem raw_trim_support (p : CPolynomial.Raw F) (width : Nat)
    (zeros : ∀ i, width ≤ i → p.coeff i = 0) : p.trim.size ≤ width := by
  let canonical : CPolynomial F := ⟨p.trim, CPolynomial.Raw.Trim.isCanonical_trim p⟩
  apply (CPolynomial.mem_degreeLT_iff_size_le (p := canonical)).mp
  apply CPolynomial.mem_degreeLT.mpr
  rw [CPolynomial.degree_lt_iff_coeff_zero]
  intro i hi
  exact (CPolynomial.Raw.Trim.coeff_eq_coeff p i).trans (zeros i hi)

private theorem raw_shift_support (q : CPolynomial.Raw F) (k : Nat) :
    (q * CPolynomial.Raw.X ^ k).size ≤ q.size + k := by
  have support := raw_trim_support (q * CPolynomial.Raw.X ^ k) (q.size + k) (by
    intro i hi
    rw [CPolynomial.Raw.coeff_mul_X_pow]
    split_ifs <;> simp_all; omega)
  simpa only [CPolynomial.Raw.mul_is_trimmed] using support

omit [DecidableEq F] in
private theorem raw_constant_support (a : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.C a * p).size ≤ p.size := by
  rw [CPolynomial.Raw.C_mul_eq_smul_trim]
  exact (CPolynomial.Raw.Trim.size_le_size _).trans_eq (by
    simp [CPolynomial.Raw.smul])

omit [DecidableEq F] in
private theorem raw_div_residual_support (p q : CPolynomial.Raw F)
    (larger : q.size ≤ p.size) :
    ((p - CPolynomial.Raw.C p.leadingCoeff *
      (q * CPolynomial.Raw.X ^ (p.size - q.size))).trim).size ≤ p.size := by
  rw [← CPolynomial.Raw.subScaledShift_eq_sub_C_mul_X_pow p q p.leadingCoeff
    (p.size - q.size) (by omega)]
  exact (CPolynomial.Raw.Trim.size_le_size _).trans_eq (by
    simp)

theorem countedDivAux_quotient_support (fuel width : Nat) (p q : CPolynomial.Raw F)
    (inputSupport : p.size ≤ width) :
    (countedDivAux fuel p q).1.1.size ≤ width + 1 := by
  rw [countedDivAux_value]
  induction fuel generalizing p with
  | zero => simp [CPolynomial.Raw.divModByMonicAux.go]
  | succ fuel ih =>
    simp only [CPolynomial.Raw.divModByMonicAux.go]
    split_ifs with stop
    · simp
    · have residual := raw_div_residual_support p q (by omega)
      have tail := ih _ (residual.trans inputSupport)
      have term := raw_constant_support p.leadingCoeff
        (CPolynomial.Raw.X ^ (p.size - q.size))
      have powerSize : (CPolynomial.Raw.X ^ (p.size - q.size) :
          CPolynomial.Raw F).size = p.size - q.size + 1 := by
        rw [CPolynomial.Raw.X_pow_eq_monomial_one]
        simp [CPolynomial.Raw.monomial]
      rw [powerSize] at term
      change ((CPolynomial.Raw.divModByMonicAux.go fuel
        ((p - CPolynomial.Raw.C p.leadingCoeff *
          (q * CPolynomial.Raw.X ^ (p.size - q.size))).trim) q).1 +
        CPolynomial.Raw.C p.leadingCoeff * CPolynomial.Raw.X ^ (p.size - q.size)).size ≤ _
      exact (CPolynomial.Raw.Trim.size_le_size _).trans
        (CPolynomial.Raw.add_size.le.trans (max_le tail (by omega)))

/-- Cubic coefficient-arithmetic budget for textbook long division when its
fuel is the dividend's length. This holds even without monicity or canonicality
assumptions: the same-size residual invariant suffices for the runtime bound.
Power construction, convolution, negation and padded additions are included;
trimming comparisons, allocation and copying remain separate. -/
theorem countedDivAux_cost (fuel width : Nat) (p q : CPolynomial.Raw F)
    (inputSupport : p.size ≤ width) (divisorSupport : q.size ≤ width) :
    (countedDivAux fuel p q).2 ≤ fuel * (40 * (width + 1) ^ 2) := by
  induction fuel generalizing p with
  | zero => simp [countedDivAux]
  | succ fuel ih =>
    by_cases stop : p.size < q.size
    · simp [countedDivAux, stop]
    · let k := p.size - q.size
      let power := countedRawPow (CPolynomial.Raw.X : CPolynomial.Raw F) k
      let shifted := countedRawMul q power.1
      let scaled := countedRawMul (CPolynomial.Raw.C p.leadingCoeff) shifted.1.trim
      let term := countedRawMul (CPolynomial.Raw.C p.leadingCoeff) power.1
      let residual := (p - scaled.1.trim).trim
      have powerSize : power.1.size = k + 1 := by
        rw [countedRawPow_value, CPolynomial.Raw.X_pow_eq_monomial_one]
        simp [CPolynomial.Raw.monomial]
      have shiftedSize : shifted.1.trim.size ≤ width := by
        change (countedRawMul q power.1).1.trim.size ≤ _
        rw [countedRawMul_value, countedRawPow_value]
        exact (raw_shift_support q k).trans (by dsimp [k]; omega)
      have scaledSize : scaled.1.trim.size ≤ width := by
        rw [show scaled.1.trim = CPolynomial.Raw.C p.leadingCoeff * shifted.1.trim from by
          simp only [scaled, countedRawMul_value]; rfl]
        exact (raw_constant_support _ _).trans shiftedSize
      have residualSize : residual.size ≤ width := by
        dsimp only [residual, scaled, shifted, power]
        rw [countedRawMul_value, countedRawMul_value, countedRawPow_value]
        exact (raw_div_residual_support p q (by omega)).trans inputSupport
      have termSize : term.1.trim.size ≤ width + 1 := by
        change (countedRawMul (CPolynomial.Raw.C p.leadingCoeff) power.1).1.trim.size ≤ _
        rw [countedRawMul_value]
        exact (raw_constant_support _ _).trans (by rw [powerSize]; dsimp [k]; omega)
      have tailSize := countedDivAux_quotient_support fuel width residual q residualSize
      have tailCost := ih residual residualSize
      have powerCost := countedRawPow_X_cost (F := F) k
      have shiftedCost := countedRawMul_cost q power.1
      have scaledCost := countedRawMul_cost (CPolynomial.Raw.C p.leadingCoeff) shifted.1.trim
      have termCost := countedRawMul_cost (CPolynomial.Raw.C p.leadingCoeff) power.1
      change power.2 ≤ _ at powerCost
      change shifted.2 ≤ _ at shiftedCost
      change scaled.2 ≤ 1 * (1 + 2 * shifted.1.trim.size) at scaledCost
      change term.2 ≤ 1 * (1 + 2 * power.1.size) at termCost
      rw [powerSize] at shiftedCost termCost
      have kBound : k ≤ width := by dsimp [k]; omega
      have powerBudget : power.2 ≤ 12 * (width + 1) ^ 2 := by nlinarith
      have shiftedBudget : shifted.2 ≤ 3 * (width + 1) ^ 2 := by
        have := Nat.mul_le_mul divisorSupport
          (Nat.add_le_add divisorSupport (Nat.mul_le_mul_left 2 (by omega : k + 1 ≤ width + 1)))
        nlinarith
      have scaledBudget : scaled.2 ≤ 1 + 2 * width := by omega
      have termBudget : term.2 ≤ 3 + 2 * width := by omega
      simp only [countedDivAux, stop, ↓reduceIte]
      change 2 * power.2 + shifted.2 + scaled.2 + term.2 +
        scaled.1.trim.size + max p.size scaled.1.trim.size +
        max (countedDivAux fuel residual q).1.1.size term.1.trim.size +
        (countedDivAux fuel residual q).2 ≤ _
      have firstMax : max p.size scaled.1.trim.size ≤ width := by omega
      have secondMax : max (countedDivAux fuel residual q).1.1.size term.1.trim.size ≤
          width + 1 := by omega
      rw [Nat.add_mul]
      nlinarith

/-- Include the field-normalization arithmetic surrounding long division.
Both occurrences of the inverse in `Raw.div` are charged. -/
def countedRawDiv (inverseCost : Nat) (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F × Nat :=
  let scale := q.leadingCoeff⁻¹
  let numerator := CPolynomial.Raw.C scale • p
  let denominator := CPolynomial.Raw.C scale * q
  let core := countedDivAux numerator.size numerator denominator
  (core.1.1, 2 * inverseCost +
    (countedRawMul (CPolynomial.Raw.C scale) p).2 +
    (countedRawMul (CPolynomial.Raw.C scale) q).2 + core.2)

omit [LawfulBEq F] [DecidableEq F] in
theorem countedRawDiv_value (inverseCost : Nat) (p q : CPolynomial.Raw F) :
    (countedRawDiv inverseCost p q).1 = CPolynomial.Raw.div p q := by
  simp only [countedRawDiv, countedDivAux_value, CPolynomial.Raw.div,
    CPolynomial.Raw.divByMonic, CPolynomial.Raw.divModByMonicAux]

theorem countedRawDiv_cost (inverseCost width : Nat) (p q : CPolynomial.Raw F)
    (left : p.size ≤ width) (right : q.size ≤ width) :
    (countedRawDiv inverseCost p q).2 ≤
      2 * inverseCost + 2 + 4 * width + 40 * width * (width + 1) ^ 2 := by
  let scale := q.leadingCoeff⁻¹
  have numeratorSize : (CPolynomial.Raw.C scale • p).size ≤ width := by
    rw [smul_eq_mul]
    exact (raw_constant_support scale p).trans left
  have denominatorSize := (raw_constant_support scale q).trans right
  have core := countedDivAux_cost (CPolynomial.Raw.C scale • p).size width
    (CPolynomial.Raw.C scale • p) (CPolynomial.Raw.C scale * q)
    numeratorSize denominatorSize
  have coreBudget := core.trans (Nat.mul_le_mul_right _ numeratorSize)
  have numerator := countedRawMul_cost (CPolynomial.Raw.C scale) p
  have denominator := countedRawMul_cost (CPolynomial.Raw.C scale) q
  change (countedRawMul (CPolynomial.Raw.C scale) p).2 ≤ 1 * (1 + 2 * p.size) at numerator
  change (countedRawMul (CPolynomial.Raw.C scale) q).2 ≤ 1 * (1 + 2 * q.size) at denominator
  change 2 * inverseCost + (countedRawMul (CPolynomial.Raw.C scale) p).2 +
    (countedRawMul (CPolynomial.Raw.C scale) q).2 +
    (countedDivAux (CPolynomial.Raw.C scale • p).size
      (CPolynomial.Raw.C scale • p) (CPolynomial.Raw.C scale * q)).2 ≤ _
  nlinarith

def countedDiv (inverseCost : Nat) (p q : CPolynomial F) : CPolynomial F × Nat :=
  let result := countedRawDiv inverseCost p.val q.val
  (CPolynomial.ofArray result.1, result.2)

omit [DecidableEq F] in
theorem countedDiv_value (inverseCost : Nat) (p q : CPolynomial F) :
    (countedDiv inverseCost p q).1 = p / q := by
  apply CPolynomial.ext
  simp only [countedDiv, CPolynomial.ofArray, countedRawDiv_value,
    CPolynomial.Raw.div_canonical]
  rfl

theorem countedDiv_cost (inverseCost width : Nat) (p q : CPolynomial F)
    (left : p.val.size ≤ width) (right : q.val.size ≤ width) :
    (countedDiv inverseCost p q).2 ≤
      2 * inverseCost + 2 + 4 * width + 40 * width * (width + 1) ^ 2 :=
  countedRawDiv_cost inverseCost width p.val q.val left right

omit [DecidableEq F] in
theorem add_support (p q : CPolynomial F) :
    (p + q).val.size ≤ max p.val.size q.val.size := by
  exact (CPolynomial.Raw.Trim.size_le_size _).trans_eq CPolynomial.Raw.add_size

omit [DecidableEq F] in
theorem sub_support (p q : CPolynomial F) :
    (p - q).val.size ≤ max p.val.size q.val.size := by
  change (p.val.addRaw (CPolynomial.Raw.neg q.val)).trim.size ≤ _
  exact (CPolynomial.Raw.Trim.size_le_size _).trans_eq (by
    rw [CPolynomial.Raw.add_size]; simp [CPolynomial.Raw.neg])

omit [DecidableEq F] in
theorem mul_support (p q : CPolynomial F) :
    (p * q).val.size ≤ p.val.size + q.val.size := by
  apply CPolynomial.mem_degreeLT_iff_size_le.mp
  apply CPolynomial.mem_degreeLT.mpr
  rw [CPolynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [CPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases left : p.val.size ≤ j
  · rw [CPolynomial.coeff_eq_zero_of_size_le p left, zero_mul]
  · rw [CPolynomial.coeff_eq_zero_of_size_le q (by omega), mul_zero]

omit [DecidableEq F] in
theorem constant_support (a : F) : (CPolynomial.C a).val.size ≤ 1 :=
  (CPolynomial.Raw.Trim.size_le_size _).trans_eq (by rfl)

omit [DecidableEq F] in
theorem constant_mul_support (a : F) (p : CPolynomial F) :
    (CPolynomial.C a * p).val.size ≤ p.val.size := by
  apply CPolynomial.mem_degreeLT_iff_size_le.mp
  apply CPolynomial.mem_degreeLT.mpr
  rw [CPolynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [CPolynomial.coeff_C_mul, CPolynomial.coeff_eq_zero_of_size_le p hi, mul_zero]

def countedAdd (p q : CPolynomial F) : CPolynomial F × Nat :=
  (p + q, max p.val.size q.val.size)

def countedSub (p q : CPolynomial F) : CPolynomial F × Nat :=
  (p - q, q.val.size + max p.val.size q.val.size)

def countedFieldPow (a : F) : Nat → F × Nat
  | 0 => (1, 0)
  | n + 1 =>
    let previous := countedFieldPow a n
    (previous.1 * a, previous.2 + 1)

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedFieldPow_value (a : F) (n : Nat) :
    (countedFieldPow a n).1 = a ^ n := by
  induction n with
  | zero => simp [countedFieldPow]
  | succ n ih => simp [countedFieldPow, ih, pow_succ]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedFieldPow_cost (a : F) (n : Nat) :
    (countedFieldPow a n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedFieldPow, ih]

def countedEvalFold (point : F) : List (F × Nat) → F → F × Nat
  | [], acc => (acc, 0)
  | (a, i) :: rest, acc =>
    let power := countedFieldPow point i
    let tail := countedEvalFold point rest (acc + a * power.1)
    (tail.1, power.2 + 2 + tail.2)

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedEvalFold_value (point : F) (terms : List (F × Nat)) (acc : F) :
    (countedEvalFold point terms acc).1 =
      terms.foldl (fun acc pair => acc + pair.1 * point ^ pair.2) acc := by
  induction terms generalizing acc with
  | nil => rfl
  | cons term rest ih => simp [countedEvalFold, countedFieldPow_value, ih]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedEvalFold_cost (point : F) (terms : List (F × Nat)) (acc : F)
    (width : Nat) (indices : ∀ pair ∈ terms, pair.2 < width) :
    (countedEvalFold point terms acc).2 ≤ terms.length * (width + 2) := by
  induction terms generalizing acc with
  | nil => simp [countedEvalFold]
  | cons term rest ih =>
    have head := indices term (by simp)
    have tail := ih (acc + term.1 * (countedFieldPow point term.2).1)
      (fun pair hp => indices pair (by simp [hp]))
    simp only [countedEvalFold, countedFieldPow_cost, List.length_cons, Nat.add_mul]
    omega

def countedEval (p : CPolynomial F) (point : F) : F × Nat :=
  countedEvalFold point p.val.zipIdx.toList 0

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedEval_value (p : CPolynomial F) (point : F) :
    (countedEval p point).1 = p.eval point := by
  rw [countedEval, countedEvalFold_value]
  simp only [CPolynomial.eval, Array.foldl_toList]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
theorem countedEval_cost (p : CPolynomial F) (point : F) (width : Nat)
    (support : p.val.size ≤ width) :
    (countedEval p point).2 ≤ width * (width + 2) := by
  have bound := countedEvalFold_cost point p.val.zipIdx.toList 0 width (by
    intro pair hp
    obtain ⟨i, hi, equal⟩ := List.mem_iff_getElem.mp hp
    have within : i < p.val.size := by simpa using hi
    have index : pair.2 = i := by rw [← equal]; simp
    omega)
  have bound' : (countedEval p point).2 ≤ p.val.size * (width + 2) := by
    simpa only [countedEval, Array.length_toList, Array.size_zipIdx] using bound
  exact bound'.trans (Nat.mul_le_mul_right _ support)

def countedRawMod (inverseCost : Nat) (p q : CPolynomial.Raw F) :
    CPolynomial.Raw F × Nat :=
  let scale := q.leadingCoeff⁻¹
  let numerator := CPolynomial.Raw.C scale • p
  let denominator := CPolynomial.Raw.C scale * q
  let core := countedDivAux numerator.size numerator denominator
  (core.1.2, 2 * inverseCost +
    (countedRawMul (CPolynomial.Raw.C scale) p).2 +
    (countedRawMul (CPolynomial.Raw.C scale) q).2 + core.2)

omit [LawfulBEq F] [DecidableEq F] in
theorem countedRawMod_value (inverseCost : Nat) (p q : CPolynomial.Raw F) :
    (countedRawMod inverseCost p q).1 = CPolynomial.Raw.mod p q := by
  simp only [countedRawMod, countedDivAux_value, CPolynomial.Raw.mod,
    CPolynomial.Raw.modByMonic, CPolynomial.Raw.divModByMonicAux]

def countedMod (inverseCost : Nat) (p q : CPolynomial F) : CPolynomial F × Nat :=
  let result := countedRawMod inverseCost p.val q.val
  (CPolynomial.ofArray result.1, result.2)

omit [DecidableEq F] in
theorem countedMod_value (inverseCost : Nat) (p q : CPolynomial F) :
    (countedMod inverseCost p q).1 = p.mod q := by
  apply CPolynomial.ext
  simp only [countedMod, CPolynomial.ofArray, countedRawMod_value,
    CPolynomial.Raw.mod_canonical]
  rfl

theorem countedMod_cost (inverseCost width : Nat) (p q : CPolynomial F)
    (left : p.val.size ≤ width) (right : q.val.size ≤ width) :
    (countedMod inverseCost p q).2 ≤
      2 * inverseCost + 2 + 4 * width + 40 * width * (width + 1) ^ 2 :=
  countedDiv_cost inverseCost width p q left right

theorem div_support (p q : CPolynomial F) (width : Nat) (support : p.val.size ≤ width) :
    (p / q).val.size ≤ width + 1 := by
  let scale := q.val.leadingCoeff⁻¹
  have numeratorSize : (CPolynomial.Raw.C scale • p.val).size ≤ width := by
    rw [smul_eq_mul]
    exact (raw_constant_support scale p.val).trans support
  have core := countedDivAux_quotient_support
    (CPolynomial.Raw.C scale • p.val).size width
    (CPolynomial.Raw.C scale • p.val) (CPolynomial.Raw.C scale * q.val) numeratorSize
  rw [countedDivAux_value] at core
  exact core

omit [DecidableEq F] in
/-- Actual Euclidean remainder drop, independently of the fuel counter. -/
theorem remainder_drop (previous r : CPolynomial F) (nonzero : r ≠ 0) :
    (previous - (previous / r) * r).val.size < r.val.size := by
  have degree : (previous - (previous / r) * r).degree < r.degree := by
    rw [CPolynomial.degree_toPoly, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
      show previous / r = previous.div r from rfl, CPolynomial.div_toPoly_eq_div,
      mul_comm, ← EuclideanDomain.mod_eq_sub_mul_div]
    simpa only [CPolynomial.degree_toPoly] using
      Polynomial.degree_mod_lt previous.toPoly ((CPolynomial.toPoly_eq_zero_iff r).not.mpr nonzero)
  have positive : 0 < r.val.size := by
    by_contra zero
    have empty : r = 0 := CPolynomial.ext (Array.eq_empty_of_size_eq_zero (by omega))
    exact nonzero empty
  have naturalDegree : r.degree = (r.val.size - 1 : Nat) := by
    cases size : r.val.size with
    | zero => omega
    | succ n => simp [CPolynomial.degree, size]
  have bound := CPolynomial.mem_degreeLT_iff_size_le.mp
    (CPolynomial.mem_degreeLT.mpr (naturalDegree ▸ degree))
  omega

def xgcdStepBudget (inverseCost width : Nat) : Nat :=
  2 * inverseCost + 2 + 16 * width + 9 * width ^ 2 +
    40 * width * (width + 1) ^ 2

/-- Coefficient-arithmetic execution of the actual partial Euclidean loop.
This instruments each division, convolution and coefficient subtraction;
it does not count a polynomial operation as a constant-time field operation. -/
def countedXgcdFieldAux (inverseCost threshold : Nat) : Nat →
    CPolynomial F → CPolynomial F → CPolynomial F →
    CPolynomial F → CPolynomial F → CPolynomial F →
    (CPolynomial F × CPolynomial F × CPolynomial F) × Nat
  | 0, _, _, _, previous, sPrevious, tPrevious => ((previous, sPrevious, tPrevious), 0)
  | fuel + 1, r, s, t, previous, sPrevious, tPrevious =>
    if r.natDegree < threshold then ((r, s, t), 0)
    else if r == 0 then ((previous, sPrevious, tPrevious), 0)
    else
      let division := countedDiv inverseCost previous r
      let qr := countedMul division.1 r
      let qs := countedMul division.1 s
      let qt := countedMul division.1 t
      let residual := countedSub previous qr.1
      let nextS := countedSub sPrevious qs.1
      let nextT := countedSub tPrevious qt.1
      let tail := countedXgcdFieldAux inverseCost threshold fuel
        residual.1 nextS.1 nextT.1 r s t
      (tail.1, division.2 + qr.2 + qs.2 + qt.2 +
        residual.2 + nextS.2 + nextT.2 + tail.2)

omit [DecidableEq F] in
theorem countedXgcdFieldAux_value (inverseCost threshold fuel : Nat)
    (r s t previous sPrevious tPrevious : CPolynomial F) :
    (countedXgcdFieldAux inverseCost threshold fuel r s t previous sPrevious tPrevious).1 =
      CPolynomial.xgcdAux threshold fuel r s t previous sPrevious tPrevious := by
  induction fuel generalizing r s t previous sPrevious tPrevious with
  | zero => rfl
  | succ fuel ih =>
    simp only [countedXgcdFieldAux, CPolynomial.xgcdAux]
    split_ifs <;> simp [countedSub, countedDiv_value, countedMul_value, ih]

set_option maxHeartbeats 1600000 in
/-- A polynomial support bound derived along the actual Euclidean execution.
Residues strictly shrink; quotient support is at most `residueWidth+1`.
Thus cofactors grow by at most that many coefficients per fueled step.
No hypothesis bounds an unobserved trace or assumes a desired resource count. -/
theorem countedXgcdFieldAux_cost (inverseCost threshold fuel residueWidth cofactorWidth : Nat)
    (r s t previous sPrevious tPrevious : CPolynomial F)
    (rSupport : r.val.size ≤ residueWidth) (previousSupport : previous.val.size ≤ residueWidth)
    (sSupport : s.val.size ≤ cofactorWidth) (tSupport : t.val.size ≤ cofactorWidth)
    (sPreviousSupport : sPrevious.val.size ≤ cofactorWidth)
    (tPreviousSupport : tPrevious.val.size ≤ cofactorWidth) :
    (countedXgcdFieldAux inverseCost threshold fuel r s t previous sPrevious tPrevious).2 ≤
      fuel * xgcdStepBudget inverseCost
        (residueWidth + cofactorWidth + fuel * (residueWidth + 1)) := by
  induction fuel generalizing cofactorWidth r s t previous sPrevious tPrevious with
  | zero => simp [countedXgcdFieldAux]
  | succ fuel ih =>
    by_cases stop : r.natDegree < threshold
    · simp [countedXgcdFieldAux, stop]
    by_cases zero : r == 0
    · simp [countedXgcdFieldAux, stop, zero]
    have nonzero : r ≠ 0 := by simpa only [beq_iff_eq] using zero
    let quotient := previous / r
    let width := residueWidth + cofactorWidth + (fuel + 1) * (residueWidth + 1)
    let nextCofactorWidth := cofactorWidth + residueWidth + 1
    have qSupport : quotient.val.size ≤ residueWidth + 1 := div_support previous r _ previousSupport
    have residualSupport : (previous - quotient * r).val.size ≤ residueWidth :=
      (remainder_drop previous r nonzero).le.trans rSupport
    have nextSSupport : (sPrevious - quotient * s).val.size ≤ nextCofactorWidth := by
      exact (sub_support _ _).trans (max_le (by dsimp [nextCofactorWidth]; omega)
        ((mul_support _ _).trans (by dsimp [nextCofactorWidth]; omega)))
    have nextTSupport : (tPrevious - quotient * t).val.size ≤ nextCofactorWidth := by
      exact (sub_support _ _).trans (max_le (by dsimp [nextCofactorWidth]; omega)
        ((mul_support _ _).trans (by dsimp [nextCofactorWidth]; omega)))
    have nextSPrevious : s.val.size ≤ nextCofactorWidth := by dsimp [nextCofactorWidth]; omega
    have nextTPrevious : t.val.size ≤ nextCofactorWidth := by dsimp [nextCofactorWidth]; omega
    have tail := ih nextCofactorWidth (previous - quotient * r)
      (sPrevious - quotient * s) (tPrevious - quotient * t) r s t
      residualSupport rSupport nextSSupport nextTSupport nextSPrevious nextTPrevious
    have sameWidth : residueWidth + nextCofactorWidth + fuel * (residueWidth + 1) = width := by
      dsimp [nextCofactorWidth, width]; ring
    rw [sameWidth] at tail
    have rW : r.val.size ≤ width := by dsimp [width]; omega
    have previousW : previous.val.size ≤ width := by dsimp [width]; omega
    have qW : quotient.val.size ≤ width := by dsimp [width]; omega
    have sW : s.val.size ≤ width := by dsimp [width]; omega
    have tW : t.val.size ≤ width := by dsimp [width]; omega
    have sPreviousW : sPrevious.val.size ≤ width := by dsimp [width]; omega
    have tPreviousW : tPrevious.val.size ≤ width := by dsimp [width]; omega
    have divCost := countedDiv_cost inverseCost width previous r previousW rW
    have qrCost := countedMul_cost quotient r width qW rW
    have qsCost := countedMul_cost quotient s width qW sW
    have qtCost := countedMul_cost quotient t width qW tW
    have qrSupport : (quotient * r).val.size ≤ 2 * width :=
      (mul_support _ _).trans (by omega)
    have qsSupport : (quotient * s).val.size ≤ 2 * width :=
      (mul_support _ _).trans (by omega)
    have qtSupport : (quotient * t).val.size ≤ 2 * width :=
      (mul_support _ _).trans (by omega)
    simp only [countedXgcdFieldAux, stop, zero, ↓reduceIte, countedSub,
      countedDiv_value, countedMul_value]
    change (countedDiv inverseCost previous r).2 +
      (countedMul quotient r).2 + (countedMul quotient s).2 + (countedMul quotient t).2 +
      ((quotient * r).val.size + max previous.val.size (quotient * r).val.size) +
      ((quotient * s).val.size + max sPrevious.val.size (quotient * s).val.size) +
      ((quotient * t).val.size + max tPrevious.val.size (quotient * t).val.size) +
      (countedXgcdFieldAux inverseCost threshold fuel (previous - quotient * r)
        (sPrevious - quotient * s) (tPrevious - quotient * t) r s t).2 ≤ _
    have maxR : max previous.val.size (quotient * r).val.size ≤ 2 * width := by omega
    have maxS : max sPrevious.val.size (quotient * s).val.size ≤ 2 * width := by omega
    have maxT : max tPrevious.val.size (quotient * t).val.size ≤ 2 * width := by omega
    change _ ≤ (fuel + 1) * xgcdStepBudget inverseCost width
    rw [Nat.add_mul]
    unfold xgcdStepBudget at *
    omega

def countedXgcd (inverseCost threshold : Nat) (p q : CPolynomial F) :
    (CPolynomial F × CPolynomial F × CPolynomial F) × Nat :=
  countedXgcdFieldAux inverseCost threshold p.val.size p 1 0 q 0 1

omit [DecidableEq F] in
theorem countedXgcd_value (inverseCost threshold : Nat) (p q : CPolynomial F) :
    (countedXgcd inverseCost threshold p q).1 = CPolynomial.xgcd p q threshold :=
  countedXgcdFieldAux_value inverseCost threshold p.val.size p 1 0 q 0 1

theorem countedXgcd_cost (inverseCost threshold width : Nat) (p q : CPolynomial F)
    (left : p.val.size ≤ width) (right : q.val.size ≤ width) :
    (countedXgcd inverseCost threshold p q).2 ≤ p.val.size *
      xgcdStepBudget inverseCost (width + 1 + p.val.size * (width + 1)) := by
  apply countedXgcdFieldAux_cost inverseCost threshold p.val.size width 1
    p 1 0 q 0 1 left right <;> first | exact Nat.le_refl 1 | exact Nat.zero_le 1

def countedProduct : List (CPolynomial F × Nat) → CPolynomial F × Nat
  | [] => (1, 0)
  | term :: rest =>
    let tail := countedProduct rest
    let product := countedMul term.1 tail.1
    (product.1, term.2 + tail.2 + product.2)

omit [DecidableEq F] in
theorem countedProduct_value (terms : List (CPolynomial F × Nat)) :
    (countedProduct terms).1 = (terms.map Prod.fst).prod := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [countedProduct, countedMul_value, ih]

omit [DecidableEq F] in
theorem countedProduct_support (terms : List (CPolynomial F × Nat))
    (supports : ∀ term ∈ terms, term.1.val.size ≤ 2) :
    (countedProduct terms).1.val.size ≤ 2 * terms.length + 1 := by
  induction terms with
  | nil => exact Nat.le_refl 1
  | cons term rest ih =>
    have head := supports term (by simp)
    have tail := ih (fun term hp => supports term (by simp [hp]))
    rw [show (countedProduct (term :: rest)).1 = term.1 * (countedProduct rest).1 from
      by simp [countedProduct, countedMul_value]]
    exact (mul_support _ _).trans (by simp only [List.length_cons]; omega)

omit [DecidableEq F] in
theorem countedProduct_cost (terms : List (CPolynomial F × Nat)) (width termBudget : Nat)
    (length : terms.length ≤ width)
    (supports : ∀ term ∈ terms, term.1.val.size ≤ 2)
    (costs : ∀ term ∈ terms, term.2 ≤ termBudget) :
    (countedProduct terms).2 ≤ terms.length * (termBudget + 3 * (2 * width + 1) ^ 2) := by
  induction terms with
  | nil => simp [countedProduct]
  | cons term rest ih =>
    have headSupport := supports term (by simp)
    have headCost := costs term (by simp)
    have tailSupports : ∀ item ∈ rest, item.1.val.size ≤ 2 := by
      intro item hp; exact supports item (by simp [hp])
    have tail := ih (by simp only [List.length_cons] at length; omega)
      tailSupports (fun term hp => costs term (by simp [hp]))
    have tailSupport := countedProduct_support rest tailSupports
    have product := countedMul_cost term.1 (countedProduct rest).1 (2 * width + 1)
      (by simp only [List.length_cons] at length; omega)
      (by simp only [List.length_cons] at length; omega)
    simp only [countedProduct, List.length_cons, Nat.add_mul]
    omega

def countedSum : List (CPolynomial F × Nat) → CPolynomial F × Nat
  | [] => (0, 0)
  | term :: rest =>
    let tail := countedSum rest
    let sum := countedAdd term.1 tail.1
    (sum.1, term.2 + tail.2 + sum.2)

omit [DecidableEq F] in
theorem countedSum_value (terms : List (CPolynomial F × Nat)) :
    (countedSum terms).1 = (terms.map Prod.fst).sum := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [countedSum, countedAdd, ih]

omit [DecidableEq F] in
theorem countedSum_support (terms : List (CPolynomial F × Nat)) (width : Nat)
    (supports : ∀ term ∈ terms, term.1.val.size ≤ width) :
    (countedSum terms).1.val.size ≤ width := by
  induction terms with
  | nil => exact Nat.zero_le width
  | cons term rest ih =>
    exact (add_support _ _).trans (max_le (supports term (by simp))
      (ih (fun term hp => supports term (by simp [hp]))))

omit [DecidableEq F] in
theorem countedSum_cost (terms : List (CPolynomial F × Nat)) (width termBudget : Nat)
    (supports : ∀ term ∈ terms, term.1.val.size ≤ width)
    (costs : ∀ term ∈ terms, term.2 ≤ termBudget) :
    (countedSum terms).2 ≤ terms.length * (termBudget + width) := by
  induction terms with
  | nil => simp [countedSum]
  | cons term rest ih =>
    have headSupport := supports term (by simp)
    have headCost := costs term (by simp)
    have tailSupports : ∀ item ∈ rest, item.1.val.size ≤ width := by
      intro item hp; exact supports item (by simp [hp])
    have tailSupport := countedSum_support rest width tailSupports
    have tail := ih tailSupports (fun term hp => costs term (by simp [hp]))
    simp only [countedSum, countedAdd, List.length_cons, Nat.add_mul]
    omega

def countedBasisFactor (inverseCost : Nat) (node other : F) : CPolynomial F × Nat :=
  let difference := node - other
  let linear := countedSub CPolynomial.X (CPolynomial.C other)
  let product := countedMul (CPolynomial.C difference⁻¹) linear.1
  (product.1, 1 + inverseCost + linear.2 + product.2)

omit [DecidableEq F] in
theorem countedBasisFactor_value (inverseCost : Nat) (node other : F) :
    (countedBasisFactor inverseCost node other).1 = CPolynomial.CLagrange.basisDivisor node other := by
  simp [countedBasisFactor, countedSub, countedMul_value, CPolynomial.CLagrange.basisDivisor]

omit [DecidableEq F] in
theorem countedBasisFactor_support (inverseCost : Nat) (node other : F) :
    (countedBasisFactor inverseCost node other).1.val.size ≤ 2 := by
  rw [countedBasisFactor_value]
  exact (constant_mul_support _ _).trans ((sub_support _ _).trans
    (max_le (Nat.le_refl 2) ((constant_support other).trans (by omega))))

omit [DecidableEq F] in
theorem countedBasisFactor_cost (inverseCost : Nat) (node other : F) :
    (countedBasisFactor inverseCost node other).2 ≤ inverseCost + 9 := by
  have c := constant_support other
  have factorSupport : (CPolynomial.X - CPolynomial.C other).val.size ≤ 2 :=
    (sub_support _ _).trans (max_le (Nat.le_refl 2) (c.trans (by omega)))
  have scalar := constant_support (node - other)⁻¹
  have product := countedRawMul_cost (CPolynomial.C (node - other)⁻¹).val
    (CPolynomial.X - CPolynomial.C other).val
  have productBudget : (countedMul (CPolynomial.C (node - other)⁻¹)
      (CPolynomial.X - CPolynomial.C other)).2 ≤ 5 := by
    exact product.trans (by
      calc
        _ ≤ 1 * (1 + 2 * 2) :=
          Nat.mul_le_mul scalar (Nat.add_le_add scalar (Nat.mul_le_mul_left 2 factorSupport))
        _ = 5 := rfl)
  change 1 + inverseCost + ((CPolynomial.C other).val.size +
    max CPolynomial.X.val.size (CPolynomial.C other).val.size) +
    (countedMul (CPolynomial.C (node - other)⁻¹)
      (CPolynomial.X - CPolynomial.C other)).2 ≤ _
  rw [show (CPolynomial.X : CPolynomial F).val.size = 2 from rfl]
  omega

def basisIndices (n : Nat) (i : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun j => j ≠ i)

def countedBasis (inverseCost : Nat) (n : Nat) (nodes : Fin n → F) (i : Fin n) :
    CPolynomial F × Nat :=
  countedProduct ((basisIndices n i).map (fun j => countedBasisFactor inverseCost (nodes i) (nodes j)))

omit [DecidableEq F] in
theorem countedBasis_value (inverseCost n : Nat) (nodes : Fin n → F) (i : Fin n) :
    (countedBasis inverseCost n nodes i).1 =
      CPolynomial.CLagrange.basis Finset.univ nodes i := by
  apply CPolynomial.toPolyLinearEquiv.injective
  simp only [CPolynomial.toPolyLinearEquiv_apply, countedBasis, countedProduct_value,
    List.map_map, Function.comp_def, countedBasisFactor_value]
  have enumeration : (basisIndices n i).toFinset = Finset.univ.erase i := by
    ext j; simp [basisIndices]
  have nodup : (basisIndices n i).Nodup := (List.nodup_finRange n).filter _
  rw [← List.prod_toFinset _ nodup, enumeration, CPolynomial.toPoly_prod,
    CPolynomial.CLagrange.cbasis_eq_basis, Lagrange.basis]
  simp [CPolynomial.CLagrange.cbasisDivisor_eq_basisDivisor]

omit [DecidableEq F] in
theorem countedBasis_support (inverseCost n : Nat) (nodes : Fin n → F) (i : Fin n) :
    (countedBasis inverseCost n nodes i).1.val.size ≤ 2 * n + 1 := by
  have length : (basisIndices n i).length ≤ n :=
    (List.length_filter_le _ _).trans_eq List.length_finRange
  exact (countedProduct_support _ (by
    intro term ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
    exact countedBasisFactor_support _ _ _)).trans (by simp; omega)

omit [DecidableEq F] in
theorem countedBasis_cost (inverseCost n : Nat) (nodes : Fin n → F) (i : Fin n) :
    (countedBasis inverseCost n nodes i).2 ≤ n * (inverseCost + 9 + 3 * (2 * n + 1) ^ 2) := by
  have length : (basisIndices n i).length ≤ n :=
    (List.length_filter_le _ _).trans_eq List.length_finRange
  have bound := countedProduct_cost
    ((basisIndices n i).map (fun j => countedBasisFactor inverseCost (nodes i) (nodes j)))
    n (inverseCost + 9) (by simpa using length)
    (by intro term ht; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht; exact countedBasisFactor_support _ _ _)
    (by intro term ht; obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht; exact countedBasisFactor_cost _ _ _)
  exact bound.trans (Nat.mul_le_mul_right _ (by simpa using length))

def countedInterpolant (inverseCost : Nat) (D : Domain (F := F)) (received : Vector F D.n) :
    CPolynomial F × Nat :=
  countedSum ((List.finRange D.n).map fun i =>
    let basis := countedBasis inverseCost D.n (D.val[·]) i
    let term := countedMul (CPolynomial.C (received.get i)) basis.1
    (term.1, basis.2 + term.2))

omit [DecidableEq F] in
theorem countedInterpolant_value (inverseCost : Nat) (D : Domain (F := F))
    (received : Vector F D.n) :
    (countedInterpolant inverseCost D received).1 =
      CompPoly.ReedSolomon.Gao.receivedInterpolant D received := by
  apply CPolynomial.toPolyLinearEquiv.injective
  rw [CPolynomial.toPolyLinearEquiv_apply, CPolynomial.toPolyLinearEquiv_apply,
    countedInterpolant, countedSum_value]
  simp only [List.map_map, countedMul_value, countedBasis_value]
  rw [← List.sum_toFinset _ (List.nodup_finRange _)]
  simp only [List.toFinset_finRange]
  rw [CompPoly.ReedSolomon.Gao.receivedInterpolant,
    CPolynomial.CLagrange.cinterpolate_eq_interpolate, Lagrange.interpolate]
  simp [CPolynomial.toPoly_sum, CPolynomial.toPoly_mul, CPolynomial.C_toPoly,
    CPolynomial.CLagrange.cbasis_eq_basis]

def interpolationBudget (inverseCost n : Nat) : Nat :=
  n * (n * (inverseCost + 9 + 3 * (2 * n + 1) ^ 2) +
    3 * (2 * n + 1) ^ 2 + (2 * n + 1))

omit [DecidableEq F] in
theorem countedInterpolant_support (inverseCost : Nat) (D : Domain (F := F))
    (received : Vector F D.n) :
    (countedInterpolant inverseCost D received).1.val.size ≤ 2 * D.n + 1 := by
  apply countedSum_support
  intro term ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
  rw [countedMul_value]
  exact (constant_mul_support _ _).trans (countedBasis_support _ _ _ _)

omit [DecidableEq F] in
theorem countedInterpolant_cost (inverseCost : Nat) (D : Domain (F := F))
    (received : Vector F D.n) :
    (countedInterpolant inverseCost D received).2 ≤ interpolationBudget inverseCost D.n := by
  unfold countedInterpolant interpolationBudget
  have bound := countedSum_cost
    ((List.finRange D.n).map fun i =>
      let basis := countedBasis inverseCost D.n (D.val[·]) i
      let term := countedMul (CPolynomial.C (received.get i)) basis.1
      (term.1, basis.2 + term.2))
    (2 * D.n + 1)
    (D.n * (inverseCost + 9 + 3 * (2 * D.n + 1) ^ 2) + 3 * (2 * D.n + 1) ^ 2)
    (by
      intro term ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      rw [countedMul_value]
      exact (constant_mul_support _ _).trans (countedBasis_support _ _ _ _))
    (by
      intro term ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact Nat.add_le_add (countedBasis_cost _ _ _ _)
        (countedMul_cost _ _ _ ((constant_support _).trans (by omega))
          (countedBasis_support _ _ _ _)))
  simpa only [List.length_map, List.length_finRange] using bound

def countedNodal (D : Domain (F := F)) : CPolynomial F × Nat :=
  countedProduct (D.val.toList.map fun node => countedSub CPolynomial.X (CPolynomial.C node))

omit [DecidableEq F] in
theorem countedNodal_value (D : Domain (F := F)) :
    (countedNodal D).1 = CompPoly.ReedSolomon.Gao.nodalPoly D := by
  rw [countedNodal, countedProduct_value]
  simp only [List.map_map, Function.comp_def, countedSub]
  rw [CompPoly.ReedSolomon.Gao.nodalPoly, ← Array.foldl_toList,
    ← List.foldl_map (f := fun node => CPolynomial.X - CPolynomial.C node) (g := (· * ·)),
    ← List.prod_eq_foldl]

omit [DecidableEq F] in
theorem countedNodal_support (D : Domain (F := F)) :
    (countedNodal D).1.val.size ≤ 2 * D.n + 1 := by
  have bound := countedProduct_support
    (D.val.toList.map fun node => countedSub CPolynomial.X (CPolynomial.C node)) (by
      intro term ht
      obtain ⟨node, hn, rfl⟩ := List.mem_map.mp ht
      exact (sub_support _ _).trans (max_le (Nat.le_refl 2)
        ((constant_support node).trans (by omega))))
  simpa only [countedNodal, List.length_map, Array.length_toList,
    CompPoly.ReedSolomon.Domain.n] using bound

omit [DecidableEq F] in
theorem countedNodal_cost (D : Domain (F := F)) :
    (countedNodal D).2 ≤ D.n * (3 + 3 * (2 * D.n + 1) ^ 2) := by
  have bound := countedProduct_cost
    (D.val.toList.map fun node => countedSub CPolynomial.X (CPolynomial.C node))
    D.n 3 (by simp [CompPoly.ReedSolomon.Domain.n])
    (by
      intro term ht
      obtain ⟨node, hn, rfl⟩ := List.mem_map.mp ht
      exact (sub_support _ _).trans (max_le (Nat.le_refl 2)
        ((constant_support node).trans (by omega))))
    (by
      intro term ht
      obtain ⟨node, hn, rfl⟩ := List.mem_map.mp ht
      have support := constant_support node
      change (CPolynomial.C node).val.size + max 2 (CPolynomial.C node).val.size ≤ 3
      omega)
  simpa only [countedNodal, List.length_map, Array.length_toList,
    CompPoly.ReedSolomon.Domain.n] using bound

theorem xgcdAux_support (threshold fuel residueWidth cofactorWidth : Nat)
    (r s t previous sPrevious tPrevious : CPolynomial F)
    (rSupport : r.val.size ≤ residueWidth) (previousSupport : previous.val.size ≤ residueWidth)
    (sSupport : s.val.size ≤ cofactorWidth) (tSupport : t.val.size ≤ cofactorWidth)
    (sPreviousSupport : sPrevious.val.size ≤ cofactorWidth)
    (tPreviousSupport : tPrevious.val.size ≤ cofactorWidth) :
    let result := CPolynomial.xgcdAux threshold fuel r s t previous sPrevious tPrevious
    result.1.val.size ≤ residueWidth ∧
      result.2.1.val.size ≤ cofactorWidth + fuel * (residueWidth + 1) ∧
      result.2.2.val.size ≤ cofactorWidth + fuel * (residueWidth + 1) := by
  induction fuel generalizing cofactorWidth r s t previous sPrevious tPrevious with
  | zero => simpa [CPolynomial.xgcdAux] using ⟨previousSupport, sPreviousSupport, tPreviousSupport⟩
  | succ fuel ih =>
    simp only [CPolynomial.xgcdAux]
    split_ifs with stop zero
    · exact ⟨rSupport, sSupport.trans (by omega), tSupport.trans (by omega)⟩
    · exact ⟨previousSupport, sPreviousSupport.trans (by omega), tPreviousSupport.trans (by omega)⟩
    · have nonzero : r ≠ 0 := by simpa only [beq_iff_eq] using zero
      let quotient := previous / r
      have qSupport : quotient.val.size ≤ residueWidth + 1 := div_support previous r _ previousSupport
      have residualSupport : (previous - quotient * r).val.size ≤ residueWidth :=
        (remainder_drop previous r nonzero).le.trans rSupport
      have nextSSupport : (sPrevious - quotient * s).val.size ≤ cofactorWidth + residueWidth + 1 :=
        (sub_support _ _).trans (max_le (sPreviousSupport.trans (by omega))
          ((mul_support _ _).trans (by omega)))
      have nextTSupport : (tPrevious - quotient * t).val.size ≤ cofactorWidth + residueWidth + 1 :=
        (sub_support _ _).trans (max_le (tPreviousSupport.trans (by omega))
          ((mul_support _ _).trans (by omega)))
      have result := ih (cofactorWidth + residueWidth + 1) (previous - quotient * r)
        (sPrevious - quotient * s) (tPrevious - quotient * t) r s t
        residualSupport rSupport nextSSupport nextTSupport
        (sSupport.trans (by omega)) (tSupport.trans (by omega))
      have equal : cofactorWidth + residueWidth + 1 + fuel * (residueWidth + 1) =
          cofactorWidth + (fuel + 1) * (residueWidth + 1) := by ring
      simpa only [equal] using result

def decoderWidth (n : Nat) : Nat :=
  (2 * n + 1) + 1 + (2 * n + 1) * ((2 * n + 1) + 1)

def divisionBudget (inverseCost width : Nat) : Nat :=
  2 * inverseCost + 2 + 4 * width + 40 * width * (width + 1) ^ 2

def decoderBudget (inverseCost n : Nat) : Nat :=
  n * (3 + 3 * (2 * n + 1) ^ 2) + interpolationBudget inverseCost n +
    (2 * n + 1) * xgcdStepBudget inverseCost (decoderWidth n) +
    2 * divisionBudget inverseCost (decoderWidth n)

theorem xgcdStepBudget_mono (inverseCost : Nat) {a b : Nat} (bound : a ≤ b) :
    xgcdStepBudget inverseCost a ≤ xgcdStepBudget inverseCost b := by
  unfold xgcdStepBudget
  gcongr

/-- Complete coefficient-arithmetic instrumentation of Gao: nodal product,
Lagrange interpolation, partial xgcd and both final remainder/division calls.
The public-domain array construction itself uses no field arithmetic. -/
def countedDecode (inverseCost k : Nat) (D : Domain (F := F)) (received : Vector F D.n) :
    Option (CPolynomial F) × Nat :=
  let nodal := countedNodal D
  let interpolant := countedInterpolant inverseCost D received
  let gcd := countedXgcd inverseCost ((D.n + k + 1) / 2) nodal.1 interpolant.1
  let remainder := countedMod inverseCost gcd.1.1 gcd.1.2.2
  let cost := nodal.2 + interpolant.2 + gcd.2 + remainder.2
  if remainder.1 == 0 then
    let quotient := countedDiv inverseCost gcd.1.1 gcd.1.2.2
    (if quotient.1.degree < k then some quotient.1 else none, cost + quotient.2)
  else (none, cost)

omit [DecidableEq F] in
theorem countedDecode_value (inverseCost k : Nat) (D : Domain (F := F))
    (received : Vector F D.n) :
    (countedDecode inverseCost k D received).1 = decode k D received := by
  simp only [countedDecode, countedNodal_value, countedInterpolant_value, countedXgcd_value,
    countedMod_value, countedDiv_value, decode, CompPoly.ReedSolomon.Gao.decode,
    CompPoly.ReedSolomon.Gao.partialGcd]
  split_ifs <;> simp_all
  all_goals simp_all only [← not_lt, ite_false]

set_option maxHeartbeats 1600000 in
theorem countedDecode_cost (inverseCost k : Nat) (D : Domain (F := F))
    (received : Vector F D.n) :
    (countedDecode inverseCost k D received).2 ≤ decoderBudget inverseCost D.n := by
  let nodal := countedNodal D
  let interpolant := countedInterpolant inverseCost D received
  let threshold := (D.n + k + 1) / 2
  let gcd := countedXgcd inverseCost threshold nodal.1 interpolant.1
  let residueWidth := 2 * D.n + 1
  have nodalSupport : nodal.1.val.size ≤ residueWidth := countedNodal_support D
  have interpolantSupport : interpolant.1.val.size ≤ residueWidth :=
    countedInterpolant_support inverseCost D received
  have gcdCost := countedXgcd_cost inverseCost threshold residueWidth
    nodal.1 interpolant.1 nodalSupport interpolantSupport
  have gcdBudget : gcd.2 ≤ residueWidth * xgcdStepBudget inverseCost (decoderWidth D.n) := by
    exact gcdCost.trans (Nat.mul_le_mul nodalSupport
      (xgcdStepBudget_mono inverseCost (by
        unfold decoderWidth; dsimp only [residueWidth]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ nodalSupport) _)))
  have output := xgcdAux_support threshold nodal.1.val.size residueWidth 1
    nodal.1 1 0 interpolant.1 0 1 nodalSupport interpolantSupport
    (Nat.le_refl 1) (Nat.zero_le 1) (Nat.zero_le 1) (Nat.le_refl 1)
  have outputValue : gcd.1 = CPolynomial.xgcdAux threshold nodal.1.val.size
      nodal.1 1 0 interpolant.1 0 1 := countedXgcd_value _ _ _ _
  have rSupport : gcd.1.1.val.size ≤ decoderWidth D.n := by
    rw [outputValue]
    exact output.1.trans (by unfold decoderWidth; dsimp [residueWidth]; omega)
  have tSupport : gcd.1.2.2.val.size ≤ decoderWidth D.n := by
    rw [outputValue]
    exact output.2.2.trans (by
      change 1 + nodal.1.val.size * (residueWidth + 1) ≤
        residueWidth + 1 + residueWidth * (residueWidth + 1)
      exact Nat.add_le_add (by omega) (Nat.mul_le_mul_right _ nodalSupport))
  have remainderCost := countedMod_cost inverseCost (decoderWidth D.n)
    gcd.1.1 gcd.1.2.2 rSupport tSupport
  have quotientCost := countedDiv_cost inverseCost (decoderWidth D.n)
    gcd.1.1 gcd.1.2.2 rSupport tSupport
  have nodalCost := countedNodal_cost D
  have interpolantCost := countedInterpolant_cost inverseCost D received
  unfold countedDecode
  change (if (countedMod inverseCost gcd.1.1 gcd.1.2.2).1 == 0 then
    (if (countedDiv inverseCost gcd.1.1 gcd.1.2.2).1.degree < k then
      some (countedDiv inverseCost gcd.1.1 gcd.1.2.2).1 else none,
      nodal.2 + interpolant.2 + gcd.2 + (countedMod inverseCost gcd.1.1 gcd.1.2.2).2 +
        (countedDiv inverseCost gcd.1.1 gcd.1.2.2).2)
    else (none, nodal.2 + interpolant.2 + gcd.2 +
      (countedMod inverseCost gcd.1.1 gcd.1.2.2).2)).2 ≤ _
  split_ifs <;> simp only
  all_goals
    unfold decoderBudget divisionBudget
    change nodal.2 ≤ _ at nodalCost
    change interpolant.2 ≤ _ at interpolantCost
    dsimp only [residueWidth] at gcdBudget
    omega

end Whir.ReedSolomonExtraction
