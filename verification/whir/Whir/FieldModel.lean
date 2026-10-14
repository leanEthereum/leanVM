import Whir.FieldCardinality
import Mathlib

/-! Polynomial representations of the actual machine words.  The coefficient
map uses XOR, not the native modular-integer addition on `UInt64`.  Quotients
are kept separate from machine types; no field instance on `UInt64` is used. -/
namespace Whir.FieldModel
open Concrete Polynomial
open scoped BigOperators

noncomputable section
abbrev F₂ := ZMod 2

/-- Least-significant-bit-first polynomial representation. -/
def bitPoly {n : Nat} (a : BitVec n) : F₂[X] :=
  ∑ i ∈ Finset.range n, monomial i (if a.getLsbD i then 1 else 0)

@[simp] theorem coeff_bitPoly {n : Nat} (a : BitVec n) (i : Nat) :
    (bitPoly a).coeff i = if a.getLsbD i then 1 else 0 := by
  classical
  by_cases hi : i < n
  · simp [bitPoly, coeff_monomial, hi]
  · simp [bitPoly, coeff_monomial, hi,
      BitVec.getLsbD_of_ge a i (by omega : n ≤ i)]

@[simp] theorem bitPoly_zero (n : Nat) : bitPoly (0 : BitVec n) = 0 := by
  ext i
  simp

@[simp] theorem bitPoly_xor {n : Nat} (a b : BitVec n) :
    bitPoly (a ^^^ b) = bitPoly a + bitPoly b := by
  ext i
  simp only [coeff_bitPoly, coeff_add, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> decide

theorem bitPoly_injective {n : Nat} : Function.Injective (@bitPoly n) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  have hc := congrArg (fun p : F₂[X] => p.coeff i) h
  simp only [coeff_bitPoly] at hc
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> simp_all

/-- The polynomial whose residue class represents an actual base-field word. -/
def wordPoly (a : K) : F₂[X] := bitPoly a.toBitVec

@[simp] theorem wordPoly_kadd (a b : K) :
    wordPoly (kadd a b) = wordPoly a + wordPoly b :=
  bitPoly_xor _ _

@[simp] theorem wordPoly_xor (a b : K) :
    wordPoly (a ^^^ b) = wordPoly a + wordPoly b := wordPoly_kadd a b

@[simp] theorem wordPoly_zero : wordPoly 0 = 0 := bitPoly_zero 64

theorem wordPoly_injective : Function.Injective wordPoly := by
  intro a b h
  exact UInt64.toBitVec_inj.mp (bitPoly_injective h)

theorem bitPoly_shiftRight_one {n : Nat} (a : BitVec n) :
    bitPoly a = C (if a.getLsbD 0 then (1 : F₂) else 0) + X * bitPoly (a >>> 1) := by
  ext i
  cases i with
  | zero => cases h : a.getLsbD 0 <;> simp [h]
  | succ i => cases a.getLsbD 0 <;> simp [coeff_one, Nat.add_comm]

theorem bitPoly_shiftLeft_one {n : Nat} (a : BitVec (n+1)) :
    bitPoly (a <<< 1) =
      X * bitPoly a + monomial (n+1) (if a.getLsbD n then 1 else 0) := by
  ext i
  cases i with
  | zero => simp [coeff_monomial]
  | succ i =>
    by_cases hi : i < n
    · simp [coeff_X_mul, coeff_monomial, show i+1 < n+1 by omega,
        show n ≠ i by omega, -BitVec.getLsbD_eq_getElem]
    · by_cases he : i = n
      · subst i
        cases h : a.getLsbD n <;>
          norm_num [h, coeff_X_mul, F₂, -BitVec.getLsbD_eq_getElem]
        decide
      · have hg : n+1 ≤ i := by omega
        simp [coeff_X_mul, coeff_monomial, show ¬ i+1 < n+1 by omega,
          show n ≠ i by omega, BitVec.getLsbD_of_ge a i hg]

@[simp] theorem wordPoly_one : wordPoly 1 = 1 := by
  ext i
  cases i with
  | zero => simp [wordPoly]
  | succ i => simp [wordPoly, coeff_one, -BitVec.getLsbD_eq_getElem]

theorem wordPoly_carryMask : wordPoly 27 = X^4 + X^3 + X + 1 := by
  ext i
  by_cases hi : i < 5
  · interval_cases i <;>
      norm_num [wordPoly, coeff_bitPoly, BitVec.getLsbD, coeff_X, coeff_one,
        Nat.testBit_succ]
  · have hg : (BitVec.ofNat 64 27).getLsbD i = false := by
      change Nat.testBit 27 i = false
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le (by decide : 27 < 2^5)
        (Nat.pow_le_pow_right (by decide) (by omega))
    simp only [wordPoly, UInt64.toBitVec_ofNat, coeff_bitPoly, hg, Bool.false_eq_true,
      ↓reduceIte, coeff_add, coeff_X_pow, coeff_X, coeff_one]
    simp [show i ≠ 4 by omega, show i ≠ 3 by omega, show 1 ≠ i by omega,
      show i ≠ 0 by omega]

/-- The reduction polynomial specified by the carry mask `27 = 0b11011`. -/
def baseModulus : F₂[X] := X^64 + X^4 + X^3 + X + 1

/-- This is a quotient ring until irreducibility has separately been proved. -/
abbrev BaseQuotient := AdjoinRoot baseModulus

def toBaseQuotient (a : K) : BaseQuotient := AdjoinRoot.mk baseModulus (wordPoly a)

@[simp] theorem toBaseQuotient_xor (a b : K) :
    toBaseQuotient (a ^^^ b) = toBaseQuotient a + toBaseQuotient b := by
  simp [toBaseQuotient]

@[simp] theorem toBaseQuotient_zero : toBaseQuotient 0 = 0 := by
  simp [toBaseQuotient]

@[simp] theorem toBaseQuotient_one : toBaseQuotient 1 = 1 := by
  simp [toBaseQuotient]

private theorem word_shiftLeft (a : K) :
    (a <<< 1).toBitVec = a.toBitVec <<< (1 : Nat) := rfl

private theorem word_shiftRight (a : K) :
    (a >>> 1).toBitVec = a.toBitVec >>> (1 : Nat) := rfl

theorem lowBit_eq (a : K) : (a &&& 1 == 1) = a.toBitVec.getLsbD 0 := by
  have h : (a &&& 1).toBitVec =
      if a.toBitVec.getLsbD 0 then (1 : BitVec 64) else 0 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i _
    change (a.toBitVec &&& 1).getLsbD i = _
    by_cases hi : i = 0
    · subst i; cases h : a.toBitVec.getLsbD 0 <;>
        simp [h, -BitVec.getLsbD_eq_getElem]
    · cases a.toBitVec.getLsbD 0 <;> simp [hi]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt64.eq_iff_toBitVec_eq, h]
  cases a.toBitVec.getLsbD 0 <;> decide

theorem carryBit_eq (a : K) : (a >>> 63 == 1) = a.toBitVec.getLsbD 63 := by
  have h : (a >>> 63).toBitVec =
      if a.toBitVec.getLsbD 63 then (1 : BitVec 64) else 0 := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i _
    change (a.toBitVec >>> (63 : Nat)).getLsbD i = _
    by_cases hi : i = 0
    · subst i; cases h : a.toBitVec.getLsbD 63 <;>
        simp [h, -BitVec.getLsbD_eq_getElem]
    · have hg : 64 ≤ 63+i := by omega
      cases a.toBitVec.getLsbD 63 <;>
        simp [hi, BitVec.getLsbD_of_ge a.toBitVec (63+i) hg]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, UInt64.eq_iff_toBitVec_eq, h]
  cases a.toBitVec.getLsbD 63 <;> decide

/-- The carry/reduction step appearing verbatim in `Concrete.kmul`. -/
def xtime (a : K) : K :=
  if a >>> 63 == 1 then (a <<< 1) ^^^ 27 else a <<< 1

theorem wordPoly_xtime (a : K) :
    wordPoly (xtime a) = X * wordPoly a +
      if a.toBitVec.getLsbD 63 then baseModulus else 0 := by
  have hs := bitPoly_shiftLeft_one (n := 63) a.toBitVec
  change wordPoly (a <<< 1) =
    X * wordPoly a + monomial 64 (if a.toBitVec.getLsbD 63 then 1 else 0) at hs
  unfold xtime
  rw [carryBit_eq]
  cases h : a.toBitVec.getLsbD 63
  · simp [h, -BitVec.getLsbD_eq_getElem] at hs ⊢
    exact hs
  · simp only [h, ↓reduceIte, wordPoly_xor, wordPoly_carryMask] at hs ⊢
    rw [hs]
    simp only [monomial_one_right_eq_X_pow]
    unfold baseModulus
    ring

theorem toBaseQuotient_xtime (a : K) :
    toBaseQuotient (xtime a) =
      AdjoinRoot.root baseModulus * toBaseQuotient a := by
  unfold toBaseQuotient
  rw [wordPoly_xtime, map_add, map_mul]
  cases a.toBitVec.getLsbD 63 <;> simp [AdjoinRoot.mk_self]

theorem toBaseQuotient_low (a : K) :
    toBaseQuotient a =
      (if a &&& 1 == 1 then 1 else 0) +
        AdjoinRoot.root baseModulus * toBaseQuotient (a >>> 1) := by
  have h := congrArg (AdjoinRoot.mk baseModulus) (bitPoly_shiftRight_one a.toBitVec)
  rw [lowBit_eq]
  cases hb : a.toBitVec.getLsbD 0 <;>
    simpa [toBaseQuotient, wordPoly, word_shiftRight, hb,
      -BitVec.getLsbD_eq_getElem] using h

private def mulStep (s : K × K × K) (_ : Nat) : K × K × K :=
  (xtime s.1, s.2.1 >>> 1, if s.2.1 &&& 1 == 1 then s.2.2 ^^^ s.1 else s.2.2)

private theorem kmul_eq_fold (a b : K) :
    kmul a b = ((List.range 64).foldl mulStep (a,b,0)).2.2 := by
  unfold kmul
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [← apply_ite]
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind]
  change (List.foldl _ (a,b,0) (List.range 64)).2.2 = _
  apply congrArg (fun s : K × K × K => s.2.2)
  apply congrArg (fun f => List.foldl f (a,b,0) (List.range 64))
  funext s i
  unfold mulStep xtime
  split_ifs <;> rfl

private def mulInvariant (s : K × K × K) : BaseQuotient :=
  toBaseQuotient s.2.2 + toBaseQuotient s.1 * toBaseQuotient s.2.1

private theorem mulStep_invariant (s : K × K × K) (i : Nat) :
    mulInvariant (mulStep s i) = mulInvariant s := by
  rcases s with ⟨x,y,z⟩
  have hy := toBaseQuotient_low y
  unfold mulInvariant mulStep
  dsimp only
  rw [toBaseQuotient_xtime]
  cases h : (y &&& 1 == 1) <;>
    simp only [h, ↓reduceIte, Bool.false_eq_true, toBaseQuotient_xor] at hy ⊢ <;>
    rw [hy] <;> ring

private theorem fold_mulInvariant (xs : List Nat) (s : K × K × K) :
    mulInvariant (xs.foldl mulStep s) = mulInvariant s := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => rw [List.foldl_cons, ih, mulStep_invariant]

private theorem fold_right (xs : List Nat) (s : K × K × K) :
    (xs.foldl mulStep s).2.1.toBitVec = s.2.1.toBitVec >>> xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons i xs ih =>
    rw [List.foldl_cons, ih]
    simp only [mulStep, word_shiftRight, List.length_cons]
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j _
    simp [Nat.add_comm, Nat.add_assoc]

/-- Exact operation-preserving bridge for all 64 iterations of the executable
carryless multiplier.  This theorem does not assume irreducibility or field laws. -/
theorem toBaseQuotient_kmul (a b : K) :
    toBaseQuotient (kmul a b) = toBaseQuotient a * toBaseQuotient b := by
  have hi := fold_mulInvariant (List.range 64) (a,b,0)
  have hy := fold_right (List.range 64) (a,b,0)
  have hz : ((List.range 64).foldl mulStep (a,b,0)).2.1 = 0 := by
    apply UInt64.toBitVec_inj.mp
    simpa using hy.trans (by simp [BitVec.ushiftRight_eq_zero])
  rw [kmul_eq_fold]
  simpa [mulInvariant, hz] using hi

theorem bitPoly_degree_lt {n : Nat} (a : BitVec n) : (bitPoly a).degree < n := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro i hi
  simp [BitVec.getLsbD_of_ge a i hi]

theorem baseModulus_degree : baseModulus.degree = 64 := by
  unfold baseModulus
  compute_degree <;> norm_num [F₂]

theorem baseModulus_monic : baseModulus.Monic := by
  have h : (X^4 + X^3 + X + (1 : F₂[X])).degree < 64 := by
    compute_degree; norm_num
  convert monic_X_pow_add h using 1; simp only [baseModulus]; ring

theorem toBaseQuotient_injective : Function.Injective toBaseQuotient := by
  intro a b h
  apply wordPoly_injective
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_dvd_of_degree_lt (AdjoinRoot.mk_eq_mk.mp h)
  rw [baseModulus_degree]
  exact (degree_sub_le _ _).trans_lt
    (max_lt (bitPoly_degree_lt a.toBitVec) (bitPoly_degree_lt b.toBitVec))

instance : Nontrivial BaseQuotient := by
  refine ⟨⟨toBaseQuotient 0, toBaseQuotient 1, ?_⟩⟩
  intro h
  have := toBaseQuotient_injective h
  exact (by decide : (0 : K) ≠ 1) this

instance : CharP BaseQuotient 2 :=
  charP_of_injective_algebraMap (algebraMap F₂ BaseQuotient).injective 2

/-- The actual bit basis, before taking the quotient. -/
theorem wordPoly_basis (i : Nat) (hi : i < 64) :
    wordPoly ((1 : K) <<< UInt64.ofNat i) = X^i := by
  ext j
  simp only [wordPoly, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat',
    UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq', BitVec.toNat_umod,
    BitVec.toNat_ofNat]
  norm_num only at *
  rw [Nat.mod_eq_of_lt (show i < 18446744073709551616 by omega)]
  rw [show (64 : BitVec 64).toNat = 64 by decide]
  rw [Nat.mod_eq_of_lt hi]
  simp only [coeff_bitPoly, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, coeff_X_pow]
  by_cases hji : j = i
  · subst j; simp [hi]
  · by_cases hlt : j < i
    · simp [hlt, hji]
    · have hj : j-i ≠ 0 := by omega
      simp [hlt, hj, hji]

theorem toBaseQuotient_basis (i : Nat) (hi : i < 64) :
    toBaseQuotient ((1 : K) <<< UInt64.ofNat i) = AdjoinRoot.root baseModulus ^ i := by
  simp [toBaseQuotient, wordPoly_basis i hi]

end

end Whir.FieldModel
