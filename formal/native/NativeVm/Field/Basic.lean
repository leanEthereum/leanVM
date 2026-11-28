module

public import LeanVM.Parameters.Field
public import Mathlib.Data.UInt

/-!
# Field elements as words and memory
-/

@[expose] public section

namespace NativeVm.Field

open LeanVM.Parameters

/-! ## `K` on words -/

theorem ofLane_xor (a b : UInt64) : K.ofLane (a ^^^ b) = K.ofLane a + K.ofLane b := (rfl)

theorem ofLane_zero : K.ofLane 0 = 0 := (rfl)

theorem ofLane_one : K.ofLane 1 = 1 := (rfl)

theorem ofLane_lane (a : K) : K.ofLane a.lane = a := (rfl)

theorem ofLane_injective : Function.Injective K.ofLane := fun _ _ h ↦ congrArg K.lane h

/-- `t · x` in `K` on a word: shift left, and fold the bit shifted out by
`x^64 = x^4 + x^3 + x + 1`. -/
def mulXW (t : UInt64) : UInt64 :=
  (t <<< 1) ^^^ (UInt64.ofBitVec (t.toBitVec.sshiftRight 63) &&& 0x1B)

/-- `mulXW` is CompPoly's word loop for the product by `2`, which runs two rounds. -/
theorem mulXW_eq_mulShift (t : UInt64) : mulXW t = BF64.mulShift 2 0 t 0 0 := by
  rw [BF64.mulShift, ite_eq_right (by decide), BF64.mulShift, ite_eq_right (by decide),
    BF64.mulShift, ite_eq_left (by decide)]
  simp only [BF64.reduceWords, BF64.tailLow, BF64.tailHigh, mulXW]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_sshiftRight]
  interval_cases i <;> simp [BitVec.msb_eq_getLsbD_last]

/-- **`mulXW` is the product by `g = x`.** -/
theorem ofLane_mulXW (t : UInt64) : K.ofLane (mulXW t) = g * K.ofLane t := by
  rw [mulXW_eq_mulShift]
  show _ = BF64.mul _ _
  rw [BF64.mul_eq_mulShift]
  rfl

/-- A word is its low bit plus `x` times the rest. -/
theorem word_bit (a : UInt64) : a = (a &&& (1 : UInt64)) ^^^ mulXW (a >>> 1) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [mulXW, BitVec.getLsbD_sshiftRight]
  interval_cases i <;> simp

/-- The low bit of a word as an element of `K`. -/
theorem ofLane_and_one (a : UInt64) :
    K.ofLane (a &&& 1) = if a.toBitVec.getLsbD 0 then 1 else 0 := by
  rw [← ofLane_one, ← ofLane_zero, ← apply_ite K.ofLane]
  congr 1
  rw [← UInt64.toBitVec_inj]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    cases h : a.toBitVec.getLsbD 0 <;> simpa [BitVec.getLsbD_eq_getElem] using h
  · cases h : a.toBitVec.getLsbD 0 <;> simp [hk0]

/-- **A word is its low bit plus `g` times the rest, in `K`.** -/
theorem ofLane_bit (a : UInt64) :
    K.ofLane a = K.ofLane (a &&& 1) + g * K.ofLane (a >>> 1) := by
  conv_lhs => rw [word_bit a]
  rw [ofLane_xor, ofLane_mulXW]

/-- The word `b` masked by the low bit of `a`, as `kmul` adds it, is `bit · b` in `K`. -/
theorem ofLane_mask (a b : UInt64) :
    K.ofLane ((0 - (a &&& 1)) &&& b) = K.ofLane (a &&& 1) * K.ofLane b := by
  rw [UInt64.and_comm, BF64.and_mask, ofLane_and_one]
  split <;> simp [ofLane_zero]

/-! ## `E` in two words -/

/-- The `E` element of the words `(lo, hi)`: limb `0` then limb `1`. -/
def eOf (lo hi : UInt64) : E := E.ofLimbs (K.ofLane lo) (K.ofLane hi)

theorem eOf_lanes (x : E) : eOf (x.limb 0).lane (x.limb 1).lane = x := by
  rw [eOf, ofLane_lane, ofLane_lane, ofLimbs_limb]

theorem eOf_add (a0 a1 b0 b1 : UInt64) :
    eOf (a0 ^^^ b0) (a1 ^^^ b1) = eOf a0 a1 + eOf b0 b1 := by
  rw [eOf, eOf, eOf, add_limbs, ofLane_xor, ofLane_xor]

theorem eOf_inj {a0 a1 b0 b1 : UInt64} : eOf a0 a1 = eOf b0 b1 ↔ a0 = b0 ∧ a1 = b1 := by
  constructor
  · intro h
    have h0 := congrArg (fun z : E ↦ z.limb 0) h
    have h1 := congrArg (fun z : E ↦ z.limb 1) h
    simp only [eOf, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact ⟨ofLane_injective h0, ofLane_injective h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem limb0_eOf (a0 a1 : UInt64) : (eOf a0 a1).limb 0 = K.ofLane a0 := by
  simp [eOf]

theorem limb1_eOf (a0 a1 : UInt64) : (eOf a0 a1).limb 1 = K.ofLane a1 := by
  simp [eOf]

theorem eOf_one : eOf 1 0 = 1 := by
  rw [eOf, ofLane_one, ofLane_zero, ← ofK_eq_ofLimbs]
  rfl

theorem eOf_zero : eOf 0 0 = 0 := by
  rw [eOf, ofLane_zero, ← ofK_eq_ofLimbs]
  rfl

/-! ## `E` in memory -/

/-- The element `x` at `p`: limb `0` at `p`, limb `1` at `p + 8`. -/
def EAt (mem : UInt64 → Option UInt64) (p : UInt64) (x : E) : Prop :=
  mem p = some (x.limb 0).lane ∧ mem (p + 8) = some (x.limb 1).lane

/-- The elements `xs` at `p`, element `i` at `p + 16 i`. -/
def EArr (mem : UInt64 → Option UInt64) (p : UInt64) (xs : List E) : Prop :=
  ∀ i (h : i < xs.length), EAt mem (p + (16 * i).toUInt64) xs[i]

theorem EArr.nil (mem : UInt64 → Option UInt64) (p : UInt64) : EArr mem p [] :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

theorem toUInt64_16_succ (i : Nat) : (16 * (i + 1)).toUInt64 = 16 + (16 * i).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, Nat.toUInt64]
  omega

theorem EArr.cons_iff {mem : UInt64 → Option UInt64} {p : UInt64} {x : E} {xs : List E} :
    EArr mem p (x :: xs) ↔ EAt mem p x ∧ EArr mem (p + 16) xs := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    rw [List.getElem_cons_zero, show Nat.toUInt64 (16 * 0) = (0 : UInt64) from rfl,
      UInt64.add_zero] at h0
    refine ⟨h0, fun i hi ↦ ?_⟩
    have := h (i + 1) (by simp; omega)
    rwa [toUInt64_16_succ, ← UInt64.add_assoc] at this
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero =>
      rw [List.getElem_cons_zero, show Nat.toUInt64 (16 * 0) = (0 : UInt64) from rfl,
        UInt64.add_zero]
      exact h0
    | succ i =>
      rw [toUInt64_16_succ, ← UInt64.add_assoc]
      exact h i (by simpa using hi)

theorem EArr.append_iff {mem : UInt64 → Option UInt64} {p : UInt64} {xs ys : List E} :
    EArr mem p (xs ++ ys) ↔ EArr mem p xs ∧ EArr mem (p + (16 * xs.length).toUInt64) ys := by
  induction xs generalizing p with
  | nil => simp [EArr.nil]
  | cons x xs ih =>
    rw [List.cons_append, EArr.cons_iff, EArr.cons_iff, ih, List.length_cons, toUInt64_16_succ,
      UInt64.add_assoc]
    tauto

/-- The word of `x`'s element `i`, limb `l`. -/
theorem EArr.word {mem : UInt64 → Option UInt64} {p : UInt64} {xs : List E} (h : EArr mem p xs)
    {i : Nat} (hi : i < xs.length) :
    mem (p + (16 * i).toUInt64) = some (xs[i].limb 0).lane ∧
      mem (p + (16 * i).toUInt64 + 8) = some (xs[i].limb 1).lane :=
  h i hi

/-! ## Words of an array -/

/-- Word `k` of a run of words at `p`. -/
def ew (p : UInt64) (k : Nat) : UInt64 := p + (8 * k).toUInt64

/-- The element `x` as element `k` of an array of `E` at `p`: words `2 k` and `2 k + 1`. -/
def EW (mem : UInt64 → Option UInt64) (p : UInt64) (k : Nat) (x : E) : Prop :=
  mem (ew p (2 * k)) = some (x.limb 0).lane ∧ mem (ew p (2 * k + 1)) = some (x.limb 1).lane

/-- Arithmetic on addresses, as a commutative ring. -/
macro "uring" : tactic => `(tactic| (
  open scoped UInt64.CommRing in
  (simp only [ew, Nat.toUInt64_eq, UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.reduceOfNat] <;>
    ring)))

theorem ew_zero (p : UInt64) : ew p 0 = p := by uring

theorem eAt_iff_EW {mem : UInt64 → Option UInt64} {p : UInt64} {k : Nat} {x : E} :
    EAt mem (p + (16 * k).toUInt64) x ↔ EW mem p k x := by
  have h0 : p + (16 * k).toUInt64 = ew p (2 * k) := by uring
  have h1 : ew p (2 * k) + 8 = ew p (2 * k + 1) := by uring
  rw [EAt, EW, h0, h1]

theorem EArr_iff_EW {mem : UInt64 → Option UInt64} {p : UInt64} {xs : List E} :
    EArr mem p xs ↔ ∀ k < xs.length, EW mem p k (xs.getD k 0) := by
  constructor
  · intro h k hk
    have := h k hk
    rw [eAt_iff_EW] at this
    rwa [← List.getElem_eq_getD 0]
  · intro h k hk
    rw [eAt_iff_EW, List.getElem_eq_getD 0]
    exact h k hk

/-- Distinct words below `2^61` have distinct addresses. -/
theorem ew_ne (p : UInt64) {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61) (h : a ≠ b) :
    ew p a ≠ ew p b := by
  intro e
  have e' := (UInt64.add_right_inj p).mp e
  have := congrArg UInt64.toNat e'
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- The words of an element, from its lanes. -/
theorem eOf_eq_iff {a b : UInt64} {x : E} :
    eOf a b = x ↔ a = (x.limb 0).lane ∧ b = (x.limb 1).lane := by
  conv_lhs => rw [← eOf_lanes x]
  exact eOf_inj

end NativeVm.Field
