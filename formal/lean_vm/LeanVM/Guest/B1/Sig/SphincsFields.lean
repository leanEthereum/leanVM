/-
  LeanVM.Guest.B1.Sig.SphincsFields

  The message digest's fields in `verify_sig_lean_sphincs` (`lean_ethereum.py:3749-3810` at leanVM main 40f877dc, `sp_md_bit`, `sp_fors_field`, `sp_md_byte`, `sp_leaf_bit`, `sp_leaf_shifts`): from the
  bits of the digest's number, the FORS leaves and the layers' leaves read as FIPS 205's
  Algorithm 19 reads them, their right shifts, and the digest's bytes placed back into its cells.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsDigestT
public import LeanVM.Guest.B1.Sig.Shifts
import LeanVM.Guest.B1.Sig.Decide

/-!
# The digest's fields

The digest is `H_msg`'s first 34 bytes: the first call's two cells and the second call's low two
bytes. `T` is their number, little endian (`T < 2^272`): byte `k` is `byteN T k`. FIPS 205's
Algorithm 19 reads its first 30 bytes most significant bit first (`base_2b`): its bit `p` is `T`'s
bit `mdPos p`; FORS tree `c`'s leaf is bits `10 c … 10 c + 9` (`forsLeafN T c`). The tree index is
bytes `30 … 32` big endian, cut to 18 bits, and the bottom leaf byte 33: the layers' leaves,
bottom first, are byte 33, byte 32 and byte 31 below the low two bits of byte 30
(`layerLeafN T l`, its bit `j` `T`'s bit `leafPos (8 l + j)`).

* `shiftsG_sound`: a field read most significant bit first from bits pinned to values and its right
  shifts (`shifts` in any bit order);
* `pw_eq`, `pw_mul`: the compiler's words `2^s` and products by them, as `eOfNat192`;
* `sMdByte_sound`, `sMdSum_sound`: `sp_md_byte`'s value is the digest's byte placed at its bit in the
  cell, the running sums the cells' low bytes.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat gen)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## The digest and its fields -/

/-- The bit of the digest's number that is its bit `p` read most significant first: bit
`7 - p % 8` of byte `p / 8`. -/
def mdPos (p : Nat) : Nat := 8 * (p / 8) + (7 - p % 8)

/-- Byte `k` of the number `T`, little endian. -/
def byteN (T k : Nat) : Nat := T / 2 ^ (8 * k) % 2 ^ 8

/-- **FORS tree `c`'s leaf** (Algorithm 19, `base_2b`): the digest's bits `10 c … 10 c + 9` read
most significant first. -/
def forsLeafN (T c : Nat) : Nat := bitsVal (fun j => T.testBit (mdPos (10 * c + 9 - j))) 10

/-- The bit of the digest's number that is bit `b` of the layers' leaves, bottom first: the bottom
leaf byte 33, the middle one byte 32, the top one byte 31 then the low two bits of byte 30. -/
def leafPos (b : Nat) : Nat :=
  if b < 8 then 264 + b else if b < 16 then 248 + b else if b < 24 then 232 + b else 216 + b

/-- **Layer `l`'s leaf** (`l < 3`, bottom first), `sLeafLen l` bits. -/
def layerLeafN (T l : Nat) : Nat := bitsVal (fun j => T.testBit (leafPos (sLeafOff l + j))) (sLeafLen l)

theorem bitE_eq (b : Bool) : bitE b = eOfNat b.toNat := by
  cases b <;> simp [bitE, Value.eOfNat_zero, Value.eOfNat_one]

theorem testBit_forsLeafN (T c j : Nat) :
    (forsLeafN T c).testBit j = (decide (j < 10) && T.testBit (mdPos (10 * c + 9 - j))) :=
  testBit_bitsVal _ _ _

theorem forsLeafN_lt (T c : Nat) : forsLeafN T c < 2 ^ 10 := bitsVal_lt _ _

theorem testBit_byteN (T k j : Nat) : (byteN T k).testBit j = (decide (j < 8) && T.testBit (8 * k + j)) := by
  rw [byteN, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm j]

theorem byteN_lt (T k : Nat) : byteN T k < 2 ^ 8 := Nat.mod_lt _ (by positivity)

theorem testBit_layerLeafN (T l j : Nat) :
    (layerLeafN T l).testBit j = (decide (j < sLeafLen l) && T.testBit (leafPos (sLeafOff l + j))) :=
  testBit_bitsVal _ _ _

theorem layerLeafN_lt (T l : Nat) : layerLeafN T l < 2 ^ sLeafLen l := bitsVal_lt _ _

/-! ## Fields and their shifts -/

theorem mem_shiftsG_step {bit : Nat → V} {n o r : Nat} (hr : 1 ≤ r) (hrn : r < n) :
    ∀ x ∈ [cst (o + 3 * r - 2) (word 2 0 0),
      mulS (.n (o + 3 * r - 1)) (.n (o + 3 * r - 2)) (.n (o + 3 * r - 3)),
      addS (.n (o + 3 * r)) (bit r) (.n (o + 3 * r - 1))], x ∈ shiftsG bit n o := by
  intro x hx
  simp only [shiftsG, List.mem_cons, List.mem_flatMap, List.mem_range]
  refine Or.inr ⟨r - 1, by omega, ?_⟩
  rw [show r - 1 + 1 = r by omega]
  simpa using hx

/-- **`shifts` in any bit order, sound**: bit `r` of an `n`-bit field read most significant first
at `bit r`, holding `f r`, the cell `o + 3 r` holds the field shifted right by `n - 1 - r`. -/
theorem shiftsG_sound {bit : Nat → V} {n o : Nat} {f : Nat → Bool} (hn : 0 < n) (hn63 : n ≤ 63)
    (hb : ∀ r < n, σ (bit r) = bitE (f r)) (h : AtomsHold rd σ (shiftsG bit n o)) :
    ∀ r < n, σ (.n (o + 3 * r)) = eOfNat (bitsVal (fun j => f (n - 1 - j)) n >>> (n - 1 - r)) := by
  set F := bitsVal (fun j => f (n - 1 - j)) n with hF
  have hN : F < 2 ^ n := bitsVal_lt _ _
  have htb : ∀ r < n, F.testBit (n - 1 - r) = f r := by
    intro r hr
    rw [hF, testBit_bitsVal]
    simp [show n - 1 - r < n by omega, show n - 1 - (n - 1 - r) = r by omega]
  intro r hr
  induction r with
  | zero =>
      have e := h.atom (List.mem_cons_self ..)
      simp only [Atom.Holds] at e
      rw [Nat.mul_zero, Nat.add_zero, e, hb 0 hn, bitE_eq, ← htb 0 hn]
      congr 1
      have h1 : F >>> (n - 1) < 2 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by rw [← pow_succ, show n - 1 + 1 = n by omega]; exact hN)
      rw [shiftRight_split, show F >>> (n - 1 - 0 + 1) = 0 by
        rw [Nat.shiftRight_eq_div_pow, show n - 1 - 0 + 1 = n by omega]; exact Nat.div_eq_of_lt hN]
      simp
  | succ r ih =>
      have hm := mem_shiftsG_step (bit := bit) (o := o) (show 1 ≤ r + 1 by omega) hr
      have e1 := h.atom (hm _ (List.mem_cons_self ..))
      have e2 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      have e3 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      simp only [Atom.Holds] at e1 e2 e3
      rw [e3, e2, e1, word_two, show o + 3 * (r + 1) - 3 = o + 3 * r by omega, ih (by omega),
        Value.gen_mul_eOfNat (by
          have : F >>> (n - 1 - r) ≤ F := Nat.shiftRight_le _ _
          have h63 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hn63
          omega),
        hb (r + 1) hr, bitE_eq, ← htb (r + 1) hr, add_comm,
        show (2 : Nat) * (F >>> (n - 1 - r)) = 2 ^ 1 * (F >>> (n - 1 - r)) by ring,
        Value.eOfNat_add_of_lt (by cases F.testBit (n - 1 - (r + 1)) <;> simp)]
      congr 1
      rw [shiftRight_split _ (n - 1 - (r + 1)), show n - 1 - (r + 1) + 1 = n - 1 - r by omega]
      ring

theorem mem_shiftsG_tail {bit : Nat → V} {n o r : Nat} (hr : 1 ≤ r) (hrn : r < n) :
    ∀ x ∈ [cst (o + 3 * r - 2) (word 2 0 0),
      mulS (.n (o + 3 * r - 1)) (.n (o + 3 * r - 2)) (.n (o + 3 * r - 3)),
      addS (.n (o + 3 * r)) (bit r) (.n (o + 3 * r - 1))], x ∈ (shiftsG bit n o).tail := by
  intro x hx
  simp only [shiftsG, List.tail_cons, List.mem_flatMap, List.mem_range]
  refine ⟨r - 1, by omega, ?_⟩
  rw [show r - 1 + 1 = r by omega]
  simpa using hx

/-- **A field with a place, and its shifts** (`sp_fors_field`): the top bit plus `2 P` at `o`, then
the shifts of `shiftsG`; the cell `o + 3 r` holds the field shifted right by `n - 1 - r` plus the
place `P` shifted left by `r + 1`. -/
theorem shiftsP_sound {bit : Nat → V} {n o P : Nat} {f : Nat → Bool} (hn : 0 < n)
    (hP : 2 ^ n * (P + 1) < 2 ^ 63) (hb : ∀ r < n, σ (bit r) = bitE (f r))
    (h0 : σ (.n o) = σ (bit 0) + eOfNat (2 * P)) (h : AtomsHold rd σ (shiftsG bit n o).tail) :
    ∀ r < n, σ (.n (o + 3 * r)) =
      eOfNat (2 ^ (r + 1) * P + bitsVal (fun j => f (n - 1 - j)) n >>> (n - 1 - r)) := by
  set F := bitsVal (fun j => f (n - 1 - j)) n with hF
  have hN : F < 2 ^ n := bitsVal_lt _ _
  have htb : ∀ r < n, F.testBit (n - 1 - r) = f r := by
    intro r hr
    rw [hF, testBit_bitsVal]
    simp [show n - 1 - r < n by omega, show n - 1 - (n - 1 - r) = r by omega]
  have hsplit : ∀ r < n, F >>> (n - 1 - r) = 2 * (F >>> (n - 1 - r + 1)) + (f r).toNat := by
    intro r hr
    rw [shiftRight_split, htb r hr]
  intro r hr
  induction r with
  | zero =>
      rw [Nat.mul_zero, Nat.add_zero, h0, hb 0 hn, bitE_eq, hsplit 0 hn,
        show F >>> (n - 1 - 0 + 1) = 0 by
          rw [Nat.shiftRight_eq_div_pow, show n - 1 - 0 + 1 = n by omega]; exact Nat.div_eq_of_lt hN,
        add_comm, show (2 : Nat) * P = 2 ^ 1 * P by ring,
        eOfNat_add_of_lt (by cases f 0 <;> simp)]
      simp
  | succ r ih =>
      have hm := mem_shiftsG_tail (bit := bit) (o := o) (show 1 ≤ r + 1 by omega) hr
      have e1 := h.atom (hm _ (List.mem_cons_self ..))
      have e2 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      have e3 := h.atom (hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      simp only [Atom.Holds] at e1 e2 e3
      have hsh : F >>> (n - 1 - r) < 2 ^ (r + 1) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show n - 1 - r + (r + 1) = n by omega]; exact hN)
      have hr1 : 2 ^ (r + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [e3, e2, e1, word_two, show o + 3 * (r + 1) - 3 = o + 3 * r by omega, ih (by omega),
        Value.gen_mul_eOfNat (by
          have : 2 ^ (r + 1) * P + 2 ^ (r + 1) ≤ 2 ^ n * (P + 1) := by
            rw [show 2 ^ (r + 1) * P + 2 ^ (r + 1) = 2 ^ (r + 1) * (P + 1) by ring]
            exact Nat.mul_le_mul_right _ hr1
          omega),
        hb (r + 1) hr, bitE_eq, add_comm,
        show (2 : Nat) * (2 ^ (r + 1) * P + F >>> (n - 1 - r)) =
          2 ^ 1 * (2 ^ (r + 1) * P + F >>> (n - 1 - r)) by ring,
        eOfNat_add_of_lt (by cases f (r + 1) <;> simp)]
      congr 1
      rw [hsplit (r + 1) hr, show n - 1 - (r + 1) + 1 = n - 1 - r by omega]
      ring

/-! ## Words `2^s` -/

theorem pw_eq {s : Nat} (hs : s < 128) : pw s = coordBasis s := by
  unfold pw coordBasis eOfNat192 word
  split_ifs with h
  · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h),
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
  · obtain ⟨t, rfl⟩ : ∃ t, s = 64 + t := ⟨s - 64, by omega⟩
    rw [show 64 + t - 64 = t by omega, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64),
      ← ofBits_mod (2 ^ 64 * 2 ^ t), Nat.mul_mod_right,
      Nat.div_eq_of_lt (show 2 ^ 64 * 2 ^ t < 2 ^ 128 by
        rw [← pow_add]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))]

/-- **A word times `2^s`**: below the limb's top, the bit pattern `2^s · v`. -/
theorem pw_mul {s v : Nat} (hs : s < 128) (h : 2 ^ (s % 64) * v < 2 ^ 64) :
    eOfNat v * pw s = eOfNat192 (2 ^ s * v) := by
  rw [pw_eq hs, mul_comm, coordBasis_mul_eOfNat (by omega) h]

theorem pw_lo {s : Nat} (hs : s < 64) : pw s = word (2 ^ s) 0 0 := by
  simp only [pw, hs, ↓reduceIte]

theorem pw_zero : pw 0 = 1 := by
  rw [pw_lo (by norm_num), pow_zero, word_eq_eOfNat, Value.eOfNat_one]

/-- `eOfNat192` of a value below `2^64` is `eOfNat`. -/
theorem eOfNat_eq192 {v : Nat} (h : v < 2 ^ 64) : eOfNat v = eOfNat192 v := (eOfNat192_of_lt h).symm

/-- A value and its high bits shifted back XOR to its low bits. -/
theorem eOfNat_low (x k : Nat) : eOfNat x + eOfNat (2 ^ k * (x >>> k)) = eOfNat (x % 2 ^ k) := by
  have hs : 2 ^ k * (x >>> k) + x % 2 ^ k = x := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_add_mod x (2 ^ k)
  have e : eOfNat x = eOfNat (2 ^ k * (x >>> k)) + eOfNat (x % 2 ^ k) := by
    rw [Value.eOfNat_add_of_lt (Nat.mod_lt _ (by positivity)), hs]
  rw [e, add_comm (eOfNat (2 ^ k * _)), add_assoc, e_add_self, add_zero]

/-- Two words of disjoint bits under one shift. -/
theorem eOfNat192_shift_add {s k X q : Nat} (hq : q < 2 ^ k) :
    eOfNat192 (2 ^ s * (2 ^ k * X)) + eOfNat192 (2 ^ s * q) = eOfNat192 (2 ^ s * (2 ^ k * X + q)) := by
  rw [add_comm, show 2 ^ s * (2 ^ k * X) = 2 ^ (s + k) * X by rw [pow_add]; ring,
    eOfNat192_add_shift (s := s + k) (by
      rw [pow_add]; exact Nat.mul_lt_mul_of_pos_left hq (by positivity))]
  congr 1
  rw [pow_add]
  ring

/-! ## The digest's bytes -/
/-- What `sp_md_byte` and `sp_fors_at` read (`vals`): FORS tree `c`'s leaf and its right shifts,
each plus the tree's place `c · 2^(10 - z)`, the FIPS 205 tree index across the trees. -/
def FValsAt (σ : Val) (T : Nat) : Prop :=
  ∀ c < 24, ∀ z < 10, σ (sFVal c z) = eOfNat (2 ^ (10 - z) * c + forsLeafN T c >>> z)

theorem forsLeaf_shift_lt_pow (T c z : Nat) (hz : z ≤ 10) : forsLeafN T c >>> z < 2 ^ (10 - z) := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (by rw [← pow_add, show z + (10 - z) = 10 by omega]; exact forsLeafN_lt T c)

/-- A value of `vals`: the place and the shift, as field elements. -/
theorem fval_split (T c z : Nat) (hz : z ≤ 10) :
    eOfNat (2 ^ (10 - z) * c + forsLeafN T c >>> z) =
      eOfNat (2 ^ (10 - z) * c) + eOfNat (forsLeafN T c >>> z) :=
  (eOfNat_add_of_lt (forsLeaf_shift_lt_pow T c z hz)).symm

theorem mdPos_byte {i j : Nat} (hj : j < 8) : mdPos (8 * i + 7 - j) = 8 * i + j := by
  unfold mdPos; omega

/-- A byte inside a leaf, unmasked: the byte starts the leaf. -/
theorem byte_in_low {T i c : Nat} (hc : 8 * i = 10 * c) : forsLeafN T c >>> 2 = byteN T i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, testBit_forsLeafN, testBit_byteN]
  by_cases hj : j < 8
  · rw [show 10 * c + 9 - (2 + j) = 8 * i + 7 - j by omega, mdPos_byte hj]
    simp [hj, show 2 + j < 10 by omega]
  · simp [hj, show ¬ 2 + j < 10 by omega]

/-- A byte inside a leaf, masked: the leaf shifted past the bits after the byte, its low byte. -/
theorem byte_in {T i c : Nat} (h1 : 10 * c ≤ 8 * i) (h2 : 8 * i + 7 < 10 * c + 10) :
    (forsLeafN T c >>> (10 * c + 2 - 8 * i)) % 2 ^ 8 = byteN T i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, testBit_forsLeafN, testBit_byteN]
  by_cases hj : j < 8
  · rw [show 10 * c + 9 - (10 * c + 2 - 8 * i + j) = 8 * i + 7 - j by omega, mdPos_byte hj]
    simp [hj, show 10 * c + 2 - 8 * i + j < 10 by omega]
  · simp [hj]

/-- A byte across two leaves: the first one's low `k1` bits, then the next one's high `8 - k1`. -/
theorem byte_across {T i c : Nat} (h2 : 10 * c + 10 ≤ 8 * i + 7)
    (h3 : 8 * i < 10 * c + 10) :
    2 ^ (8 - (10 * c + 10 - 8 * i)) * (forsLeafN T c % 2 ^ (10 * c + 10 - 8 * i)) +
      forsLeafN T (c + 1) >>> (2 + (10 * c + 10 - 8 * i)) = byteN T i := by
  set k1 := 10 * c + 10 - 8 * i with hk1
  have hq : forsLeafN T (c + 1) >>> (2 + k1) < 2 ^ (8 - k1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      show 8 - k1 + (2 + k1) = 10 by omega]
    exact forsLeafN_lt _ _
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ hq, testBit_byteN]
  by_cases hj : j < 8 - k1
  · simp only [hj, ↓reduceIte]
    rw [Nat.testBit_shiftRight, testBit_forsLeafN,
      show 10 * (c + 1) + 9 - (2 + k1 + j) = 8 * i + 7 - j by omega, mdPos_byte (by omega)]
    simp [show j < 8 by omega, show 2 + k1 + j < 10 by omega]
  · simp only [hj, ↓reduceIte]
    rw [Nat.testBit_mod_two_pow, testBit_forsLeafN]
    by_cases hj8 : j < 8
    · rw [show 10 * c + 9 - (j - (8 - k1)) = 8 * i + 7 - j by omega, mdPos_byte hj8]
      simp [hj8, show j - (8 - k1) < k1 by omega, show j - (8 - k1) < 10 by omega]
    · simp [hj8, show ¬ j - (8 - k1) < k1 by omega]

theorem forsLeaf_shift_lt (T c z : Nat) : forsLeafN T c >>> z < 2 ^ 64 :=
  lt_of_le_of_lt (Nat.shiftRight_le _ _) (lt_trans (forsLeafN_lt T c) (by norm_num))

theorem two_pow_mod_mul_lt {s k v : Nat} (hs : s % 64 + k ≤ 64) (hv : v < 2 ^ k) :
    2 ^ (s % 64) * v < 2 ^ 64 :=
  calc 2 ^ (s % 64) * v < 2 ^ (s % 64) * 2 ^ k := Nat.mul_lt_mul_of_pos_left hv (by positivity)
    _ = 2 ^ (s % 64 + k) := (pow_add _ _ _).symm
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hs

/-- A place and a value of disjoint bits under it. -/
theorem eOfNat_place {k q r : Nat} (hr : r < 2 ^ k) :
    eOfNat (2 ^ k * q + r) = eOfNat (2 ^ k * q) + eOfNat r :=
  (Value.eOfNat_add_of_lt hr).symm

/-- **A byte inside a leaf, masked**: the leaf shifted by `z` and its low byte; the place `vals`
carries cancels. -/
theorem mdIn_mask_sound {T c z b : Nat} (hc : c < 24) (hz : z + 8 < 10) (hv : FValsAt σ T)
    (h : AtomsHold rd σ (mdIn c z b true).1) :
    σ (mdIn c z b true).2.2 = eOfNat ((forsLeafN T c >>> z) % 2 ^ 8) := by
  simp only [mdIn, ↓reduceIte] at h ⊢
  have k0 : σ (.n b) = word 256 0 0 := h.atom (a := .const (.n b) _) (by simp [cst])
  have m1 : σ (.n (b + 1)) = σ (sFVal c (z + 8)) * σ (.n b) :=
    h.atom (a := .mul (.n (b + 1)) _ _) (by simp [mulS])
  have a2 : σ (.n (b + 2)) = σ (sFVal c z) + σ (.n (b + 1)) :=
    h.atom (a := .add (.n (b + 2)) _ _) (by simp [addS])
  have h8 := forsLeaf_shift_lt_pow T c (z + 8) (by omega)
  have hsh : forsLeafN T c >>> (z + 8) = (forsLeafN T c >>> z) >>> 8 := by rw [Nat.shiftRight_add]
  have h4 : 2 ^ (10 - (z + 8)) ≤ 4 :=
    calc 2 ^ (10 - (z + 8)) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hlt : 2 ^ 8 * (forsLeafN T c >>> (z + 8)) < 2 ^ (10 - z) := by
    rw [show 10 - z = 8 + (10 - (z + 8)) by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_left h8 (by positivity)
  have e8 : σ (.n (b + 1)) = eOfNat (2 ^ (10 - z) * c) + eOfNat (2 ^ 8 * (forsLeafN T c >>> (z + 8))) := by
    rw [m1, k0, hv c hc _ (by omega), word_eq_eOfNat, show (256 : Nat) = 2 ^ 8 by norm_num, mul_comm,
      Value.eOfNat_two_pow_mul (by nlinarith), mul_add, ← mul_assoc, ← pow_add,
      show 8 + (10 - (z + 8)) = 10 - z by omega, eOfNat_place hlt]
  rw [a2, e8, hv c hc _ (by omega), fval_split T c z (by omega), hsh,
    show ∀ a b d : E, a + b + (a + d) = b + d from fun a b d => by
      rw [add_add_add_comm, e_add_self, zero_add],
    eOfNat_low]

/-- **A byte placed at bit `s`**. -/
theorem mdScale_sound {s v : Nat} {m : List Stmt × Nat × V} (hs : s < 128) (hs56 : s % 64 ≤ 56)
    (hv : v < 2 ^ 8) (hm : AtomsHold rd σ m.1 → σ m.2.2 = eOfNat v)
    (h : AtomsHold rd σ (mdScale s m).1) : σ (mdScale s m).2.2 = eOfNat192 (2 ^ s * v) := by
  unfold mdScale at h ⊢
  by_cases hs0 : s = 0
  · simp only [hs0, ↓reduceIte] at h ⊢
    rw [hm h, pow_zero, one_mul, eOfNat_eq192 (lt_trans hv (by norm_num))]
  · simp only [hs0, ↓reduceIte] at h ⊢
    have k := h.atom (a := .const (.n m.2.1) (pw s)) (by simp [cst])
    have mu := h.atom (a := .mul (.n (m.2.1 + 1)) m.2.2 (.n m.2.1)) (by simp [mulS])
    simp only [Atom.Holds] at k mu
    rw [mu, k, hm h.left, pw_mul hs (two_pow_mod_mul_lt (k := 8) (by omega) hv)]

/-- **A byte and a place placed at bit `s`**: the byte's word, the place's product. -/
theorem mdScale_place_sound {s v p : Nat} {m : List Stmt × Nat × V} (hs : s < 128)
    (hs56 : s % 64 ≤ 56) (hv : v < 2 ^ 8) (hm : AtomsHold rd σ m.1 → σ m.2.2 = eOfNat v + eOfNat p)
    (h : AtomsHold rd σ (mdScale s m).1) :
    σ (mdScale s m).2.2 = eOfNat192 (2 ^ s * v) + eOfNat p * pw s := by
  unfold mdScale at h ⊢
  by_cases hs0 : s = 0
  · simp only [hs0, ↓reduceIte] at h ⊢
    rw [hm h, pow_zero, one_mul, eOfNat_eq192 (lt_trans hv (by norm_num)), pw_zero, mul_one]
  · simp only [hs0, ↓reduceIte] at h ⊢
    have k := h.atom (a := .const (.n m.2.1) (pw s)) (by simp [cst])
    have mu := h.atom (a := .mul (.n (m.2.1 + 1)) m.2.2 (.n m.2.1)) (by simp [mulS])
    simp only [Atom.Holds] at k mu
    rw [mu, k, hm h.left, add_mul, pw_mul hs (two_pow_mod_mul_lt (k := 8) (by omega) hv)]

/-- **A byte across two leaves**, placed at bit `s`: the second leaf's place `(c + 1) · 2^(8 - k1)`
stays (the first one's cancels). -/
theorem mdAcross_sound {T c k1 s b : Nat} (hc : c + 1 < 24) (hk1 : 1 ≤ k1) (hk7 : k1 ≤ 7)
    (hs : s < 128) (hs56 : s % 64 ≤ 56) (hv : FValsAt σ T) (h : AtomsHold rd σ (mdAcross c k1 s b).1) :
    σ (mdAcross c k1 s b).2.2 = eOfNat192 (2 ^ s * (2 ^ (8 - k1) * (forsLeafN T c % 2 ^ k1) +
      forsLeafN T (c + 1) >>> (2 + k1))) + eOfNat (2 ^ (8 - k1) * (c + 1)) * pw s := by
  have hq : forsLeafN T (c + 1) >>> (2 + k1) < 2 ^ (8 - k1) := by
    have := forsLeaf_shift_lt_pow T (c + 1) (2 + k1) (by omega)
    rwa [show 10 - (2 + k1) = 8 - k1 by omega] at this
  have hX : forsLeafN T c % 2 ^ k1 < 2 ^ k1 := Nat.mod_lt _ (by positivity)
  have hhi : ∀ x, x ∈ [cst b (pw k1), mulS (.n (b + 1)) (sFVal c k1) (.n b),
      addS (.n (b + 2)) (sFVal c 0) (.n (b + 1)), cst (b + 3) (pw (s + 8 - k1)),
      mulS (.n (b + 4)) (.n (b + 2)) (.n (b + 3))] → x ∈ (mdAcross c k1 s b).1 := by
    intro x hx
    unfold mdAcross
    split_ifs <;> exact List.mem_append_left _ hx
  have k0 : σ (.n b) = pw k1 := h.atom (a := .const (.n b) _) (hhi _ (by simp [cst]))
  have m1 : σ (.n (b + 1)) = σ (sFVal c k1) * σ (.n b) :=
    h.atom (a := .mul (.n (b + 1)) _ _) (hhi _ (by simp [mulS]))
  have a2 : σ (.n (b + 2)) = σ (sFVal c 0) + σ (.n (b + 1)) :=
    h.atom (a := .add (.n (b + 2)) _ _) (hhi _ (by simp [addS]))
  have k3 : σ (.n (b + 3)) = pw (s + 8 - k1) :=
    h.atom (a := .const (.n (b + 3)) _) (hhi _ (by simp [cst]))
  have m4 : σ (.n (b + 4)) = σ (.n (b + 2)) * σ (.n (b + 3)) :=
    h.atom (a := .mul (.n (b + 4)) _ _) (hhi _ (by simp [mulS]))
  have hk : forsLeafN T c >>> k1 < 2 ^ (10 - k1) := forsLeaf_shift_lt_pow T c k1 (by omega)
  have hlt : 2 ^ k1 * (forsLeafN T c >>> k1) < 2 ^ 10 := by
    rw [show 10 = k1 + (10 - k1) by omega, pow_add]
    exact Nat.mul_lt_mul_of_pos_left hk (by positivity)
  have e1 : σ (.n (b + 1)) = eOfNat (2 ^ 10 * c) + eOfNat (2 ^ k1 * (forsLeafN T c >>> k1)) := by
    rw [m1, k0, hv c (by omega) k1 (by omega), pw_lo (by omega), word_eq_eOfNat, mul_comm,
      Value.eOfNat_two_pow_mul (by
        have h7 : 2 ^ k1 * 2 ^ (10 - k1) = 2 ^ 10 := by rw [← pow_add]; congr 1; omega
        have hc1 : 2 ^ (10 - k1) * c + forsLeafN T c >>> k1 < 2 ^ (10 - k1) * 24 :=
          calc 2 ^ (10 - k1) * c + forsLeafN T c >>> k1 < 2 ^ (10 - k1) * c + 2 ^ (10 - k1) := by omega
            _ = 2 ^ (10 - k1) * (c + 1) := by ring
            _ ≤ 2 ^ (10 - k1) * 24 := Nat.mul_le_mul_left _ (by omega)
        calc 2 ^ k1 * (2 ^ (10 - k1) * c + forsLeafN T c >>> k1)
            < 2 ^ k1 * (2 ^ (10 - k1) * 24) := Nat.mul_lt_mul_of_pos_left hc1 (by positivity)
          _ = 2 ^ 10 * 24 := by rw [← mul_assoc, h7]
          _ < 2 ^ 64 := by norm_num),
      mul_add, ← mul_assoc, ← pow_add, show k1 + (10 - k1) = 10 by omega, eOfNat_place hlt]
  have e2 : σ (.n (b + 2)) = eOfNat (forsLeafN T c % 2 ^ k1) := by
    rw [a2, e1, hv c (by omega) 0 (by omega), fval_split T c 0 (by omega), Nat.shiftRight_zero,
      Nat.sub_zero, show ∀ a b d : E, a + b + (a + d) = b + d from fun a b d => by
        rw [add_add_add_comm, e_add_self, zero_add],
      eOfNat_low]
  have e4 : σ (.n (b + 4)) = eOfNat192 (2 ^ (s + 8 - k1) * (forsLeafN T c % 2 ^ k1)) := by
    rw [m4, e2, k3, pw_mul (by omega) (two_pow_mod_mul_lt (k := k1) (by omega) hX)]
  have hsk : 2 ^ (s + 8 - k1) * (forsLeafN T c % 2 ^ k1) = 2 ^ s * (2 ^ (8 - k1) * (forsLeafN T c % 2 ^ k1)) := by
    rw [← mul_assoc, ← pow_add, show s + (8 - k1) = s + 8 - k1 by omega]
  have hv1 : σ (sFVal (c + 1) (2 + k1)) =
      eOfNat (forsLeafN T (c + 1) >>> (2 + k1)) + eOfNat (2 ^ (8 - k1) * (c + 1)) := by
    rw [hv (c + 1) hc _ (by omega), show 10 - (2 + k1) = 8 - k1 by omega, eOfNat_place hq, add_comm]
  unfold mdAcross at h ⊢
  by_cases hs0 : s = 0
  · simp only [hs0, ↓reduceIte] at h ⊢
    have a5 : σ (.n (b + 5)) = σ (.n (b + 4)) + σ (sFVal (c + 1) (2 + k1)) :=
      h.atom (a := .add (.n (b + 5)) _ _) (by simp [addS])
    rw [a5, e4, hv1, ← add_assoc, eOfNat_eq192 (forsLeaf_shift_lt _ _ _), hsk, hs0, pw_zero, mul_one]
    congr 1
    simpa only [pow_zero, one_mul] using eOfNat192_shift_add (s := 0) (X := forsLeafN T c % 2 ^ k1) hq
  · simp only [hs0, ↓reduceIte] at h ⊢
    have k5 : σ (.n (b + 5)) = pw s := h.atom (a := .const (.n (b + 5)) _) (by simp [cst])
    have m6 : σ (.n (b + 6)) = σ (sFVal (c + 1) (2 + k1)) * σ (.n (b + 5)) :=
      h.atom (a := .mul (.n (b + 6)) _ _) (by simp [mulS])
    have a7 : σ (.n (b + 7)) = σ (.n (b + 4)) + σ (.n (b + 6)) :=
      h.atom (a := .add (.n (b + 7)) _ _) (by simp [addS])
    rw [a7, e4, m6, k5, hv1, add_mul, pw_mul hs (two_pow_mod_mul_lt (k := 8 - k1) (by omega) hq),
      ← add_assoc, hsk, eOfNat192_shift_add hq]

/-- **The place `vals` adds to digest byte `i`** (`G:4001-4007`): in a byte inside a field only
where the field starts (`c · 256`), in a byte across two the second field's
(`(c + 1) · 2^(8 i + 8 - 10 (c + 1))`). -/
def mdPlaceN (i : Nat) : Nat :=
  if (8 * i + 7) / 10 ≠ 8 * i / 10 then (8 * i / 10 + 1) * 2 ^ (8 * i + 8 - 10 * (8 * i / 10 + 1))
  else if 8 * i = 10 * (8 * i / 10) then 8 * i / 10 * 256 else 0

/-- The place at its bit in the cell, `pc` of `G:4001-4007`. -/
def mdPlace (i : Nat) : E := eOfNat (mdPlaceN i) * pw (8 * (i % 16))

/-- The places of bytes `i0 ..< i0 + n`, summed. -/
def mdPlaces (i0 : Nat) : Nat → E
  | 0 => 0
  | n + 1 => mdPlaces i0 n + mdPlace (i0 + n)

theorem mdPlaces_succ (i0 n : Nat) : mdPlaces i0 (n + 1) = mdPlaces i0 n + mdPlace (i0 + n) := rfl

/-- Limb `j` of `pw s`. -/
def pwLimb (s j : Nat) : Nat :=
  if j = 0 then (if s < 64 then 2 ^ s else 0) else if j = 1 then (if s < 64 then 0 else 2 ^ (s - 64))
  else 0

theorem pw_limbs (s : Nat) : pw s = word (pwLimb s 0) (pwLimb s 1) (pwLimb s 2) := by
  unfold pw pwLimb
  by_cases h : s < 64 <;> simp [h]

/-- The place's limb `j`: `pw`'s limb times the place. -/
def mdPlaceLimb (i j : Nat) : K := K.ofBits (pwLimb (8 * (i % 16)) j) * K.ofBits (mdPlaceN i)

/-- The places' limb `j`, summed. -/
def mdPlacesLimb (i0 j : Nat) : Nat → K
  | 0 => 0
  | n + 1 => mdPlacesLimb i0 j n + mdPlaceLimb (i0 + n) j

theorem mdPlace_limbs (i : Nat) :
    mdPlace i = E.ofLimbs (mdPlaceLimb i 0) (mdPlaceLimb i 1) (mdPlaceLimb i 2) := by
  rw [mdPlace, pw_limbs, mul_comm, eOfNat, word, ofLimbs_mul_ofK]
  rfl

theorem mdPlaces_limbs (i0 : Nat) : ∀ n, mdPlaces i0 n =
    E.ofLimbs (mdPlacesLimb i0 0 n) (mdPlacesLimb i0 1 n) (mdPlacesLimb i0 2 n)
  | 0 => by
      show (0 : E) = E.ofLimbs 0 0 0
      rw [← word_zero, word, ofBits_zero]
  | n + 1 => by
      rw [mdPlaces_succ, mdPlaces_limbs i0 n, mdPlace_limbs, ofLimbs_add]
      rfl

/-- **`corr0`, `corr1`** are the places of the two cells' bytes, checked limb by limb. -/
theorem corr_eq : corr0W = mdPlaces 0 16 ∧ corr1W = mdPlaces 16 14 := by
  rw [mdPlaces_limbs, mdPlaces_limbs, corr0W, corr1W, word, word, ofLimbs_inj, ofLimbs_inj]
  decide +kernel

/-- **`sp_md_byte`, sound**: the value is digest byte `i < 30` at bit `8 (i % 16)` of its cell, plus
its place. -/
theorem sMdByte_sound {T i b : Nat} (hi : i < 30) (hv : FValsAt σ T)
    (h : AtomsHold rd σ (sMdByte i b).1) :
    σ (sMdByte i b).2.2 = eOfNat192 (2 ^ (8 * (i % 16)) * byteN T i) + mdPlace i := by
  have hc24 : 8 * i / 10 < 24 := by omega
  have hs : 8 * (i % 16) % 64 ≤ 56 := by omega
  have hs128 : 8 * (i % 16) < 128 := by omega
  unfold sMdByte at h ⊢
  unfold mdPlace mdPlaceN
  by_cases hin : (8 * i + 7) / 10 = 8 * i / 10
  · simp only [hin, ↓reduceIte, ne_eq, not_true_eq_false] at h ⊢
    refine mdScale_place_sound hs128 hs (byteN_lt T i) (fun hm => ?_) h
    by_cases hlo : 8 * i = 10 * (8 * i / 10)
    · have hb : (8 * i != 10 * (8 * i / 10)) = false := by rw [bne_eq_false_iff_eq]; exact hlo
      rw [hb, ite_eq_left hlo]
      show σ (sFVal (8 * i / 10) (10 * (8 * i / 10) + 2 - 8 * i)) = _
      rw [hv _ hc24 _ (by omega), show 10 * (8 * i / 10) + 2 - 8 * i = 2 by omega,
        fval_split T _ 2 (by omega), byte_in_low hlo, add_comm,
        show 2 ^ (10 - 2) * (8 * i / 10) = 8 * i / 10 * 256 by norm_num; ring]
    · have hb : (8 * i != 10 * (8 * i / 10)) = true := by rw [bne_iff_ne]; exact hlo
      rw [hb] at hm ⊢
      rw [ite_eq_right hlo]
      rw [mdIn_mask_sound hc24 (by omega) hv hm, byte_in (by omega) (by omega), Value.eOfNat_zero,
        add_zero]
  · simp only [hin, ↓reduceIte, ne_eq, not_false_eq_true] at h ⊢
    rw [mdAcross_sound (by omega) (by omega) (by omega) hs128 hs hv h, byte_across (by omega) (by omega),
      show 2 ^ (8 - (10 * (8 * i / 10) + 10 - 8 * i)) * (8 * i / 10 + 1) =
        (8 * i / 10 + 1) * 2 ^ (8 * i + 8 - 10 * (8 * i / 10 + 1)) by
        rw [mul_comm]; congr 2; omega]

theorem mod_split (X r n : Nat) : X % 2 ^ (r + n) = 2 ^ r * (X / 2 ^ r % 2 ^ n) + X % 2 ^ r := by
  rw [pow_add, Nat.mod_mul, Nat.add_comm]


/-- **The running sums**: bytes `i ..< i + m` added to the sum of the bytes from `i0` (`0` or
`16`) before `i`, each at its bit in the cell, with their places. -/
theorem sMdSum_sound {T i0 : Nat} (hi0 : i0 = 0 ∨ i0 = 16) (hv : FValsAt σ T) :
    ∀ (m i : Nat) (acc : V) (b : Nat), i0 ≤ i → i + m ≤ 30 → i + m ≤ i0 + 16 →
      σ acc = eOfNat192 (T / 2 ^ (8 * i0) % 2 ^ (8 * (i - i0))) + mdPlaces i0 (i - i0) →
      AtomsHold rd σ (sMdSum m i acc b).1 →
      σ (sMdSum m i acc b).2.2 =
        eOfNat192 (T / 2 ^ (8 * i0) % 2 ^ (8 * (i + m - i0))) + mdPlaces i0 (i + m - i0)
  | 0, i, acc, b, _, _, _, hacc, _ => by simpa [sMdSum] using hacc
  | m + 1, i, acc, b, h1, h2, h3, hacc, h => by
      have h' : AtomsHold rd σ ((sMdByte i b).1 ++ [addS (.n (sMdByte i b).2.1) acc (sMdByte i b).2.2] ++
          (sMdSum m (i + 1) (.n (sMdByte i b).2.1) ((sMdByte i b).2.1 + 1)).1) := h
      have hx := sMdByte_sound (T := T) (by omega) hv h'.left.left
      have ha : σ (.n (sMdByte i b).2.1) = σ acc + σ (sMdByte i b).2.2 :=
        h'.left.right.atom (a := .add (.n (sMdByte i b).2.1) acc (sMdByte i b).2.2) (by simp [addS])
      have hmod : i % 16 = i - i0 := by omega
      have hnext : σ (.n (sMdByte i b).2.1) =
          eOfNat192 (T / 2 ^ (8 * i0) % 2 ^ (8 * (i + 1 - i0))) + mdPlaces i0 (i + 1 - i0) := by
        rw [ha, hacc, hx, add_add_add_comm, show i + 1 - i0 = i - i0 + 1 by omega, mdPlaces_succ,
          show i0 + (i - i0) = i by omega, hmod, eOfNat192_add_shift (Nat.mod_lt _ (by positivity)),
          show 8 * (i - i0 + 1) = 8 * (i - i0) + 8 by omega, mod_split, byteN, Nat.div_div_eq_div_mul,
          ← pow_add, show 8 * i0 + 8 * (i - i0) = 8 * i by omega, Nat.add_comm (2 ^ (8 * (i - i0)) * _)]
      have := sMdSum_sound hi0 hv m (i + 1) _ _ (by omega) (by omega) (by omega) hnext h'.right
      show σ (sMdSum m (i + 1) _ _).2.2 = _
      rw [this, show i + 1 + m = i + (m + 1) by omega]

/-- **`md0`** with `corr0`: the first call's first cell, the digest's bytes `0 … 15`. -/
theorem sMd0_sound {T : Nat} (hv : FValsAt σ T) (h0 : AtomsHold rd σ (sMdByte 0 1067).1)
    (h : AtomsHold rd σ sMd0.1) : σ sMd0.2.2 + corr0W = eOfNat192 (T % 2 ^ 128) := by
  have hb := sMdByte_sound (T := T) (i := 0) (b := 1067) (by norm_num) hv h0
  have := sMdSum_sound (Or.inl rfl) hv 15 1 _ _ (by norm_num) (by norm_num) (by norm_num)
    (by rw [hb]; simp [byteN, mdPlaces]) h
  unfold sMd0
  rw [this, corr_eq.1, add_assoc, e_add_self, add_zero]
  simp

/-- **`md1`** with `corr1`: the digest's bytes `16 … 29`, at the first call's second cell's low
bits. -/
theorem sMd1_sound {T : Nat} (hv : FValsAt σ T) (h : AtomsHold rd σ sMd1.1) :
    σ sMd1.2.2 + corr1W = eOfNat192 (T / 2 ^ 128 % 2 ^ 112) := by
  have h' : AtomsHold rd σ ((sMdByte 16 sMd0.2.1).1 ++
      (sMdSum 13 17 (sMdByte 16 sMd0.2.1).2.2 (sMdByte 16 sMd0.2.1).2.1).1) := h
  have hb := sMdByte_sound (T := T) (i := 16) (b := sMd0.2.1) (by norm_num) hv h'.left
  have := sMdSum_sound (Or.inr rfl) hv 13 17 _ _ (by norm_num) (by norm_num) (by norm_num)
    (by rw [hb]; simp [byteN, mdPlaces]) h'.right
  show σ (sMdSum 13 17 (sMdByte 16 sMd0.2.1).2.2 (sMdByte 16 sMd0.2.1).2.1).2.2 + _ = _
  rw [this, corr_eq.2, add_assoc, e_add_self, add_zero]

/-! ## The bits -/

/-- **The digest's bits are those of `T`**: the run `n28 …` holds `T`'s bits `0 … 271`. -/
def BitsAt (σ : Val) (T : Nat) : Prop := ∀ k < 272, σ (.n (28 + k)) = bitE (T.testBit k)

theorem mem_sBooleans {k : Nat} (hk : k < 272) :
    Stmt.atom (.mul (.n (28 + k)) (.n (28 + k)) (.n (28 + k))) ∈ sBooleans := by
  unfold sBooleans
  by_cases h1 : k < 128
  · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr h1, List.mem_cons_self ..⟩)
  · by_cases h2 : k < 256
    · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨k - 128, List.mem_range.mpr (by omega), ?_⟩)
      refine List.mem_cons_of_mem _ ?_
      rw [show 156 + (k - 128) = 28 + k by omega]
      exact List.mem_cons_self ..
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨k - 256, List.mem_range.mpr (by omega), ?_⟩)
      show mulS _ _ _ = _
      rw [show 284 + (k - 256) = 28 + k by omega]
      rfl

/-- **The bits pinned Boolean are those of their number.** -/
theorem sBooleans_bitsAt (h : AtomsHold rd σ sBooleans) : BitsAt σ (bitsOf σ 28 272) := by
  intro k hk
  have hb : IsBit (σ (.n (28 + k))) := (h.atom (mem_sBooleans hk)).symm
  rw [bitsOf, testBit_bitsVal]
  simp only [hk, decide_true, Bool.true_and]
  rcases isBit_cases hb with h0 | h1
  · rw [h0]; simp [bitE]
  · rw [h1]; simp [bitE]

theorem bitsOf_lt' (σ : Val) : bitsOf σ 28 272 < 2 ^ 272 := bitsVal_lt _ _

theorem sMdBit_eq {p : Nat} : sMdBit p = .n (28 + mdPos p) := by
  simp only [sMdBit, mdPos]; congr 1; omega

theorem mdPos_lt {p : Nat} (hp : p < 240) : mdPos p < 240 := by unfold mdPos; omega

theorem sLeafBit_eq {b : Nat} (hb : b < 26) : sLeafBit b = .n (28 + leafPos b) := by
  simp only [sLeafBit, leafPos]
  split_ifs <;> congr 1 <;> omega

theorem leafPos_lt {b : Nat} (hb : b < 26) : leafPos b < 272 := by
  unfold leafPos; split_ifs <;> omega

/-! ## The fields -/

/-- **`sp_fors_field`, sound**: every FORS leaf and its shifts, with the tree's place. -/
theorem sForsFields_sound {T : Nat} (hb : BitsAt σ T) (h : AtomsHold rd σ sForsFields) : FValsAt σ T := by
  intro c hc z hz
  have hsub : ∀ x ∈ sForsField c, x ∈ sForsFields := by
    intro x hx
    simp only [sForsFields, List.mem_flatMap, List.mem_range]
    exact ⟨c, hc, hx⟩
  have hF := h.sub hsub
  have hbit : ∀ r < 10, σ (sMdBit (10 * c + r)) = bitE (T.testBit (mdPos (10 * c + r))) := by
    intro r hr
    rw [sMdBit_eq]; exact hb _ (by have := mdPos_lt (p := 10 * c + r) (by omega); omega)
  have h0 : σ (.n (300 + 29 * c)) = σ (sMdBit (10 * c + 0)) + eOfNat (2 * c) := by
    by_cases hc0 : c = 0
    · subst hc0
      have e := hF.atom (a := .copy (.n 300) (sMdBit 0)) (by simp [sForsField, copyS])
      simp only [Atom.Holds] at e
      simpa [Value.eOfNat_zero] using e
    · have k := hF.atom (a := .const (.n (299 + 29 * c)) (word (2 * c) 0 0))
        (by simp [sForsField, hc0, cst])
      have a := hF.atom (a := .add (.n (300 + 29 * c)) (sMdBit (10 * c)) (.n (299 + 29 * c)))
        (by simp [sForsField, hc0, addS])
      simp only [Atom.Holds] at k a
      rw [a, k, word_eq_eOfNat, Nat.add_zero]
  have hs := shiftsP_sound (σ := σ) (bit := fun r => sMdBit (10 * c + r)) (n := 10)
    (o := 300 + 29 * c) (P := c) (f := fun r => T.testBit (mdPos (10 * c + r))) (by norm_num)
    (by omega) hbit h0 (hF.sub fun x hx => List.mem_append_right _ hx) (9 - z) (by omega)
  rw [show sFVal c z = .n (300 + 29 * c + 3 * (9 - z)) from rfl, hs, show 10 - 1 - (9 - z) = z by omega,
    show 9 - z + 1 = 10 - z by omega]
  congr 3

/-- What `sp_leaf_shifts` gives: each layer's leaf and its shifts. -/
def LValsAt (σ : Val) (T : Nat) : Prop :=
  ∀ l < 3, ∀ z < sLeafLen l, σ (sLVal (sLeafOff l + z)) = eOfNat (layerLeafN T l >>> z)

theorem sLeafLen_le {l : Nat} : 8 ≤ sLeafLen l ∧ sLeafLen l ≤ 10 := by
  unfold sLeafLen; split_ifs <;> omega

/-- **`sp_leaf_shifts`, sound.** -/
theorem sLeafShifts_sound {T : Nat} (hb : BitsAt σ T) (h : AtomsHold rd σ sLeafShifts) : LValsAt σ T := by
  intro l hl z hz
  obtain ⟨h8, h10⟩ := sLeafLen_le (l := l)
  have hsub : ∀ x ∈ shiftsG (fun r => sLeafBit (sLeafOff l + sLeafLen l - 1 - r)) (sLeafLen l)
      (sLeafBase l), x ∈ sLeafShifts := by
    intro x hx
    simp only [sLeafShifts, List.mem_flatMap, List.mem_range]
    exact ⟨l, hl, hx⟩
  have hoff : sLeafOff l + sLeafLen l ≤ 26 := by
    simp only [sLeafOff, sLeafLen]; split_ifs <;> omega
  have hs := shiftsG_sound (σ := σ) (bit := fun r => sLeafBit (sLeafOff l + sLeafLen l - 1 - r))
    (n := sLeafLen l) (o := sLeafBase l)
    (f := fun r => T.testBit (leafPos (sLeafOff l + sLeafLen l - 1 - r))) (by omega) (by omega)
    (fun r hr => by
      show σ (sLeafBit _) = _
      rw [sLeafBit_eq (by omega)]; exact hb _ (leafPos_lt (by omega)))
    (h.sub hsub) (sLeafLen l - 1 - z) (by omega)
  have hpos : sLVal (sLeafOff l + z) = .n (sLeafBase l + 3 * (sLeafLen l - 1 - z)) := by
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
    · have : z < 8 := by simpa [sLeafLen] using hz
      simp [sLVal, sLeafOff, sLeafLen, sLeafBase, this]
    · have : z < 8 := by simpa [sLeafLen] using hz
      simp [sLVal, sLeafOff, sLeafLen, sLeafBase, show 8 + z < 16 by omega]
      omega
    · have : z < 10 := by simpa [sLeafLen] using hz
      have h1 : ¬ 2 * 8 + z < 8 := by omega
      have h2 : ¬ 2 * 8 + z < 16 := by omega
      simp only [sLVal, sLeafOff, sLeafLen, sLeafBase, h1, h2, ↓reduceIte]
      congr 1
      omega
  rw [hpos, hs, show sLeafLen l - 1 - (sLeafLen l - 1 - z) = z by omega]
  congr 2
  exact bitsVal_congr fun j hj => by congr 3; omega

end
end LeanVM.Guest.B1.Sig
