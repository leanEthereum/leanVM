module

public import Native.Bytes
public import Mathlib.Data.UInt

/-!
# Word lists and arithmetic

Consecutive words, conditional rewrites and unsigned word arithmetic.
-/

@[expose] public section

namespace Native.SphincsVerifier

/-- The `n` words from `j`. -/
def words (V : Nat → UInt64) (j n : Nat) : List UInt64 := (List.range n).map fun i ↦ V (j + i)

theorem words_length (V : Nat → UInt64) (j n : Nat) : (words V j n).length = n := by simp [words]

theorem words_getElem (V : Nat → UInt64) (j n i : Nat) (h : i < (words V j n).length) :
    (words V j n)[i] = V (j + i) := by simp [words]

theorem words_congr {V V' : Nat → UInt64} {j n : Nat} (h : ∀ i < n, V' (j + i) = V (j + i)) :
    words V' j n = words V j n := by
  simp only [words, List.map_inj_left, List.mem_range]
  exact h

theorem words_add (V : Nat → UInt64) (j n m : Nat) :
    words V j (n + m) = words V j n ++ words V (j + n) m := by
  simp only [words, List.range_add, List.map_append, List.map_map]
  congr 1
  simp only [List.map_inj_left]
  intro i _
  simp [Nat.add_assoc]

theorem words_succ (V : Nat → UInt64) (j n : Nat) : words V j (n + 1) = V j :: words V (j + 1) n := by
  simp only [words, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  simp only [List.map_inj_left]
  intro i _
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]

theorem words_zero (V : Nat → UInt64) (j : Nat) : words V j 0 = [] := rfl

theorem words_one (V : Nat → UInt64) (j : Nat) : words V j 1 = [V j] := rfl

theorem ite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a b : α} :
    (if c then a else b) = b := by simp [h]

theorem ite_yes {α : Type} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

theorem dite_no {α : Type} {c : Prop} [Decidable c] (h : ¬c) {a : c → α} {b : ¬c → α} :
    dite c a b = b h := by simp [h]

theorem dite_yes {α : Type} {c : Prop} [Decidable c] (h : c) {a : c → α} {b : ¬c → α} :
    dite c a b = a h := by simp [h]

theorem toNat_toUInt64' {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- An immediate literal as a word. -/
theorem imm_nat (k : Nat) : (OfNat.ofNat k : Int64).toUInt64 = k.toUInt64 := Int64.toUInt64_ofNat'

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : a.toUInt64 = b.toUInt64) : a = b := by
  have := congrArg UInt64.toNat h
  rwa [toNat_toUInt64' ha, toNat_toUInt64' hb] at this

theorem toUInt64_add (a b : Nat) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  simp only [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_sub {a b : Nat} (h : b ≤ a) : a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  rw [show a = (a - b) + b by omega, ← toUInt64_add, UInt64.add_sub_cancel, Nat.add_sub_cancel]

theorem toUInt64_shl {a n : Nat} (hn : n < 64) (h : a * 2 ^ n < 2 ^ 64) :
    a.toUInt64 <<< n.toUInt64 = (a * 2 ^ n).toUInt64 := by
  have ha : a < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) h
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, toNat_toUInt64' ha, toNat_toUInt64' (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hn, toNat_toUInt64' h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toUInt64_shr {a n : Nat} (hn : n < 64) (ha : a < 2 ^ 64) :
    a.toUInt64 >>> n.toUInt64 = (a / 2 ^ n).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_toUInt64' ha, toNat_toUInt64' (by omega), Nat.mod_eq_of_lt hn,
    toNat_toUInt64' (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha), Nat.shiftRight_eq_div_pow]

theorem toUInt64_and_mask {a k : Nat} (hk : k < 64) (ha : a < 2 ^ 64) :
    a.toUInt64 &&& (2 ^ k - 1 : Nat).toUInt64 = (a % 2 ^ k).toUInt64 := by
  apply UInt64.toNat_inj.mp
  have hk' : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  rw [UInt64.toNat_and, toNat_toUInt64' ha, toNat_toUInt64' (by omega),
    toNat_toUInt64' (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha), Nat.and_two_pow_sub_one_eq_mod]

end Native.SphincsVerifier
