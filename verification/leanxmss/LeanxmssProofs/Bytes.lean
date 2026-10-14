import LeanxmssProofs.Statement

/-!
# Bytes of words
-/

open Aeneas Aeneas.Std

namespace leanxmss.Bytes

@[simp] theorem le_length (n x : Nat) : (le n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [le, ih]

@[simp] theorem ofWords_length (ws : List U64) : (ofWords ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ofWords, List.flatMap_cons] at *; omega

@[simp] theorem ofWords_nil : ofWords [] = [] := rfl

theorem ofWords_cons (w : U64) (ws : List U64) : ofWords (w :: ws) = le 8 w.val ++ ofWords ws := by
  simp [ofWords]

@[simp] theorem ofWords_append (a b : List U64) : ofWords (a ++ b) = ofWords a ++ ofWords b := by
  simp [ofWords, List.flatMap_append]

@[simp] theorem toNat_nil : toNat [] = 0 := rfl

@[simp] theorem toNat_cons (b : UInt8) (bs : List UInt8) : toNat (b :: bs) = b.toNat + 256 * toNat bs := rfl

theorem toNat_lt (bs : List UInt8) : toNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have := b.toNat_lt
    simp [pow_succ]
    omega

theorem uint8_ofNat_add (b : UInt8) (r : Nat) : UInt8.ofNat (b.toNat + 256 * r) = b := by
  apply UInt8.toNat_inj.mp
  simp

theorem le_toNat (bs : List UInt8) : le bs.length (toNat bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have := b.toNat_lt
    simp only [List.length_cons, le, toNat_cons, uint8_ofNat_add, List.cons.injEq, true_and]
    have : (b.toNat + 256 * toNat bs) / 256 = toNat bs := by omega
    rw [this, ih]

theorem toNat_le (n x : Nat) (h : x < 256 ^ n) : toNat (le n x) = x := by
  induction n generalizing x with
  | zero => simp at h; simp [le]; omega
  | succ n ih =>
    simp only [le, toNat_cons, UInt8.toNat_ofNat']
    rw [ih (x / 256) (by rw [pow_succ] at h; omega)]
    omega

/-- The bytes of a natural number below `2^64` determine its word. -/
theorem le_eq_iff {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n) : le n x = le n y ↔ x = y := by
  constructor
  · intro h; rw [← toNat_le n x hx, ← toNat_le n y hy, h]
  · rintro rfl; rfl

theorem val_lt (w : U64) : w.val < 256 ^ 8 := by
  have := w.hBounds; simpa using this

theorem word_val (bs : List UInt8) : (word bs).val = toNat (bs.take 8) % 2 ^ 64 := by
  simp only [word, UScalar.val]; show (BitVec.ofNat 64 _).toNat = _; simp

@[simp] theorem word_le (w : U64) (rest : List UInt8) : word (le 8 w.val ++ rest) = w := by
  simp only [word, List.take_left' (le_length 8 w.val)]
  rw [toNat_le 8 w.val (val_lt w)]
  rcases w with ⟨bv⟩
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [UScalar.val]

theorem le_word (bs : List UInt8) (h : 8 ≤ bs.length) : le 8 (word bs).val = bs.take 8 := by
  have hl : (bs.take 8).length = 8 := by simp; omega
  have hlt := toNat_lt (bs.take 8)
  rw [hl] at hlt
  rw [word_val, Nat.mod_eq_of_lt (by simpa using hlt)]
  conv => rhs; rw [← le_toNat (bs.take 8), hl]

theorem le_inj {w v : U64} (h : le 8 w.val = le 8 v.val) : w = v := by
  have := word_le w []; have := word_le v []
  simp only [List.append_nil] at *
  rw [← word_le w [], ← word_le v [], List.append_nil, List.append_nil, h]

theorem ofWords_inj {ws vs : List U64} (h : ofWords ws = ofWords vs) (hl : ws.length = vs.length) : ws = vs := by
  induction ws generalizing vs with
  | nil => cases vs <;> simp_all
  | cons w ws ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [ofWords_cons] at h
      have h8 := List.append_inj h (by simp)
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      rw [le_inj h8.1, ih h8.2 hl]

/-- Splicing bytes over a list keeps its length when they fit. -/
@[simp] theorem splice_length (bs : List UInt8) (pos : Nat) (xs : List UInt8) (h : pos + xs.length ≤ bs.length) :
    (splice bs pos xs).length = bs.length := by
  simp [splice]; omega

/-- Splicing over the boundary of `a ++ b` where the bytes land in `a`. -/
theorem splice_append_left (a b xs : List UInt8) (pos : Nat) (h : pos + xs.length ≤ a.length) :
    splice (a ++ b) pos xs = splice a pos xs ++ b := by
  simp only [splice, List.take_append_of_le_length (by omega : pos ≤ a.length)]
  rw [List.drop_append_of_le_length (by omega)]
  simp

/-- Splicing where the bytes land in `b`. -/
theorem splice_append_right (a b xs : List UInt8) (pos : Nat) (h : a.length ≤ pos) :
    splice (a ++ b) pos xs = a ++ splice b (pos - a.length) xs := by
  simp only [splice, List.take_append, List.drop_append]
  rw [List.take_of_length_le (by omega), List.drop_of_length_le (by omega)]
  simp only [List.nil_append, List.append_assoc]
  rw [show pos + xs.length - a.length = pos - a.length + xs.length by omega]

/-- Splicing exactly over a part. -/
theorem splice_exact (a b c xs : List UInt8) (h : xs.length = b.length) :
    splice (a ++ b ++ c) a.length xs = a ++ xs ++ c := by
  simp [splice, h]

end leanxmss.Bytes

namespace leanxmss.Statement

open Bytes

theorem bytes_toList {n : Std.Usize} (ws : Std.Array U64 n) (m : Nat) (h : m = 8 * n.val) :
    (bytes ws m).toList = ofWords ws.val := by
  apply List.ext_getElem
  · simp [bytes, h]
  · intro i h1 h2
    simp only [bytes, Vector.toList_ofFn, List.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem bytes_inj {n : Std.Usize} {ws vs : Std.Array U64 n} {m : Nat} (h : m = 8 * n.val)
    (e : bytes ws m = bytes vs m) : ws = vs := by
  have := congrArg Vector.toList e
  rw [bytes_toList ws m h, bytes_toList vs m h] at this
  apply Std.Array.ext
  exact ofWords_inj this (by simp)

end leanxmss.Statement
