module

public import NativeRustc.Sphincs.Model
public import NativeRustc.Digest

/-!
# The encoding as the machine code computes it

Facts the AArch64 and x86-64 proofs of the encoding share: `encode` from the digits of the
digest's big-endian number (`encode_eq`); a digit as the codeword's loops compute it
(`digitByte`, `digits_eq`, `getElem_digits`), the digits' sum bounded (`sum_digits_le`); a
literal insertion sort (`isort`, `perm_isort`) that the kernel runs to recognize the 64 digits'
loads in a sum; the encoder's address as the bytes the code stores (`adrs7_eq`); the big-endian
number of two 8-byte halves (`beNat_append8`).
-/

@[expose] public section

namespace NativeRustc.Sphincs

/-- Digit `t` of the 128-bit number `V`, as the codeword's loops store it. -/
def digitByte (V t : Nat) : UInt8 := UInt8.ofNat (V >>> (126 - 2 * t) % 4)

theorem length_digits (V : Nat) : (digits V).length = 64 := by simp [digits]

/-- `digits`' element `i`. -/
theorem getElem_digits (V : Nat) {i : Nat} (hi : i < 64) :
    (digits V)[i]'(by rw [length_digits]; exact hi) = digitByte V i := by
  simp only [digits, List.getElem_map, List.getElem_range, digitByte]
  rw [show 2 * (63 - i) = 126 - 2 * i by omega, show (3 : Nat) = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem digits_eq (V : Nat) : digits V = (List.range 64).map (digitByte V) := by
  apply List.ext_getElem (by simp [length_digits])
  intro i h1 h2
  rw [getElem_digits V (by rw [length_digits] at h1; exact h1)]
  simp

theorem digitByte_le (V t : Nat) : (digitByte V t).toNat ≤ 3 := by
  simp only [digitByte, UInt8.toNat_ofNat']
  omega

theorem sum_digits_le (V : Nat) : ((digits V).map UInt8.toNat).sum ≤ 192 := by
  rw [digits_eq, List.map_map]
  have : ∀ n, ((List.range n).map (UInt8.toNat ∘ digitByte V)).sum ≤ 3 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp]
      have := digitByte_le V n
      omega
  exact this 64

/-- `encode` from the digits of the digest's big-endian number. -/
theorem encode_eq (seed : List UInt8) (key : OtsKey) (s : List UInt8) (c : UInt32) :
    encode seed key s c =
      let V := beNat (encodeDigest seed key s c)
      if ((digits V).map UInt8.toNat).sum = 128 then some (digits V) else none := rfl

/-! ## A sort the kernel runs -/

/-- Insertion into a sorted list. -/
def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: ins a l

/-- Insertion sort. -/
def isort : List Nat → List Nat
  | [] => []
  | a :: l => ins a (isort l)

theorem perm_ins (a : Nat) : ∀ l, (ins a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    unfold ins
    split
    · exact List.Perm.refl _
    · exact ((perm_ins a l).cons b).trans (List.Perm.swap a b l)

theorem perm_isort : ∀ l, (isort l).Perm l
  | [] => List.Perm.refl _
  | a :: l => (perm_ins a (isort l)).trans ((perm_isort l).cons a)

/-! ## The encoder's address -/

/-- **The encoder's address** (`OtsKey::adrs(WOTS_PRF)`, type 7): the layer, four zeros, the tree,
the type, the key pair, eight zeros. -/
theorem adrs7_eq (key : OtsKey) :
    key.adrs 7 = be32 key.layer.toUInt32 ++ [0, 0, 0, 0] ++ be64 key.tree ++ be32 7 ++
      be32 key.leaf ++ List.replicate 8 0 := by
  simp [OtsKey.adrs, OtsKey.treeAdrs, withKeyPair, withType, adrsWord, adrsNew, writeAt, be32,
    be64]

theorem length_adrs7 (key : OtsKey) : (key.adrs 7).length = 32 := by
  rw [adrs7_eq]
  simp [be32, be64]

/-! ## Big-endian numbers -/

/-- The big-endian number of two 8-byte halves. -/
theorem beNat_append8 (A B : List UInt8) (hB : B.length = 8) :
    beNat (A ++ B) = beNat A * 2 ^ 64 + beNat B := by
  rw [beNat, beNat, beNat, List.reverse_append, leNat_append, List.length_reverse, hB,
    show (256 : Nat) ^ 8 = 2 ^ 64 by norm_num]
  ring

end NativeRustc.Sphincs
