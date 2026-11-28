module

public import Native.Sphincs.Hash
public import Mathlib.Tactic.Ring

/-!
# The message digest as words

`H_msg`'s two calls hash `mdWords` (`messageDigestCall_eq`), and byte `j` of the digest is byte
`j mod 8` of the calls' lane `j / 8` (`messageDigestByte_eq`), from which the index and the FORS
leaves are read (`digestIndex_val`, `digestForsLeaves_val`).
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-- `sequenceFin` in `Id` runs each computation. -/
theorem sequenceFin_id {α : Type} : ∀ {n : Nat} (f : Fin n → Id α),
    Id.run (sequenceFin f) = fun i ↦ Id.run (f i)
  | 0, _ => funext fun i ↦ i.elim0
  | n + 1, f => by
    funext i
    have ih := sequenceFin_id fun j : Fin n ↦ f j.succ
    simp only [sequenceFin, Id.run_bind, Id.run_pure] at ih ⊢
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact congrFun ih j

/-- The words both digest calls start with: `R ‖ PK.seed ‖ PK.root ‖ M`. -/
def mdHead (R seed root : BitVec 128) (m : BitVec 256) : List UInt64 :=
  [digestLo R, digestHi R, digestLo seed, digestHi seed, digestLo root, digestHi root] ++
    (List.range 4).map (word256 m)

/-- The words of digest call `c`: `R ‖ PK.seed ‖ PK.root ‖ M ‖ BE_32(c)`. -/
def mdWords (R seed root : BitVec 128) (m : BitVec 256) (c : Nat) : List UInt64 :=
  mdHead R seed root m ++ [c.toUInt64 <<< 24]

theorem mdWords_bytes (R seed root : BitVec 128) (m : BitVec 256) {c : Nat} (hc : c < 2) :
    (wordsBytes (mdWords R seed root m c)).take 84 =
      littleEndianBytes 16 R ++ littleEndianBytes 16 seed ++ littleEndianBytes 16 root ++
        littleEndianBytes 32 m ++ bigEndianBytes 4 (BitVec.ofNat 32 c) := by
  have h80 : (wordsBytes ([digestLo R, digestHi R, digestLo seed, digestHi seed, digestLo root,
      digestHi root] ++ (List.range 4).map (word256 m))).length = 80 := by
    rw [wordsBytes_length]; simp
  rw [mdWords, mdHead, wordsBytes_append, List.take_append, h80, List.take_of_length_le (by omega),
    littleEndianBytes_16, littleEndianBytes_16, littleEndianBytes_16, littleEndianBytes_32,
    show [digestLo R, digestHi R, digestLo seed, digestHi seed, digestLo root, digestHi root] =
      [digestLo R, digestHi R] ++ [digestLo seed, digestHi seed] ++ [digestLo root, digestHi root]
      from rfl, wordsBytes_append, wordsBytes_append, wordsBytes_append]
  simp only [List.append_assoc, List.append_cancel_left_eq]
  interval_cases c <;> rfl

/-- Digest call `c`'s lanes. -/
def mdLanes (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) (c : Nat) :
    LeanVM.Protocol.Digest :=
  keccak256 ((wordsBytes (mdWords R pk.publicSeed pk.root m c)).take 84)

/-- Lane `k mod 4` of digest call `k / 4`. -/
def mdLane (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) (k : Nat) : UInt64 :=
  (mdLanes pk R m (k / 4))[k % 4]'(Nat.mod_lt _ (by decide))

theorem messageDigestCall_eq (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256)
    (c : DigestCall) :
    Id.run (Verification.messageDigestCall (m := Id) LeanVM.Semantics.keccakF1600 R pk.publicSeed pk.root m c) =
      BitVec.ofNat 256 (∑ i : Fin 4, (mdLanes pk R m c)[i].toNat * 2 ^ (64 * i.val)) := by
  unfold Verification.messageDigestCall mdLanes
  rw [← mdWords_bytes R pk.publicSeed pk.root m c.isLt]
  exact keccakHash_keccakF _

theorem testBit_horner_lt {a b i : Nat} (hb : b < 2 ^ 64) (hi : i < 64) :
    (b + 2 ^ 64 * a).testBit i = b.testBit i := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add a hb, ite_yes hi]

theorem testBit_horner_ge {a b i : Nat} (hb : b < 2 ^ 64) (hi : 64 ≤ i) :
    (b + 2 ^ 64 * a).testBit i = a.testBit (i - 64) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add a hb, ite_no (by omega)]

theorem byte_testBit (n s : Nat) (i : Nat) :
    (n / 2 ^ s % 256).testBit i = (decide (i < 8) && n.testBit (s + i)) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.add_comm i s]

/-- Byte `j` of the digest calls' lanes. -/
def mdByte (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) (j : Nat) : Nat :=
  (mdLane pk R m (j / 8)).toNat / 2 ^ (8 * (j % 8)) % 256

theorem mdByte_lt (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) (j : Nat) :
    mdByte pk R m j < 256 := Nat.mod_lt _ (by decide)

/-- **Byte `j` of the digest** is byte `j mod 8` of lane `j / 8`. -/
theorem messageDigestByte_eq (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256)
    {j : Nat} (hj : j < 34) :
    messageDigestByte (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R m)) j =
      mdByte pk R m j := by
  unfold mdByte
  simp only [Verification.messageDigest, Id.run_bind, Id.run_pure, sequenceFin_id, messageDigestCall_eq]
  set L := mdLane pk R m with hL
  have hl : ∀ k, (L k).toNat < 2 ^ 64 := fun k ↦ (L k).toNat_lt
  have hlanes : ∀ c (i : Fin 4), (mdLanes pk R m c)[i] = L (4 * c + i.val) := by
    intro c i
    obtain ⟨i, hi⟩ := i
    simp only [hL, mdLane, show (4 * c + i) / 4 = c by omega, show (4 * c + i) % 4 = i by omega]
    rfl
  have hN : digestValue (fun c : DigestCall ↦
      BitVec.ofNat 256 (∑ i : Fin 4, (mdLanes pk R m c)[i].toNat * 2 ^ (64 * i.val))) =
      (L 0).toNat + 2 ^ 64 * ((L 1).toNat + 2 ^ 64 * ((L 2).toNat + 2 ^ 64 * ((L 3).toNat +
        2 ^ 64 * ((L 4).toNat + 2 ^ 64 * ((L 5).toNat + 2 ^ 64 * ((L 6).toNat +
          2 ^ 64 * (L 7).toNat)))))) := by
    unfold digestValue
    change ∑ c : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp only [Fin.sum_univ_four, hlanes, BitVec.toNat_ofNat]
    have := hl 0; have := hl 1; have := hl 2; have := hl 3
    have := hl 4; have := hl 5; have := hl 6; have := hl 7
    simp only [Fin.val_zero, Fin.val_one, Fin.isValue, Fin.val_two,
      show ((3 : Fin 4) : Nat) = 3 from rfl, Nat.reduceAdd, Nat.reduceMul]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    ring
  rw [messageDigestByte, truncateMessageDigest, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, hN,
    Nat.shiftRight_eq_div_pow]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [byte_testBit, byte_testBit]
  rcases Nat.lt_or_ge i 8 with hi | hi
  · simp only [hi, decide_true, Bool.true_and]
    rw [Nat.testBit_mod_two_pow, decide_eq_true (by unfold digestByteCount; omega),
      Bool.true_and]
    obtain ⟨q, r, rfl, hr⟩ : ∃ q r, j = 8 * q + r ∧ r < 8 := ⟨j / 8, j % 8, by omega, by omega⟩
    rw [show (8 * q + r) / 8 = q by omega, show (8 * q + r) % 8 = r by omega]
    have hq : q < 5 := by omega
    clear hN hlanes
    interval_cases q
    · rw [testBit_horner_lt (hl 0) (by omega)]
      exact congrArg _ (by omega)
    · rw [testBit_horner_ge (hl 0) (by omega), testBit_horner_lt (hl 1) (by omega)]
      exact congrArg _ (by omega)
    · rw [testBit_horner_ge (hl 0) (by omega), testBit_horner_ge (hl 1) (by omega),
        testBit_horner_lt (hl 2) (by omega)]
      exact congrArg _ (by omega)
    · rw [testBit_horner_ge (hl 0) (by omega), testBit_horner_ge (hl 1) (by omega),
        testBit_horner_ge (hl 2) (by omega), testBit_horner_lt (hl 3) (by omega)]
      exact congrArg _ (by omega)
    · rw [testBit_horner_ge (hl 0) (by omega), testBit_horner_ge (hl 1) (by omega),
        testBit_horner_ge (hl 2) (by omega), testBit_horner_ge (hl 3) (by omega),
        testBit_horner_lt (hl 4) (by omega)]
      exact congrArg _ (by omega)
  · simp [show ¬i < 8 by omega]

/-- **The index**: bytes `30` to `32` big-endian cut to 18 bits, then byte `33`. -/
theorem digestIndex_val (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256) :
    (_root_.Sphincs.digestIndex (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R m))).val =
      ((mdByte pk R m 30 * 256 + mdByte pk R m 31) * 256 + mdByte pk R m 32) % 2 ^ 18 * 256 +
        mdByte pk R m 33 := by
  have hbe : ∀ d : MessageDigest, messageDigestBigEndian d 30 3 =
      (messageDigestByte d 30 * 256 + messageDigestByte d 31) * 256 + messageDigestByte d 32 := by
    intro d
    simp only [messageDigestBigEndian, show List.range 3 = [0, 1, 2] from rfl, List.foldl_cons,
      List.foldl_nil, Nat.add_zero, Nat.reduceAdd]
    omega
  have hbe1 : ∀ d : MessageDigest, messageDigestBigEndian d 33 1 = messageDigestByte d 33 := by
    intro d
    simp only [messageDigestBigEndian, show List.range 1 = [0] from rfl, List.foldl_cons,
      List.foldl_nil, Nat.add_zero]
    omega
  simp only [_root_.Sphincs.digestIndex, forsMessageByteCount, treeIndexByteCount,
    leafIndexByteCount, Nat.reduceAdd, hbe, hbe1,
    messageDigestByte_eq pk R m (show 30 < 34 by decide),
    messageDigestByte_eq pk R m (show 31 < 34 by decide),
    messageDigestByte_eq pk R m (show 32 < 34 by decide),
    messageDigestByte_eq pk R m (show 33 < 34 by decide)]
  have := mdByte_lt pk R m 33
  omega

/-- The bits of a number, most significant first: the `n` bits below bit `m + 1`. -/
theorem div_mod_two_eq {x y e f : Nat} (h : x.testBit e = y.testBit f) :
    x / 2 ^ e % 2 = y / 2 ^ f % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at h
  have := Nat.mod_two_eq_zero_or_one (x / 2 ^ e)
  have := Nat.mod_two_eq_zero_or_one (y / 2 ^ f)
  simp only [decide_eq_decide] at h
  omega

theorem foldl_bits (Y m : Nat) : ∀ n, n ≤ m + 1 →
    (List.range n).foldl (fun v j ↦ 2 * v + Y / 2 ^ (m - j) % 2) 0 = Y / 2 ^ (m + 1 - n) % 2 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_bits Y m n (by omega), List.foldl_cons,
      List.foldl_nil, show m + 1 - n = (m - n) + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul,
      show m + 1 - (n + 1) = m - n by omega, Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mod_mul]
    omega

/-- **FORS tree `κ`'s leaf**: the bits from bit `10 κ` of bytes `⌊10 κ / 8⌋` and the next. -/
theorem digestForsLeaves_val (pk : _root_.Sphincs.PublicKey) (R : BitVec 128) (m : BitVec 256)
    (κ : ForsTreeIndex) :
    (digestForsLeaves (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R m))
      κ).val =
      (mdByte pk R m (10 * κ.val / 8) * 256 + mdByte pk R m (10 * κ.val / 8 + 1)) /
        2 ^ (6 - 10 * κ.val % 8) % 1024 := by
  have hκ := κ.isLt
  unfold forsTreeCount at hκ
  set Y := mdByte pk R m (10 * κ.val / 8) * 256 + mdByte pk R m (10 * κ.val / 8 + 1)
  have hbits : ∀ j < 10, messageDigestBit
      (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R m))
      (forsTreeHeight * κ.val + j) = Y / 2 ^ (15 - 10 * κ.val % 8 - j) % 2 := by
    intro j hj
    unfold messageDigestBit
    rw [messageDigestByte_eq pk R m (by unfold forsTreeHeight; omega)]
    have hb0 := mdByte_lt pk R m (10 * κ.val / 8)
    have hb1 := mdByte_lt pk R m (10 * κ.val / 8 + 1)
    unfold forsTreeHeight
    rw [show 7 = 15 - 8 by rfl]
    apply div_mod_two_eq
    rw [show Y = 2 ^ 8 * mdByte pk R m (10 * κ.val / 8) + mdByte pk R m (10 * κ.val / 8 + 1)
      by simp only [Y]; omega, Nat.testBit_two_pow_mul_add _ hb1]
    rcases Nat.lt_or_ge (10 * κ.val % 8 + j) 8 with ho | ho
    · rw [ite_no (by omega), show (10 * κ.val + j) / 8 = 10 * κ.val / 8 by omega]
      exact congrArg _ (by omega)
    · rw [ite_yes (by omega), show (10 * κ.val + j) / 8 = 10 * κ.val / 8 + 1 by omega]
      exact congrArg _ (by omega)
  simp only [digestForsLeaves, forsLeafOfNat, forsTreeHeight]
  rw [List.foldl_ext _ (fun v j ↦ 2 * v + Y / 2 ^ ((15 - 10 * κ.val % 8) - j) % 2) 0 ?_]
  · rw [foldl_bits Y _ 10 (by omega), show 15 - 10 * κ.val % 8 + 1 - 10 = 6 - 10 * κ.val % 8 by omega]
    simp
  · intro v j hj
    rw [List.mem_range] at hj
    have := hbits j hj
    unfold forsTreeHeight at this
    rw [this, Nat.sub_sub]

end Native.SphincsVerifier
