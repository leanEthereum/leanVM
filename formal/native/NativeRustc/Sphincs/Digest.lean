module

public import NativeRustc.Sphincs.Codeword

/-!
# `h_msg` and `digest_fields` are the statement's message digest

On the bytes of the key, the randomizer and the message, byte `p < 34` of `h_msg`'s 64 bytes is the
statement's `messageDigestByte` (`messageDigestByte_eq`); `digest_fields` reads the statement's
index (`digestFields_index`) and FORS leaves (`digestFields_leaves`) from them.
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig HashSig.OverPermutation LeanVM.Protocol.KeccakHash NativeRustc.Keccak
  Native.Keccak

/-- `H` over Keccak-f[1600] is the little-endian number of Keccak-256's bytes. -/
theorem keccakHash_eq (input : HashInput) :
    Id.run (keccakHash (m := Id) LeanVM.Semantics.keccakF1600 input) =
      BitVec.ofNat 256 (leNat (hashBytes input)) := by
  rw [keccakHash, Id.run_map]
  rfl

theorem length_hashBytes (input : HashInput) : (hashBytes input).length = 32 := by
  rw [hashBytes, show digestBytes (keccak256 input) = wordsBytes (keccak256 input).toList from rfl,
    Proof.length_wordsBytes]
  simp

/-- The bytes `h_msg` hashes for call `i`. -/
def hMsgInput (R : Randomizer) (pk : _root_.Sphincs.PublicKey) (msg : Message) (i : Nat) :
    HashInput :=
  littleEndianBytes 16 R ++ littleEndianBytes 16 pk.publicSeed ++ littleEndianBytes 16 pk.root ++
    littleEndianBytes 32 msg ++ bigEndianBytes 4 (BitVec.ofNat 32 i)

/-- `h_msg`'s two calls. -/
theorem hMsg_eq (R : Randomizer) (pk : _root_.Sphincs.PublicKey) (msg : Message) :
    hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root) (littleEndianBytes 32 msg) =
      hashBytes (hMsgInput R pk msg 0) ++ hashBytes (hMsgInput R pk msg 1) := by
  rw [hMsg, show List.range 2 = [0, 1] from rfl, List.flatMap_cons, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, be32_eq, be32_eq]
  rfl

/-- **Byte `p` of the digest** is byte `p` of `h_msg`. -/
theorem messageDigestByte_eq (pk : _root_.Sphincs.PublicKey) (R : Randomizer) (msg : Message)
    {p : Nat} (hp : p < 34) :
    messageDigestByte
        (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R msg)) p =
      ((hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
        (littleEndianBytes 32 msg)).getD p 0).toNat := by
  have h0 := leNat_lt (hashBytes (hMsgInput R pk msg 0))
  have h1 := leNat_lt (hashBytes (hMsgInput R pk msg 1))
  rw [length_hashBytes, show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num] at h0 h1
  have hcall : ∀ c : DigestCall, Id.run (Verification.messageDigestCall (m := Id)
      LeanVM.Semantics.keccakF1600 R pk.publicSeed pk.root msg c) =
      BitVec.ofNat 256 (leNat (hashBytes (hMsgInput R pk msg c.val))) :=
    fun c ↦ keccakHash_eq (hMsgInput R pk msg c.val)
  have hV : digestValue (fun call : DigestCall ↦ Id.run (Verification.messageDigestCall (m := Id)
      LeanVM.Semantics.keccakF1600 R pk.publicSeed pk.root msg call)) =
      leNat (hashBytes (hMsgInput R pk msg 0) ++ hashBytes (hMsgInput R pk msg 1)) := by
    rw [digestValue, leNat_append, length_hashBytes]
    simp only [hcall, BitVec.toNat_ofNat]
    change ∑ c : Fin 2, _ = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, pow_zero, Nat.mul_one]
    rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, show (256 : Nat) ^ 32 = 2 ^ 256 by norm_num]
    ring
  have hl : (hashBytes (hMsgInput R pk msg 0) ++ hashBytes (hMsgInput R pk msg 1)).length = 64 := by
    simp [length_hashBytes]
  simp only [Verification.messageDigest, Id.run_bind, Id.run_pure, Native.XmssVerifier.sequenceFin_id]
  rw [messageDigestByte, truncateMessageDigest, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, hV,
    hMsg_eq, Nat.shiftRight_eq_div_pow, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hl]; omega), Option.getD_some,
    ← leNat_div_mod _ (by rw [hl]; omega)]
  generalize leNat (hashBytes (hMsgInput R pk msg 0) ++ hashBytes (hMsgInput R pk msg 1)) = V
  rw [show 8 * digestByteCount = 8 * p + (272 - 8 * p) by unfold digestByteCount; omega, pow_add,
    Nat.mod_mul_right_div_self, show (256 : Nat) ^ p = 2 ^ (8 * p) by rw [pow_mul]; rfl]
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))

/-- `v << 1 | b` for a bit `b`. -/
theorem shift_or_bit (v : Nat) {b : Nat} (hb : b < 2) : v <<< 1 ||| b = 2 * v + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hb), Nat.shiftLeft_eq]
  ring

/-- Bits folded in, most significant first, fit their count. -/
theorem foldl_bits_lt (g : Nat → Nat) (hg : ∀ j, g j < 2) : ∀ n,
    (List.range n).foldl (fun v j ↦ 2 * v + g j) 0 < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, pow_succ]
    have := foldl_bits_lt g hg n
    have := hg n
    omega

/-- `digest_fields`' `bit` is the statement's. -/
theorem digestBit_eq (pk : _root_.Sphincs.PublicKey) (R : Randomizer) (msg : Message) {p : Nat}
    (hp : p < 272) :
    digestBit (hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
        (littleEndianBytes 32 msg)) p =
      messageDigestBit
        (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R msg)) p := by
  rw [digestBit, messageDigestBit, messageDigestByte_eq pk R msg (by omega)]
  generalize ((hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
    (littleEndianBytes 32 msg)).getD (p / 8) 0) = b
  have hk : (7 - p % 8 : Nat) < 8 := by omega
  rw [UInt8.toNat_and, UInt8.toNat_shiftRight, Nat.toUInt8_eq, UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : 7 - p % 8 < 2 ^ 8), Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  simp only [UInt8.reduceToNat, Nat.and_one_is_mod]

/-- **`digest_fields`' FORS leaves** are the statement's. -/
theorem digestFields_leaves (pk : _root_.Sphincs.PublicKey) (R : Randomizer) (msg : Message) :
    (digestFields (hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
        (littleEndianBytes 32 msg))).2 =
      List.ofFn fun c : ForsTreeIndex ↦ (digestForsLeaves
        (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R msg)) c).val := by
  apply List.ext_getElem (by
    simp only [digestFields, List.length_map, List.length_range, List.length_ofFn]; rfl)
  intro c h1 h2
  have hc : c < 24 := by simpa [digestFields] using h1
  rw [List.getElem_ofFn]
  simp only [digestFields, List.getElem_map, List.getElem_range, digestForsLeaves, forsLeafOfNat,
    forsTreeHeight]
  have hbit : ∀ j, messageDigestBit (Id.run (Verification.messageDigest (m := Id)
      LeanVM.Semantics.keccakF1600 pk R msg)) j < 2 := fun j ↦ Nat.mod_lt _ (by omega)
  rw [List.foldl_ext _ (fun v j ↦ 2 * v + messageDigestBit (Id.run (Verification.messageDigest
      (m := Id) LeanVM.Semantics.keccakF1600 pk R msg)) (10 * c + j)) 0 ?_]
  · exact (Nat.mod_eq_of_lt (foldl_bits_lt _ (fun j ↦ hbit _) 10)).symm
  · intro v j hj
    rw [List.mem_range] at hj
    rw [digestBit_eq pk R msg (by omega), shift_or_bit _ (hbit _)]

/-- `v << 8 | b` in a `u64` that does not overflow. -/
theorem shift_or_byte (v : UInt64) (b : UInt8) (hv : v.toNat < 2 ^ 56) :
    (v <<< 8 ||| b.toUInt64).toNat = 256 * v.toNat + b.toNat := by
  have hb : b.toNat < 2 ^ 8 := b.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm, lor_eq_add hb (Dvd.intro_left _ rfl)]
  omega

/-- **`digest_fields`' index** is the statement's. -/
theorem digestFields_index (pk : _root_.Sphincs.PublicKey) (R : Randomizer) (msg : Message) :
    (digestFields (hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
        (littleEndianBytes 32 msg))).1.toNat =
      (digestIndex
        (Id.run (Verification.messageDigest (m := Id) LeanVM.Semantics.keccakF1600 pk R msg))).val := by
  generalize hh : hMsg (le16 R) (littleEndianBytes 16 pk.publicSeed) (le16 pk.root)
    (littleEndianBytes 32 msg) = hm
  have hl : hm.length = 64 := by rw [← hh, hMsg_eq]; simp [length_hashBytes]
  have hb : ∀ p (hp : p < 34), messageDigestByte (Id.run (Verification.messageDigest (m := Id)
      LeanVM.Semantics.keccakF1600 pk R msg)) p = (hm[p]'(by omega)).toNat := fun p hp ↦ by
    rw [messageDigestByte_eq pk R msg hp, hh, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hs3 : slice hm 30 3 = [hm[30], hm[31], hm[32]] := by
    apply List.ext_getElem (by simp [slice]; omega)
    intro i h1 h2
    have : i < 3 := by simpa using h2
    interval_cases i <;> simp [slice]
  have hs1 : slice hm 33 1 = [hm[33]] := by
    apply List.ext_getElem (by simp [slice]; omega)
    intro i h1 h2
    have : i < 1 := by simpa using h2
    interval_cases i
    simp [slice]
  have h30 := hm[30].toNat_lt
  have h31 := hm[31].toNat_lt
  have h32 := hm[32].toNat_lt
  have h33 := hm[33].toNat_lt
  have e1 := shift_or_byte 0 hm[30] (by simp)
  have e2 := shift_or_byte ((0 : UInt64) <<< 8 ||| hm[30].toUInt64) hm[31]
    (by rw [e1]; simp; omega)
  have e3 := shift_or_byte (((0 : UInt64) <<< 8 ||| hm[30].toUInt64) <<< 8 ||| hm[31].toUInt64)
    hm[32] (by rw [e2, e1]; simp; omega)
  have e4 := shift_or_byte 0 hm[33] (by simp)
  have htree : (digestInt (slice hm 30 3) 18).toNat =
      ((hm[30].toNat * 256 + hm[31].toNat) * 256 + hm[32].toNat) % 2 ^ 18 := by
    rw [digestInt, hs3]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [UInt64.toNat_and, e3, e2, e1,
      show ((1 : UInt64) <<< (18 : Nat).toUInt64 - 1).toNat = 2 ^ 18 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add]
    congr 1
    ring
  have hleaf : (digestInt (slice hm 33 1) 8).toNat = hm[33].toNat := by
    rw [digestInt, hs1]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [UInt64.toNat_and, e4,
      show ((1 : UInt64) <<< (8 : Nat).toUInt64 - 1).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add]
    omega
  have hbe3 : ∀ d : MessageDigest, messageDigestBigEndian d 30 3 =
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
  rw [digestFields, digestIndex]
  simp only [forsMessageByteCount, treeIndexByteCount, leafIndexByteCount, Nat.reduceAdd, hbe3,
    hbe1, hb 30 (by decide), hb 31 (by decide), hb 32 (by decide), hb 33 (by decide)]
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, htree, hleaf]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    lor_eq_add (n := 8) (by omega) (Dvd.intro_left _ rfl)]
  omega

end NativeRustc.Sphincs
