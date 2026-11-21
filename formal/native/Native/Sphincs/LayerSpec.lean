module

public import Native.Sphincs.DigestSpec
public import Native.Sphincs.Layout

/-!
# The layers' specification

A codeword's digit is two bits of a word of the encoding hash (`base2bDigits_val`); the encoding's
payload is the message's two words and the counter's big-endian bytes (`encPayload_take`); in `Id`,
a one-time leaf is the encoding's test then the leaf hash of the chains (`otsLeaf_id`), the layers
are three `layerRoot`s (`verifyLayers_id`), and `verifyWithKeccak` is the digest, FORS, the layers
and the comparison (`verifyWithKeccak_eq`).
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-! ## The digits -/

/-- **Digit `i` of a codeword**: bits `8 ⌊i/4⌋ + 6 - 2 (i mod 4)` of the digest, two bits of its
word `⌊i/32⌋`. -/
theorem base2bDigits_val (d : Digest) (i : ChainIndex) :
    (TargetSum.base2bDigits d i).val =
      (digestWord d (i.val / 32)).toNat / 2 ^ ((8 * (i.val / 4) + 6 - 2 * (i.val % 4)) % 64) % 4 := by
  obtain ⟨i, hi⟩ := i
  unfold chainCount at hi
  have hw : (digestWord d (i / 32)).toNat = d.toNat / 2 ^ (64 * (i / 32)) % 2 ^ 64 := by
    unfold digestWord digestLo digestHi
    split
    · rename_i h; simp only [h, Nat.mul_zero, Nat.pow_zero, Nat.div_one, UInt64.toNat_ofNat']; rfl
    · rw [show i / 32 = 1 by omega]; simp only [UInt64.toNat_ofNat']; rfl
  simp only [TargetSum.base2bDigits, winternitzBits, BitVec.val_toFin, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, hw]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rcases Nat.lt_or_ge j 2 with hj | hj
  · simp only [hj, decide_true, Bool.true_and]
    rw [decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · simp [show ¬j < 2 by omega]

/-! ## The encoding's payload -/

/-- `be32`'s word: the big-endian bytes of the low 32 bits, then zeros. -/
theorem wordBytes_bs_zero (x : UInt64) :
    wordBytes (bs x) = bigEndianBytes 4 (BitVec.ofNat 32 x.toNat) ++ [0, 0, 0, 0] := by
  have := wordBytes_bs x 0
  rw [bs_zero, show (0 : UInt64) <<< 32 = 0 from rfl, UInt64.or_zero] at this
  rw [this]
  rfl

/-- The message's 16 bytes, then the counter's 4, big-endian. -/
theorem encPayload_take (msg : Digest) (c : EncodingCounter) :
    (wordsBytes [digestLo msg, digestHi msg, bs c.toNat.toUInt64]).take 20 =
      littleEndianBytes 16 msg ++ bigEndianBytes 4 c := by
  have hl : wordsBytes [digestLo msg, digestHi msg] = littleEndianBytes 16 msg :=
    (littleEndianBytes_16 msg).symm
  have hc : BitVec.ofNat 32 c.toNat.toUInt64.toNat = c := by
    rw [toNat_toUInt64 (Nat.lt_trans c.isLt (by decide)), BitVec.ofNat_toNat]
    exact BitVec.setWidth_eq c
  rw [show [digestLo msg, digestHi msg, bs c.toNat.toUInt64] =
    [digestLo msg, digestHi msg] ++ [bs c.toNat.toUInt64] from rfl, wordsBytes_append,
    hl, wordsBytes_cons, wordBytes_bs_zero, hc, List.take_append]
  simp [littleEndianBytes, bigEndianBytes, wordsBytes]

/-- Nothing past the counter. -/
theorem encPayload_drop (msg : Digest) (c : EncodingCounter) :
    ∀ b ∈ (wordsBytes [digestLo msg, digestHi msg, bs c.toNat.toUInt64]).drop 20, b = 0 := by
  have hl : wordsBytes [digestLo msg, digestHi msg] = littleEndianBytes 16 msg :=
    (littleEndianBytes_16 msg).symm
  rw [show [digestLo msg, digestHi msg, bs c.toNat.toUInt64] =
    [digestLo msg, digestHi msg] ++ [bs c.toNat.toUInt64] from rfl, wordsBytes_append,
    hl, wordsBytes_cons, wordBytes_bs_zero, List.drop_append]
  simp [littleEndianBytes, bigEndianBytes, wordsBytes]

/-! ## A one-time leaf, in `Id` -/

/-- The encoding hash of `msg` under counter `c`. -/
def encDigest (seed : PublicParameter) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (msg : Digest) (c : EncodingCounter) : Digest :=
  Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
    (makeAddress L.val tree.val .wotsEncoding leaf.val 0 0)
    (littleEndianBytes 16 msg ++ bigEndianBytes 4 c))

/-- **The one-time leaf**: if the encoding is a codeword, the leaf hash of the chains walked from
its digits to their ends. -/
theorem otsLeaf_id (seed : PublicParameter) (L : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (msg : Digest) (c : EncodingCounter) (vals : ChainIndex → Digest) :
    Id.run (Verification.otsLeaf (m := Id) LeanVM.Semantics.keccakF1600 seed L tree leaf msg c
      vals) =
      if TargetSum.sum (TargetSum.base2bDigits (encDigest seed L tree leaf msg c)) = 128 then
        some (Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
          (makeAddress L.val tree.val .wotsPublicKey leaf.val 0 0)
          (digestsPayload fun i ↦ Id.run (Verification.chainWalk (m := Id)
            LeanVM.Semantics.keccakF1600 seed L tree leaf i
            (TargetSum.base2bDigits (encDigest seed L tree leaf msg c) i).val
            (3 - (TargetSum.base2bDigits (encDigest seed L tree leaf msg c) i).val) (vals i)))))
      else none := by
  have he : Id.run (Verification.tweakableHash (m := Id) LeanVM.Semantics.keccakF1600 seed
      (.encoding L tree leaf) (littleEndianBytes 16 msg ++ bigEndianBytes 4 c)) =
      encDigest seed L tree leaf msg c := rfl
  simp only [Verification.otsLeaf, Verification.encode, Id.run_bind, Id.run_pure, he,
    TargetSum.decodeDigest, TargetSum.Valid, targetSum]
  by_cases h : TargetSum.sum (TargetSum.base2bDigits (encDigest seed L tree leaf msg c)) = 128
  · simp only [h, ite_true, Id.run_bind, Id.run_pure, sequenceFin_id]
    rfl
  · simp only [h, ite_false]
    rfl

/-! ## The layers, in `Id` -/

/-- Layer `L`'s root above `d`: its key's one-time leaf of `d`, folded up its path, or `none` when
the counter gives no codeword. -/
def layerRoot (seed : PublicParameter) (idx : Index) (sig : Signature) (L : Layer) (d : Digest) :
    Option Digest :=
  (Id.run (Verification.otsLeaf (m := Id) LeanVM.Semantics.keccakF1600 seed L (treeOfIndex L idx)
    (leafOfIndex L idx) d (sig.layers L).counter (sig.layers L).chainValues)).map fun v ↦
      Id.run (Verification.treeFold (m := Id) LeanVM.Semantics.keccakF1600 seed L
        (treeOfIndex L idx) (leafOfIndex L idx) (Verification.layerPath sig L) (layerHeight L) v)

/-- One layer of `verifyLayers`, from the bottom. -/
theorem verifyLayers_succ_id (seed : PublicParameter) (idx : Index) (sig : Signature) {k : Nat}
    (hk : k < layerCount) (x : Digest) :
    Id.run (Verification.verifyLayers (m := Id) LeanVM.Semantics.keccakF1600 seed idx sig (k + 1) x) =
      (layerRoot seed idx sig ⟨layerCount - 1 - k, by omega⟩ x).bind fun r ↦
        if k = 0 then some r
        else Id.run (Verification.verifyLayers (m := Id) LeanVM.Semantics.keccakF1600 seed idx sig k r) := by
  rw [Verification.verifyLayers]
  simp only [hk, ↓reduceDIte]
  simp only [Id.run_bind, layerRoot]
  cases Id.run (Verification.otsLeaf (m := Id) LeanVM.Semantics.keccakF1600 seed
    ⟨layerCount - 1 - k, by omega⟩ _ _ x _ _)
  · rfl
  · simp only [Option.map_some, Option.bind_some]
    split <;> rfl

/-- **The hypertree** is its three layers from the bottom. -/
theorem verifyLayers_id (seed : PublicParameter) (idx : Index) (sig : Signature) (d : Digest) :
    Id.run (Verification.verifyLayers (m := Id) LeanVM.Semantics.keccakF1600 seed idx sig 3 d) =
      ((layerRoot seed idx sig 0 d).bind (layerRoot seed idx sig 1)).bind
        (layerRoot seed idx sig 2) := by
  rw [verifyLayers_succ_id seed idx sig (k := 2) (by decide)]
  simp (config := { decide := true }) only [verifyLayers_succ_id seed idx sig (k := 1) (by decide),
    verifyLayers_succ_id seed idx sig (k := 0) (by decide), Option.bind_assoc, ite_true, ite_false,
    Option.bind_fun_some]
  rfl

/-! ## Verification -/

/-- `verifyLayers_id` at `layerCount`. -/
theorem verifyLayers_layerCount (seed : PublicParameter) (idx : Index) (sig : Signature) (d : Digest) :
    Id.run (Verification.verifyLayers (m := Id) LeanVM.Semantics.keccakF1600 seed idx sig layerCount d) =
      ((layerRoot seed idx sig 0 d).bind (layerRoot seed idx sig 1)).bind
        (layerRoot seed idx sig 2) :=
  verifyLayers_id seed idx sig d

/-- `verify` in `Id`, over any permutation: the comparison of the layers' root with `PK.root`. -/
theorem verify_run (π : LeanVM.Semantics.KeccakState → Id LeanVM.Semantics.KeccakState)
    (pk : _root_.Sphincs.PublicKey) (msg : Message) (sig : Signature) :
    Id.run (Verification.verify (m := Id) π pk msg sig) =
      (match Id.run (Verification.verifyLayers (m := Id) π pk.publicSeed
          (digestIndex (Id.run (Verification.messageDigest (m := Id) π pk sig.randomizer msg))) sig layerCount
          (Id.run (Verification.forsRecover (m := Id) π pk.publicSeed
            (digestIndex (Id.run (Verification.messageDigest (m := Id) π pk sig.randomizer msg)))
            (digestForsLeaves (Id.run (Verification.messageDigest (m := Id) π pk sig.randomizer msg)))
            sig.forsOpening))) with
        | some r => decide (r = pk.root)
        | none => false) := by
  unfold Verification.verify
  simp only [Id.run_bind]
  generalize Id.run (Verification.verifyLayers (m := Id) π _ _ _ layerCount _) = o
  cases o <;> rfl

/-- **`verifyWithKeccak`**: the digest's index and leaves, the FORS key, the three layers, then
the comparison with `PK.root`. -/
theorem verifyWithKeccak_eq (pk : _root_.Sphincs.PublicKey) (msg : Message) (sig : Signature) :
    verifyWithKeccak pk msg sig =
      (match ((layerRoot pk.publicSeed (digestIndex (Id.run (Verification.messageDigest (m := Id)
          LeanVM.Semantics.keccakF1600 pk sig.randomizer msg))) sig 0
          (Id.run (Verification.forsRecover (m := Id) LeanVM.Semantics.keccakF1600 pk.publicSeed
            (digestIndex (Id.run (Verification.messageDigest (m := Id)
              LeanVM.Semantics.keccakF1600 pk sig.randomizer msg)))
            (digestForsLeaves (Id.run (Verification.messageDigest (m := Id)
              LeanVM.Semantics.keccakF1600 pk sig.randomizer msg))) sig.forsOpening))).bind
          (layerRoot pk.publicSeed (digestIndex (Id.run (Verification.messageDigest (m := Id)
            LeanVM.Semantics.keccakF1600 pk sig.randomizer msg))) sig 1)).bind
          (layerRoot pk.publicSeed (digestIndex (Id.run (Verification.messageDigest (m := Id)
            LeanVM.Semantics.keccakF1600 pk sig.randomizer msg))) sig 2) with
        | some r => decide (r = pk.root)
        | none => false) := by
  rw [show verifyWithKeccak pk msg sig = Id.run (Verification.verify (m := Id)
    LeanVM.Semantics.keccakF1600 pk msg sig) from rfl, verify_run, verifyLayers_layerCount]

end Native.SphincsVerifier
