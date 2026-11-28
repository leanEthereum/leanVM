module

public import Native.Sphincs.Gadgets
public import Statement.LeanSphincs

/-!
# The tweakable hash as words

leanSPHINCS's addressed hash `Trunc_16(H(PK.seed ‖ ADRS ‖ M))` is `th` of the seed,
address and payload words (`addressedHash_eq`).
-/

@[expose] public section

namespace Native.SphincsVerifier

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation _root_.Sphincs Keccak

/-! ## Bytes of words -/

theorem wordsBytes_append (a b : List UInt64) : wordsBytes (a ++ b) = wordsBytes a ++ wordsBytes b :=
  List.flatMap_append

theorem wordsBytes_cons (w : UInt64) (ws : List UInt64) :
    wordsBytes (w :: ws) = wordBytes w ++ wordsBytes ws := List.flatMap_cons

theorem wordsBytes_length (ws : List UInt64) : (wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [wordsBytes_cons, ih, wordBytes]; omega

theorem ofNat_toNat32 (x : UInt64) : BitVec.ofNat 32 x.toNat = x.toBitVec.setWidth 32 :=
  BitVec.ofNat_toNat _ _

/-- A word of two big-endian 32-bit fields. -/
theorem wordBytes_bs (x y : UInt64) :
    wordBytes (bs x ||| bs y <<< 32) =
      bigEndianBytes 4 (BitVec.ofNat 32 x.toNat) ++ bigEndianBytes 4 (BitVec.ofNat 32 y.toNat) := by
  simp only [wordBytes, bigEndianBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [ofNat_toNat32, bs, UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
    interval_cases i <;> simp

theorem bs_zero : bs 0 = 0 := rfl

/-- A tree below `2^32`, as `bigEndianBytes 8`. -/
theorem bigEndianBytes_tree {t : Nat} (ht : t < 2 ^ 32) :
    bigEndianBytes 8 (BitVec.ofNat 64 t) =
      bigEndianBytes 4 (BitVec.ofNat 32 0) ++ bigEndianBytes 4 (BitVec.ofNat 32 t) := by
  simp only [bigEndianBytes, List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat]
    interval_cases i <;> simp <;>
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ht (Nat.pow_le_pow_right (by decide) (by decide)))

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-! ## The hash -/

/-- `Trunc_16(H(PK.seed ‖ ADRS ‖ payload))` is `th` of the words. -/
theorem addressedHash_eq (seed : BitVec 128) (address : Address) (payload : HashInput)
    (aw pw : List UInt64) (len : Nat) (ha : wordsBytes aw = address.toBytes) (haw : aw.length = 4)
    (hp : (wordsBytes pw).take (len - 48) = payload) (hlen : 48 ≤ len) :
    Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed address payload) =
      th ([digestLo seed, digestHi seed] ++ aw ++ pw) len := by
  have hin : (wordsBytes ([digestLo seed, digestHi seed] ++ aw ++ pw)).take len =
      addressedHashInput seed address payload := by
    have h48 : (wordsBytes ([digestLo seed, digestHi seed] ++ aw)).length = 48 := by
      rw [wordsBytes_length]; simp [haw]
    rw [wordsBytes_append, List.take_append, h48, List.take_of_length_le (by omega), hp,
      addressedHashInput, hasherInput, wordsBytes_append, ← littleEndianBytes_16, ha]
  rw [th, hin, ← truncate_keccakHash]
  rfl

theorem words_two {V : Nat → UInt64} {k : Nat} {d : BitVec 128} (h0 : V k = digestLo d)
    (h1 : V (k + 1) = digestHi d) : words V k 2 = [digestLo d, digestHi d] := by
  simp [words, show List.range 2 = [0, 1] from rfl, h0, h1]

/-- Two words hold a digest's 16 bytes. -/
theorem payload_digest {V : Nat → UInt64} {k : Nat} {d : BitVec 128} (h0 : V k = digestLo d)
    (h1 : V (k + 1) = digestHi d) : (wordsBytes (words V k 2)).take 16 = littleEndianBytes 16 d := by
  rw [words_two h0 h1, littleEndianBytes_16, List.take_of_length_le]
  rw [wordsBytes_length]; simp

/-- Four words hold a node's two children. -/
theorem payload_node {V : Nat → UInt64} {k : Nat} {a b : BitVec 128} (h0 : V k = digestLo a)
    (h1 : V (k + 1) = digestHi a) (h2 : V (k + 2) = digestLo b) (h3 : V (k + 3) = digestHi b) :
    (wordsBytes (words V k 4)).take 32 = nodePayload a b := by
  rw [show 4 = 2 + 2 from rfl, words_add, words_two h0 h1,
    words_two (k := k + 2) h2 (by rw [Nat.add_assoc]; exact h3), wordsBytes_append]
  unfold nodePayload
  rw [littleEndianBytes_16, littleEndianBytes_16, List.take_of_length_le]
  rw [List.length_append, wordsBytes_length, wordsBytes_length]; simp

/-- `2 n` words hold `n` digests. -/
theorem words_digests {V : Nat → UInt64} : ∀ {n : Nat} {k : Nat} {f : Fin n → Digest},
    (∀ i : Fin n, V (k + 2 * i.val) = digestLo (f i) ∧ V (k + 2 * i.val + 1) = digestHi (f i)) →
    wordsBytes (words V k (2 * n)) = digestsPayload f
  | 0, _, _, _ => rfl
  | n + 1, k, f, h => by
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, words_add, wordsBytes_append,
      words_two (d := f 0) (by simpa using (h 0).1) (by simpa using (h 0).2),
      ← littleEndianBytes_16 (f 0),
      words_digests (n := n) (k := k + 2) (f := fun i ↦ f i.succ) fun i ↦ by
        have := h i.succ
        simp only [Fin.val_succ] at this
        constructor
        · rw [← this.1]; congr 1; omega
        · rw [← this.2]; congr 1; omega]
    simp only [digestsPayload]
    erw [List.ofFn_succ, List.flatMap_cons]

end Native.SphincsVerifier
