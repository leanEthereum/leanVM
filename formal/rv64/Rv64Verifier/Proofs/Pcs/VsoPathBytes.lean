import Rv64Verifier.Proofs.Pcs.VsoOpenings
import Rv64Verifier.Proofs.Pcs.VsoMerkle
import Rv64Verifier.Proofs.Pcs.VsoClimbBytes
import Rv64Verifier.Proofs.Hash.Mem

/-!
# A path's bytes

The leaf's words and the digests in memory as the bytes `merkleRust` hashes and compares
(`leaf_bytes`, `digestBits_at`), and `memcmp`'s result, sign-extended from its low word as
`0x8000ab18` and `0x8000b0b4` test it, zero only for equal bytes (`cmp_eq`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime LeanVM.Protocol
  Rv64Verifier.PcsContracts

theorem readWords_eq_range (s : MachineState) (b : Word) (n : Nat) :
    s.readWords b n = (List.range n).map fun i ↦ s.getMem (b + BitVec.ofNat 64 (8 * i)) := by
  apply List.ext_getElem
  · simp [readWords_length]
  · intro i _ h2
    have hi : i < n := by simpa using h2
    rw [readWords_getElem s b n i hi]
    simp

/-- The bytes of `k` aligned doublewords. -/
theorem bytesAt_dwordsV (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) :
    ∀ k, a.toNat + 8 * k < 2 ^ 64 → Contracts.bytesAt s a (8 * k) =
      ((List.range k).map fun i ↦ s.getMem (a + BitVec.ofNat 64 (8 * i))).flatMap Model.toLeBytes
  | 0, _ => rfl
  | k + 1, hk => by
    have hadd : ∀ m n, Contracts.bytesAt s a (m + n) =
        Contracts.bytesAt s a m ++ Contracts.bytesAt s (a + BitVec.ofNat 64 m) n := by
      intro m n
      simp only [Contracts.bytesAt, List.range_add, List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]
    rw [show 8 * (k + 1) = 8 * k + 8 by ring, hadd, bytesAt_dwordsV s ha k (by omega),
      List.range_succ, List.map_append, List.flatMap_append]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hb : (a + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    simp only [Model.toLeBytes, Contracts.bytesAt]
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    rw [getByte_aligned s hb hi]
    simp only [extractByte, Nat.mul_comm]

theorem byteBits_flatMap {α : Type} (l : List α) (f : α → List UInt8) :
    Model.byteBits (l.flatMap f) = l.flatMap fun x ↦ Model.byteBits (f x) := by
  simp only [Model.byteBits, List.map_flatMap]

theorem toBytes_ofBitVec (w : Word) : Model.byteBits (K.toBytes (BF64.ofBitVec w)) = Model.toLeBytes w :=
  (Model.toLeBytes_toBitVec ⟨w⟩).symm

/-- A leaf's words, as `keccak_hash` reads them. -/
theorem leaf_bytes (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) (n : Nat)
    (hn : a.toNat + 8 * n < 2 ^ 64) :
    Model.byteBits (((s.readWords a n).map BF64.ofBitVec).flatMap K.toBytes) =
      Contracts.bytesAt s a (8 * n) := by
  rw [bytesAt_dwordsV s ha n hn, readWords_eq_range, List.map_map, byteBits_flatMap,
    List.flatMap_map, List.flatMap_map]
  simp only [Function.comp, toBytes_ofBitVec]

/-- An aligned digest, as `memcmp` and the climb read it. -/
theorem digestBits_at (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0)
    (hn : a.toNat + 32 < 2 ^ 64) :
    Model.Pcs.digestBits (digestAt s a) = Contracts.bytesAt s a 32 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, bytesAt_dwordsV s ha 4 hn]
  simp only [Model.Pcs.digestBits, KeccakHash.digestBytes, digestAt, Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero,
    show List.range 4 = [0, 1, 2, 3] from rfl, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil]
  rfl

theorem toLeBytes_laneOfBytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    Model.toLeBytes (Transcript.laneOfBytes [b0, b1, b2, b3, b4, b5, b6, b7]).toBitVec =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [Transcript.laneOfBytes, Model.toLeBytes, List.foldr_cons, List.foldr_nil,
    UInt64.toBitVec_ofBitVec, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem bytesAt_add (s : MachineState) (a : Word) (m n : ℕ) :
    Contracts.bytesAt s a (m + n) =
      Contracts.bytesAt s a m ++ Contracts.bytesAt s (a + BitVec.ofNat 64 m) n := by
  simp only [Contracts.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, BitVec.add_assoc, BitVec.ofNat_add]

/-- A digest read as bytes, at any alignment, as `memcmp` and the climb read it. -/
theorem digestBits_bytes (s : MachineState) (a : Word) :
    Model.Pcs.digestBits (Transcript.digestBytesAt s a) = Contracts.bytesAt s a 32 := by
  have e (b : Word) : Model.toLeBytes (Transcript.laneOfBytes (Contracts.bytesAt s b 8)).toBitVec =
      Contracts.bytesAt s b 8 := by
    simp only [Contracts.bytesAt, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.map_cons, List.map_nil]
    exact toLeBytes_laneOfBytes _ _ _ _ _ _ _ _
  rw [show (32 : ℕ) = 8 + (8 + (8 + 8)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    ← e a, ← e (a + BitVec.ofNat 64 8), ← e (a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8),
    ← e (a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8)]
  simp only [Model.Pcs.digestBits, KeccakHash.digestBytes, Transcript.digestBytesAt,
    Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Model.byteBits, List.map_append, Fin.val_zero, Fin.val_succ, BitVec.add_assoc,
    Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero, BitVec.reduceAdd]
  rfl

/-- `memcmp`'s result tested as its low word: zero only for equal bytes. -/
theorem cmp_eq : ∀ {xs ys : List (BitVec 8)}, xs.length = ys.length →
    (wordResult .add ((cmpBytes xs ys).truncate 32) ((0 : Word).truncate 32)).signExtend 64 = 0 →
      xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [cmpBytes] at h
    by_cases hxy : x = y
    · rw [ite_eq_left hxy] at h
      rw [hxy, cmp_eq hl h]
    · exfalso
      rw [ite_eq_right hxy] at h
      have h0 : (wordResult .add ((x.zeroExtend 64 - y.zeroExtend 64).truncate 32)
          ((0 : Word).truncate 32)) = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have := congrArg (fun v : Word ↦ v.getLsbD i) h
        simp only [BitVec.getLsbD_signExtend] at this
        simpa [hi, show i < 64 by omega] using this
      apply hxy
      apply BitVec.eq_of_toNat_eq
      have hx := x.isLt
      have hy := y.isLt
      have := congrArg BitVec.toNat h0
      simp only [wordResult, BitVec.truncate_eq_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth,
        BitVec.toNat_sub, show BitVec.toNat (0 : Word) = 0 from rfl,
        show BitVec.toNat (0 : BitVec 32) = 0 from rfl] at this
      omega

end Rv64Verifier.Proofs.Pcs.Vso
