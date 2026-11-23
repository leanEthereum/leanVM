module

public import NativeRustcArm.KeccakF.Inv
public import NativeRustcArm.Hasher.Bytes
public import NativeRustcVmArm.Spec.Keccak

/-!
# Memory lemmas for the Keccak proofs

Bytes kept by a block where no write overlaps them (`bytesAt_keep`), bytes carried across a
`SameOutside` (`bytesAt_of_same`), addresses of a range apart from another outside it
(`not_inRange_of_apart`), the round constants as words (`rcBytes_eq`, `load_rc_at`), the
words of a state as `stateBytes` (`wordsAt_iff`), the model's words as the arch's
(`wordAt_bits`, `load_wordAt`), and words' bytes from their words (`bytesAt_words`).
-/

namespace NativeRustcVmArm.Keccak

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
  LeanVM.Parameters

public section

variable [Labels] {env : Env} {S : SState} {m : MachineData}

/-- **Bytes kept**: bytes in region `r` that no write of the block covers keep their values. -/
theorem bytesAt_keep (hm : Match env S m) {r o sz : Nat} {b : BitVec 64}
    (hb : env.regions[r]? = some (b, sz)) {bs : List UInt8} (hle : o + bs.length ≤ sz)
    (h : firstOverlap r o bs.length S.mem = none) (h0 : BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := by
  intro i hi
  rw [addr_add, hm.mem r b sz hb (o + i) (by omega)]
  unfold memByte
  rw [findWrite_none h (Nat.le_add_right o i) (by omega), ← addr_add]
  exact h0 i hi

omit [Labels] in
/-- Bytes outside the addresses `R` are carried across `SameOutside`. -/
theorem bytesAt_of_same {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs)
    (hR : ∀ i < bs.length, ¬ R (a + BitVec.ofNat 64 i)) : BytesAt d' a bs :=
  fun i hi => (hs _ (hR i hi)).trans (h i hi)

omit [Labels] in
/-- A byte of a range is outside another range apart from it. -/
theorem not_inRange_of_apart {a b : BitVec 64} {n n' : Nat} (hna : NoWrap a n) (hnb : NoWrap b n')
    (hap : Apart a n b n') {i : Nat} (hi : i < n) : ¬ InRange b n' (a + BitVec.ofNat 64 i) := by
  rw [inRange_iff hnb, toNat_add_ofNat _ _ (by unfold NoWrap at hna; omega)]
  unfold Apart at hap
  omega

omit [Labels] in
/-- `bytesOf` of a range carried across `SameOutside`. -/
theorem bytesOf_of_same {d d' : DataMem} {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    {a : BitVec 64} {n : Nat} (hR : ∀ i < n, ¬ R (a + BitVec.ofNat 64 i)) :
    bytesOf d' a n = bytesOf d a n :=
  Hasher.bytesOf_congr fun i hi => hs _ (hR i hi)

omit [Labels] in
theorem length_rcBytes : rcBytes.length = 192 := by
  rw [show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
    Native.Keccak.Proof.length_wordsBytes]
  rfl

omit [Labels] in
/-- **Round constant `i`** is what the environment loads at `o + 8 i` from region `r` where the
table is at `o`. -/
theorem load_rc_at {r o i : Nat} (hb : BytesAt env.mem0 (env.base r + BitVec.ofNat 64 o) rcBytes)
    (hi : i < 24) : env.load r (o + 8 * i) 8 = (keccakRC.getD i 0).toBitVec := by
  apply KeccakF.load_eq_of_bytes
  intro k hk
  rw [show o + 8 * i + k = o + (8 * i + k) by omega, ← addr_add,
    hb (8 * i + k) (by rw [length_rcBytes]; omega), Option.getD_some,
    KeccakF.getElem_eq_getD', show rcBytes = Native.Keccak.wordsBytes keccakRC from rfl,
    Native.Keccak.Proof.getD_wordsBytes, show (8 * i + k) / 8 = i by omega,
    show (8 * i + k) % 8 = k by omega]

omit [Labels] in
/-- A word of the model's as the arch's `WordAt` of its bits. -/
theorem wordAt_bits {d : DataMem} {a : BitVec 64} {x : UInt64} (h : NativeRustcVm.WordAt d a x) :
    KeccakF.WordAt d a x.toBitVec := by
  have := Hasher.wordBytes_ofBitVec x.toBitVec
  rw [UInt64.ofBitVec_toBitVec] at this
  unfold KeccakF.WordAt
  rw [← this]
  exact h

omit [Labels] in
/-- A word of the model's, loaded. -/
theorem load_wordAt {r o : Nat} {x : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 o) x) :
    env.load r o 8 = x.toBitVec :=
  KeccakF.load_of_wordAt (wordAt_bits h)

omit [Labels] in
/-- Words' bytes from their words. -/
theorem bytesAt_words {d : DataMem} {a : BitVec 64} {ws : List UInt64}
    (h : ∀ j < ws.length, KeccakF.WordAt d (a + BitVec.ofNat 64 (8 * j)) (ws.getD j 0).toBitVec) :
    BytesAt d a (Native.Keccak.wordsBytes ws) := by
  intro p hp
  rw [Native.Keccak.Proof.length_wordsBytes] at hp
  have := h (p / 8) (by omega) (p % 8) (by simp; omega)
  rw [addr_add, show 8 * (p / 8) + p % 8 = p by omega] at this
  rw [this, List.getElem_map, List.getElem_range, KeccakF.byteOf_toBitVec _ (by omega),
    KeccakF.getElem_eq_getD', Native.Keccak.Proof.getD_wordsBytes]

omit [Labels] in
/-- The words of a state are its `stateBytes`. -/
theorem wordsAt_iff {d : DataMem} {a : BitVec 64} {A : KeccakState} :
    NativeRustcVm.WordsAt d a A.toList ↔ BytesAt d a (stateBytes A) := Iff.rfl

end

end NativeRustcVmArm.Keccak
