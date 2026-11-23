module

public import NativeRustcX64.SphincsVerify.Fors.Call
public import NativeRustcX64.SphincsVerify.Digest.ForsKey
public import NativeRustcX64.SphincsVerify.Bswap

/-!
# The FORS region's states and words (x86-64)

The states the proof passes through: a tree's head (`AtTree`, `b58`), a node's head (`AtNode`,
`b65`). The words the region builds its addresses from: tree `c`'s leaf index in the leaves'
copy (`wordAt_leaf`), the leaf's and a node's index (`bytes_leafIndex`, `bytes_nodeIndex`), the
height (`bytes_height`), the addresses in the pieces the blocks write (`leafAdrs_eq`,
`nodeAdrs_eq`); the bit of the leaf index that orders a node's children (`bit_eval`); a load's
bytes (`bytes_load`).
-/

namespace NativeRustcX64.SphincsVerifyProof.Fors

open NativeRustc NativeRustc.Sphincs NativeRustcX64.Sym LeanVM.Protocol.KeccakHash

@[expose] public section

/-- **At tree `c`'s head** `b58`: RSI the tree counter, R12 hasher A, R14 `PK.seed`,
R13 the tree word, EBP the key pair word and R15 hasher B. -/
structure AtTree [Labels] (r : Run) (c : Nat) (m : MachineData) : Prop where
  keep : Keep0 r c m
  rsi : Run.RegIs m .rsi (BitVec.ofNat 64 c)
  r12 : Run.RegIs m .r12 (r.off 4104)
  r14 : Run.RegIs m .r14 (r.off 112)
  r13 : wordBytes (UInt64.ofBitVec (reg m .r13)) = be64 (r.key 0).tree
  rbp : wordBytes (UInt64.ofBitVec (reg m .rbp)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0]
  rbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec
  r15 : Run.RegIs m .r15 (r.off 560)

/-- **At a node's head** `b65` (`.LSphincsVerify_20`): tree `c`, height `z < 10` (RCX), the
value after `z` steps at `8328`, `c` at `88`. -/
structure AtNode [Labels] (r : Run) (c z : Nat) (m : MachineData) : Prop where
  keep : Keep r c m
  hz : z < 10
  rcx : Run.RegIs m .rcx (BitVec.ofNat 64 z)
  r12 : Run.RegIs m .r12 (r.off 2056)
  r15 : Run.RegIs m .r15 (r.off 4104)
  r13 : wordBytes (UInt64.ofBitVec (reg m .r13)) = be64 (r.key 0).tree
  rbp : wordBytes (UInt64.ofBitVec (reg m .rbp)) = be32 (r.key 0).leaf ++ [0, 0, 0, 0]
  w88 : r.WordAt m 88 c.toUInt64
  cur : BytesAt m.dmem (r.off 8328) (r.forsUpTo c z)
  rbx : Run.RegIs m .rbx (Labels.label "memset").toBitVec
  r14 : Run.RegIs m .r14 (Labels.label "memcpy").toBitVec

end

public section

variable {r : Run}

/-- Tree `c`'s leaf index in the leaves' copy. -/
theorem wordAt_leaf {m : MachineData} (h : BytesAt m.dmem (r.off 10384) (leavesBytes r)) {c : Nat}
    (hc : c < 24) : r.WordAt m (10384 + 8 * c) (r.leafOf c).toUInt64 := by
  have := Chains.BytesAt.slice h (8 * c) (8 * 1)
  rw [leavesBytes, slice_wordsBytes, Run.off_add] at this
  have e : ((r.leaves.map Nat.toUInt64).drop c).take 1 = [(r.leafOf c).toUInt64] := by
    have hl : c < (r.leaves.map Nat.toUInt64).length := by simp [r.length_leaves, hc]
    rw [List.take_one, List.head?_drop, List.getElem?_eq_getElem hl, Option.toList_some,
      List.getElem_map, Run.leafOf, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [r.length_leaves]; exact hc), Option.getD_some]
  rw [e] at this
  show BytesAt m.dmem (r.off (10384 + 8 * c)) (wordBytes (r.leafOf c).toUInt64)
  simpa [Native.Keccak.wordsBytes] using this

/-- The low 4 bytes of a 32-bit truncation are the value's. -/
theorem bytes4_trunc (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 x)) = (List.range 4).map (byteOf x) := by
  rw [Digest.bytes_trunc32, ← bytes_word, ← List.map_take, List.take_range]
  rfl

theorem toNat_leaf {c : Nat} (hc : c < 24) :
    ((r.leafOf c).toUInt64.toBitVec).toNat = r.leafOf c := by
  have := r.leafOf_lt hc
  rw [UInt64.toNat_toBitVec, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

theorem shl10 : ∀ c < 24, (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 c))
    (BitVec.ofNat 64 10)).toNat = c * 1024 := by decide +kernel

/-- A 32-bit sum's number. -/
theorem toNat_add32 (x y : BitVec 64) :
    (BinOp.apply .add .W32 x y).toNat = (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [BinOp.apply, low, ext, BitVec.toNat_setWidth, BitVec.toNat_add, Width.bits]
  omega

/-- The leaf's index word, as `b58` computes it. -/
theorem bytes_leafIndex {c : Nat} (hc : c < 24) (l : Nat) :
    (List.range 4).map (byteOf (UnOp.apply .trunc .W32 (UnOp.apply .bswap .W32
      (BinOp.apply .add .W32 (BitVec.ofNat 64 l)
        (BinOp.apply .shl .W32 (UnOp.apply .trunc .W32 (BitVec.ofNat 64 c))
          (BitVec.ofNat 64 10)))))) =
      be32 ((c <<< (10 - 0)) + l).toUInt32 := by
  rw [bytes4_trunc, bytes_bswap32]
  congr 1
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.toUInt32_eq, UInt32.toNat_ofNat', toNat_add32, shl10 c hc,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The leaf's address, in the pieces `b58` writes. -/
theorem leafAdrs_eq (r : Run) (c l : Nat) :
    forsNodeAdrs r.idx c 0 l = (be32 0 ++ be32 0) ++ (be64 (r.key 0).tree ++ (be32 3 ++
      (be32 (r.key 0).leaf ++ (be32 0 ++ be32 ((c <<< (10 - 0)) + l).toUInt32)))) := by
  rw [forsNodeAdrs_eq, adrsBytes, List.append_assoc]
  rfl

/-- A hasher no write of a block touches. -/
theorem HasherAt.kept [Labels] (hpre : r.Pre) {m m' : MachineData} {a : Nat} {x : List UInt8}
    (h : Digest.HasherAt r m a x) {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hm : Match (r.env m vars ret) S m') (hwf : (r.env m vars ret).WF) (ha : a + 344 ≤ 29400)
    (hn : Run.noWriteIn S a 344 = true) : Digest.HasherAt r m' a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, r.bytesAt_kept hpre hm hwf (by omega) hb (by rw [hl]; exact hn), hh⟩

/-- A hasher a call does not touch. -/
theorem HasherAt.kc {m m' : MachineData} {a' n : Nat} (hk : KC r m m' a' n) {a : Nat}
    {x : List UInt8} (h : Digest.HasherAt r m a x) (ha : a + 344 ≤ 29400)
    (hd : a + 344 ≤ a' ∨ a' + n ≤ a) : Digest.HasherAt r m' a x := by
  obtain ⟨b, hb, hh⟩ := h
  have hl := Keccak.length_of_holds hh
  exact ⟨b, hk (by omega) (by omega) hb, hh⟩

/-- `PK.seed` in the frame. -/
theorem Keep.seed {c : Nat} {m : MachineData} (hK : Keep r c m) :
    BytesAt m.dmem (r.off 112) r.seed :=
  Digest.Keep.seed ⟨hK.1, hK.2.1.inputs, hK.2.1.w176⟩

/-- Tree `c`'s secret in the frame. -/
theorem Base.secret {c : Nat} {m : MachineData} (hB : Base r c m) :
    BytesAt m.dmem (r.off (20716 + 176 * c)) (r.openingOf c).secret := by
  have := Chains.BytesAt.slice hB.inputs.2 (176 * c + 160) 16
  rw [Run.off_add, show sigMem r.sig = sigMem (sigOf r.w) from rfl,
    SigMem.sigMem_secret r.w hB.hc] at this
  rwa [show 20556 + (176 * c + 160) = 20716 + 176 * c by omega] at this

/-- Tree `c`'s path node `z` in the frame. -/
theorem Base.pathNode {c : Nat} {m : MachineData} (hB : Base r c m) {z : Nat} (hz : z < 10) :
    BytesAt m.dmem (r.off (20556 + 176 * c + 16 * z)) (r.pathNode c z) := by
  have := Chains.BytesAt.slice hB.inputs.2 (176 * c + 16 * z) 16
  rw [Run.off_add, show sigMem r.sig = sigMem (sigOf r.w) from rfl,
    SigMem.sigMem_path r.w hB.hc hz] at this
  rwa [show 20556 + (176 * c + 16 * z) = 20556 + 176 * c + 16 * z by omega] at this

theorem bytes_zero8 : (List.range 8).map (byteOf (BitVec.ofNat 64 0)) = be32 0 ++ be32 0 := by
  decide

theorem bytes_zero4 : (List.range 4).map (byteOf (BitVec.ofNat 64 0)) = be32 0 := by
  decide

theorem bytes_typeW : (List.range 4).map (byteOf (BitVec.ofNat 64 50331648)) = be32 3 := by
  decide

theorem length_forsNodeAdrs (idx : UInt64) (c z j : Nat) :
    (forsNodeAdrs idx c z j).length = 32 := by
  rw [forsNodeAdrs_eq]; rfl

end

end NativeRustcX64.SphincsVerifyProof.Fors
