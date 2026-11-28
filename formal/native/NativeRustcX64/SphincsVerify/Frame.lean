module

public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.SphincsVerify.Basic
public import NativeRustcX64.Sym.Run
public import NativeRustcX64.Got

/-!
# The frame's facts for calls and blocks (x86-64)

From the run's precondition and the frame's invariant (`Run.Pre`, `Run.Frame`): the frame's bytes
(with the return address above them) are mapped and do not wrap (`Run.frame_mapped`), apart from
each other and from the round constants (`Run.apart_off`, `Run.apart_rc`); the bytes apart from
the stack area keep their entry values (`Run.bytesAt_entry`, `Run.lh`).

At a call (`Run.AtCall`: RSP 8 below the base, the return address pushed) the callee has its
stack (`Run.stackOk`) and the round constants (`Run.rcAt`), apart from the frame
(`Run.apart_off_below`); after the call, changes in the frame below the saved registers and in
the callee's stack keep the invariant (`Run.Frame.of_post`; their places: `Run.inRange_off`,
`Run.inRange_below`).

The executor's view (`Run.env`, `Run.match_frame`): region 0 the frame and the return address
(`frameRegion` bytes from the base, RSP `ptr 0 0`), region 1 the 16 bytes below it, where `call`
and `push` write (aliased as `ptr 0 (-8)`, `ptr 0 (-16)`, `frameAliases`). After a block: the
invariant (`Run.Frame.of_match`, `frameWrites`), or at a call (`Run.AtCall.of_match`); the bytes
it does not write (`Run.bytesAt_kept`, `noWriteIn`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc

public section

/-- Bytes no change covers are kept. -/
theorem bytesAt_of_sameOutside {d d' : DataMem} {a : BitVec 64} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : BytesAt d a bs) (hs : SameOutside d d' R)
    (hR : ∀ i < bs.length, ¬R (a + BitVec.ofNat 64 i)) : BytesAt d' a bs := fun i hi ↦ by
  rw [hs _ (hR i hi)]
  exact h i hi

/-- `Apart` from a range is `Apart` from a range inside it. -/
theorem apart_of_sub {a x y : BitVec 64} {n N n' : Nat} (h : Apart a n x N)
    (h1 : x.toNat ≤ y.toNat) (h2 : y.toNat + n' ≤ x.toNat + N) : Apart a n y n' := by
  unfold Apart at *
  omega

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_sub_ofNat {b : BitVec 64} {n : Nat} (h : n ≤ b.toNat) :
    (b - BitVec.ofNat 64 n).toNat = b.toNat - n := by
  have := b.isLt
  rw [Sym.toNat_sub_of_le _ _ (by rw [toNat_ofNat_lt (by omega)]; exact h),
    toNat_ofNat_lt (by omega)]

theorem inRange_self_add {a : BitVec 64} {n i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    InRange a n (a + BitVec.ofNat 64 i) := by
  unfold InRange
  rw [BitVec.add_comm, BitVec.add_sub_cancel, toNat_ofNat_lt (by omega)]
  exact hi

namespace Run

theorem frameSize_eq : frameSize = 21624 := rfl
theorem frameRegion_eq : frameRegion = 21632 := rfl
theorem finalizeStack_eq : finalizeStack = 672 := rfl
theorem sphincsStack_eq : sphincsStack = 22304 := rfl

theorem off_add (r : Run) (a i : Nat) : r.off a + BitVec.ofNat 64 i = r.off (a + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

variable (r : Run) [Labels]

/-- The frame's base: `frameSize` below RSP at entry, 680 bytes of the stack below it, the return
address above. -/
theorem base_toNat (hpre : r.Pre) :
    r.base.toNat + 21624 = (rspOf r.m0).toNat ∧ 680 ≤ r.base.toNat ∧
      (rspOf r.m0).toNat + 8 ≤ 2 ^ 64 := by
  have hle := hpre.1.1
  have hw := hpre.1.2.1
  rw [sphincsStack_eq] at hle
  unfold base
  rw [frameSize_eq, toNat_sub_ofNat (by omega)]
  omega

/-- The frame's byte `a`. -/
theorem off_toNat (hpre : r.Pre) {a : Nat} (ha : a ≤ 21624) :
    (r.off a).toNat = r.base.toNat + a := by
  have := r.base_toNat hpre
  exact Sym.toNat_add_ofNat _ _ (by omega)

/-- The stack area's start: 680 bytes below the frame. -/
theorem below_toNat (hpre : r.Pre) :
    (stackBelow r.m0 sphincsStack).toNat + 680 = r.base.toNat := by
  have := r.base_toNat hpre
  have hle := hpre.1.1
  rw [sphincsStack_eq] at hle ⊢
  unfold stackBelow
  rw [toNat_sub_ofNat (by omega)]
  omega

/-- The bytes from 680 below the frame to its return address are mapped, in any state keeping
the entry's mapped bytes. -/
theorem area_mapped (hpre : r.Pre) {d : DataMem} (hk : Kept r.m0.dmem d) {p : BitVec 64}
    (h1 : r.base.toNat ≤ p.toNat + 680) (h2 : p.toNat < r.base.toNat + 21632) :
    (d.get? p).isSome := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have hp : p = stackBelow r.m0 sphincsStack +
      BitVec.ofNat 64 (p.toNat - (stackBelow r.m0 sphincsStack).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega
  have hm : (r.m0.dmem.get? (stackBelow r.m0 sphincsStack +
      BitVec.ofNat 64 (p.toNat - (stackBelow r.m0 sphincsStack).toNat))).isSome :=
    hpre.1.2.2 (p.toNat - (stackBelow r.m0 sphincsStack).toNat)
      (by simp only [sphincsStack_eq] at *; omega)
  rw [← hp] at hm
  exact hk _ hm

/-- **The frame's bytes** `a .. a + n` are mapped and do not wrap. -/
theorem frame_mapped (hpre : r.Pre) {d : DataMem} (hk : Kept r.m0.dmem d) {a n : Nat}
    (h : a + n ≤ 21624) : Mapped d (r.off a) n ∧ NoWrap (r.off a) n := by
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
  · rw [Sym.toNat_add_ofNat _ _ (by omega), ho]
    omega
  · rw [Sym.toNat_add_ofNat _ _ (by omega), ho]
    omega
  · unfold NoWrap
    omega

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'` are apart when their offsets are. -/
theorem apart_off (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 21624) (ha' : a' + n' ≤ 21624)
    (h : a + n ≤ a' ∨ a' + n' ≤ a) : Apart (r.off a) n (r.off a') n' := by
  unfold Apart
  rw [r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)]
  omega

/-- The stack area: from 680 bytes below the frame to the return address. -/
theorem stackArea_iff (hpre : r.Pre) (p : BitVec 64) :
    r.StackArea p ↔ r.base.toNat ≤ p.toNat + 680 ∧ p.toNat < r.base.toNat + 21624 := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  unfold StackArea
  rw [Sym.inRange_iff (by simp only [sphincsStack_eq] at *; omega)]
  simp only [sphincsStack_eq] at *
  omega

/-- No byte apart from the stack and the return address is in the stack area. -/
theorem not_area_of_apart (hpre : r.Pre) {a : BitVec 64} {n : Nat}
    (h : Apart a n (stackBelow r.m0 sphincsStack) (sphincsStack + 8)) (hw : NoWrap a n) {i : Nat}
    (hi : i < n) : ¬r.StackArea (a + BitVec.ofNat 64 i) := by
  rw [r.stackArea_iff hpre]
  have hw' := r.below_toNat hpre
  unfold Apart NoWrap at *
  simp only [sphincsStack_eq] at *
  rw [Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- The bytes at `a`, apart from the stack, are the entry's. -/
theorem bytesAt_entry (hpre : r.Pre) {d : DataMem} (hs : SameOutside r.m0.dmem d r.StackArea)
    {a : BitVec 64} {bs : List UInt8} (h : BytesAt r.m0.dmem a bs)
    (hA : Apart a bs.length (stackBelow r.m0 sphincsStack) (sphincsStack + 8))
    (hw : NoWrap a bs.length) : BytesAt d a bs :=
  bytesAt_of_sameOutside h hs fun _ hi ↦ r.not_area_of_apart hpre hA hw hi

/-- The frame's bytes are apart from the round constants. -/
theorem apart_rc (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 21624) :
    Apart (r.off a) n rcAddr 192 := by
  obtain ⟨_, _, hA⟩ := hpre.2.1
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  unfold Apart at *
  simp only [sphincsStack_eq] at *
  omega

/-- `LAYER_HEIGHTS` in any state of the frame. -/
theorem lh (hpre : r.Pre) {d : DataMem} (hs : SameOutside r.m0.dmem d r.StackArea) :
    BytesAt d (label NativeRustcX64.layerHeightsLabel).toBitVec lhBytes :=
  have hlen : lhBytes.length = 24 := by decide
  r.bytesAt_entry hpre hs hpre.2.2.1 (hlen ▸ hpre.2.2.2.2.1) (hlen ▸ hpre.2.2.2.1)

/-- The public key buffer's precondition facts. -/
theorem pk_pre (hpre : r.Pre) :
    BytesAt r.m0.dmem r.pkPtr r.pkB ∧ NoWrap r.pkPtr 32 ∧
      Apart r.pkPtr 32 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) :=
  ⟨hpre.2.2.2.2.2.1, hpre.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.1⟩

/-- The message buffer's precondition facts. -/
theorem msg_pre (hpre : r.Pre) :
    BytesAt r.m0.dmem r.msgPtr r.msgB ∧ NoWrap r.msgPtr 32 ∧
      Apart r.msgPtr 32 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) :=
  ⟨hpre.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The signature buffer's precondition facts. -/
theorem sig_pre (hpre : r.Pre) :
    BytesAt r.m0.dmem r.sigPtr r.sigB ∧ NoWrap r.sigPtr 7740 ∧
      Apart r.sigPtr 7740 (stackBelow r.m0 sphincsStack) (sphincsStack + 8) :=
  ⟨hpre.2.2.2.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2.2.2.2.1, hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The message buffer in any state of the frame. -/
theorem msg_at (hpre : r.Pre) {d : DataMem} (hs : SameOutside r.m0.dmem d r.StackArea) :
    BytesAt d r.msgPtr r.msgB :=
  have ⟨hm, hw, hA⟩ := r.msg_pre hpre
  r.bytesAt_entry hpre hs hm (r.hmsg ▸ hA) (r.hmsg ▸ hw)

/-- The signature buffer in any state of the frame. -/
theorem sig_at (hpre : r.Pre) {d : DataMem} (hs : SameOutside r.m0.dmem d r.StackArea) :
    BytesAt d r.sigPtr r.sigB :=
  have ⟨hsig, hw, hA⟩ := r.sig_pre hpre
  r.bytesAt_entry hpre hs hsig (r.hsig ▸ hA) (r.hsig ▸ hw)

/-- The frame's bytes are apart from an external buffer apart from the stack. -/
theorem apart_off_ext (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 21624)
    {b : BitVec 64} {m : Nat} (hA : Apart b m (stackBelow r.m0 sphincsStack) (sphincsStack + 8)) :
    Apart (r.off a) n b m := by
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  unfold Apart at *
  simp only [sphincsStack_eq] at *
  omega

/-! ## At a call -/

/-- **At a call**: RSP 8 below the base (the return address pushed), the saved registers in
place, no byte changed outside the stack area, every mapped byte still mapped. -/
@[expose] def AtCall (m : MachineData) : Prop :=
  rspOf m + 8#64 = r.base ∧ BytesAt m.dmem (r.off 21576) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem r.StackArea ∧ Kept r.m0.dmem m.dmem

omit [Labels] in
variable {r} in
theorem AtCall.rsp {m : MachineData} (hc : r.AtCall m) : rspOf m = r.base - 8#64 := by
  rw [← hc.1, BitVec.add_sub_cancel]

/-- RSP at a call. -/
theorem rsp_toNat (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) :
    (rspOf m).toNat + 8 = r.base.toNat := by
  have hb := r.base_toNat hpre
  rw [hc.rsp, toNat_sub_ofNat (by omega)]
  omega

/-- The `n ≤ finalizeStack` bytes below RSP at a call. -/
theorem stackBelow_toNat (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {n : Nat}
    (hn : n ≤ finalizeStack) : (stackBelow m n).toNat + n + 8 = r.base.toNat := by
  rw [finalizeStack_eq] at hn
  have hb := r.base_toNat hpre
  have := r.rsp_toNat hpre hc
  unfold stackBelow
  rw [toNat_sub_ofNat (by omega)]
  omega

/-- At a call, the callee has `n ≤ finalizeStack` bytes of stack and its return address. -/
theorem stackOk (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {n : Nat}
    (hn : n ≤ finalizeStack) : StackOk m n := by
  have hb := r.base_toNat hpre
  have hs := r.rsp_toNat hpre hc
  have hl := r.stackBelow_toNat hpre hc hn
  rw [finalizeStack_eq] at hn
  refine ⟨by omega, by omega, fun i hi ↦ r.area_mapped hpre hc.2.2.2 ?_ ?_⟩ <;>
  · rw [Sym.toNat_add_ofNat _ _ (by unfold stackBelow at hl; omega)]
    unfold stackBelow at hl
    omega

/-- What is apart from the stack area and the return address is apart from a callee's stack and
return address. -/
theorem apart_below (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {a : BitVec 64} {n N : Nat}
    (hN : N ≤ finalizeStack) (h : Apart a n (stackBelow r.m0 sphincsStack) (sphincsStack + 8)) :
    Apart a n (stackBelow m N) (N + 8) := by
  have := r.stackBelow_toNat hpre hc hN
  have := r.below_toNat hpre
  rw [finalizeStack_eq] at hN
  refine apart_of_sub h (by omega) ?_
  simp only [sphincsStack_eq] at *
  omega

/-- The frame's bytes are apart from a callee's stack and return address. -/
theorem apart_off_below (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {a n N : Nat}
    (ha : a + n ≤ 21624) (hN : N ≤ finalizeStack) : Apart (r.off a) n (stackBelow m N) (N + 8) := by
  have := r.stackBelow_toNat hpre hc hN
  unfold Apart
  rw [r.off_toNat hpre (by omega)]
  omega

/-- The frame's bytes are apart from the return address a call pushed. -/
theorem apart_off_ret (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {a n : Nat}
    (ha : a + n ≤ 21624) : Apart (r.off a) n (rspOf m) 8 := by
  have := r.rsp_toNat hpre hc
  unfold Apart
  rw [r.off_toNat hpre (by omega)]
  omega

/-- **The round constants** for a callee using `n ≤ finalizeStack` bytes of stack. -/
theorem rcAt (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {n : Nat}
    (hn : n ≤ finalizeStack) : RcAt m n := by
  obtain ⟨hrc, hw, hA⟩ := hpre.2.1
  have hlen : rcBytes.length = 192 := by
    rw [show rcBytes = Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC from rfl,
      Native.Keccak.Proof.length_wordsBytes]
    rfl
  exact ⟨r.bytesAt_entry hpre hc.2.2.1 hrc (hlen ▸ hA) (hlen ▸ hw), hw, r.apart_below hpre hc hn hA⟩

/-- The loader's two reachable function pointers. -/
theorem got (hpre : r.Pre) :
    GotAt r.m0 sphincsStack
      [(r.pkPtr, 32), (r.msgPtr, 32), (r.sigPtr, 7740),
        ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24)]
      ["memcpy", "memset"] :=
  hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem got_apart_lh (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 (label NativeRustcX64.layerHeightsLabel).toBitVec 24 :=
  ((r.got hpre).1 l hl).2.2.2
    ((label NativeRustcX64.layerHeightsLabel).toBitVec, 24) (by simp)

theorem got_apart_pk (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 r.pkPtr 32 :=
  ((r.got hpre).1 l hl).2.2.2 (r.pkPtr, 32) (by simp)

theorem got_apart_msg (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 r.msgPtr 32 :=
  ((r.got hpre).1 l hl).2.2.2 (r.msgPtr, 32) (by simp)

theorem got_apart_sig (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 r.sigPtr 7740 :=
  ((r.got hpre).1 l hl).2.2.2 (r.sigPtr, 7740) (by simp)

theorem got_apart_off (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {a n : Nat} (ha : a + n ≤ 21624) : Apart (gotAddr l) 8 (r.off a) n := by
  have hg := ((r.got hpre).1 l hl).2.2.1
  have hb := r.below_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  simp only [stackBelow, sphincsStack_eq] at hg hb
  apply apart_of_sub hg (by omega)
  omega

theorem got_apart_frame (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 r.base frameRegion := by
  have hg := ((r.got hpre).1 l hl).2.2.1
  have hb := r.below_toNat hpre
  simp only [stackBelow, sphincsStack_eq] at hg hb
  apply apart_of_sub hg (by omega)
  rw [frameRegion_eq]
  omega

theorem got_apart_below (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart (gotAddr l) 8 (r.base - 16#64) 16 := by
  have hg := ((r.got hpre).1 l hl).2.2.1
  have hb := r.below_toNat hpre
  have ht := r.base_toNat hpre
  have hs : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  simp only [stackBelow, sphincsStack_eq] at hg hb
  apply apart_of_sub hg (by omega)
  omega

theorem got_byte (hpre : r.Pre) {d : DataMem} (hs : SameOutside r.m0.dmem d r.StackArea)
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    d.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (Sym.byteOf (Labels.label l).toBitVec i) := by
  have hg := (r.got hpre).1 l hl
  have hb := r.below_toNat hpre
  have ht := r.base_toNat hpre
  simp only [sphincsStack_eq] at hb
  have hnw : NoWrap (stackBelow r.m0 sphincsStack) (sphincsStack + 8) := by
    unfold NoWrap
    rw [sphincsStack_eq]
    omega
  rw [hs _ (fun h => hg.2.2.1.not_inRange hg.2.1 hnw hi (Nat.lt_trans h (by omega)))]
  exact (r.got hpre).byte hl hi

theorem gotAt (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {n : Nat}
    (hn : n ≤ finalizeStack) {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hl : symbols.Sublist ["memcpy", "memset"])
    (ha : ∀ l ∈ symbols, ∀ a ∈ areas, Apart (gotAddr l) 8 a.1 a.2) :
    GotAt m n areas symbols := by
  apply ((r.got hpre).symbols hl).transport
  · intro l hl' i hi
    rw [r.got_byte hpre hc.2.2.1 (hl.subset hl') hi, (r.got hpre).byte (hl.subset hl') hi]
  · intro l hl'
    exact r.apart_below hpre hc hn (((r.got hpre).1 l (hl.subset hl')).2.2.1)
  · exact ha

/-! ## The invariant again -/

/-- A change in the frame's bytes `a .. a + n` below the saved registers is in the stack area,
off the saved registers. -/
theorem inRange_off (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 21576) {p : BitVec 64}
    (h : InRange (r.off a) n p) : r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  have hs := r.off_toNat hpre (a := 21576) (by decide)
  rw [Sym.inRange_iff (by rw [ho]; omega), ho] at h
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

/-- A change in a callee's stack is in the stack area, off the saved registers. -/
theorem inRange_below (hpre : r.Pre) {m : MachineData} (hc : r.AtCall m) {N : Nat}
    (hN : N ≤ finalizeStack) {p : BitVec 64} (h : InRange (stackBelow m N) N p) :
    r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  have hb := r.base_toNat hpre
  have hl := r.stackBelow_toNat hpre hc hN
  have hs := r.off_toNat hpre (a := 21576) (by decide)
  rw [finalizeStack_eq] at hN
  rw [Sym.inRange_iff (by omega)] at h
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

omit [Labels] in
theorem length_savedBytes (m : MachineData) : (savedBytes m).length = 48 := by
  rw [savedBytes, Native.Keccak.Proof.length_wordsBytes]
  rfl

omit [Labels] in
variable {r} in
/-- **The invariant after a change** in the stack area off the saved registers, RSP the base. -/
theorem Frame.of_change {m m' : MachineData}
    (hsv : BytesAt m.dmem (r.off 21576) (savedBytes r.m0))
    (hso : SameOutside r.m0.dmem m.dmem r.StackArea) (hk0 : Kept r.m0.dmem m.dmem)
    (hsp : rspOf m' = r.base) {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → r.StackArea p ∧ ¬InRange (r.off 21576) 48 p) (hk : Kept m.dmem m'.dmem) :
    r.Frame m' :=
  ⟨hsp, bytesAt_of_sameOutside hsv hout fun _ hi h ↦ (hR _ h).2 (inRange_self_add
      (by rwa [length_savedBytes] at hi) (by decide)),
    fun p hp ↦ (hout p fun h ↦ hp (hR p h).1).trans (hso p hp),
    fun p h ↦ hk p (hk0 p h)⟩

omit [Labels] in
variable {r} in
/-- **The invariant after a call**: the callee returned RSP 8 above, kept the mapped bytes, and
changed bytes only in the stack area off the saved registers. -/
theorem Frame.of_post {m m' : MachineData} (hc : r.AtCall m) (hsp : rspOf m' = rspOf m + 8#64)
    (hS : Saved m m') {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → r.StackArea p ∧ ¬InRange (r.off 21576) 48 p) : r.Frame m' :=
  Frame.of_change hc.2.1 hc.2.2.1 hc.2.2.2 (by rw [hsp]; exact hc.1) hout hR hS.2

/-! ## The frame as the executor's regions -/

/-- The frame, slots below it, and the memcpy and memset GOT slots. -/
abbrev frameRegs : List (BitVec 64 × Nat) :=
  [(r.base, frameRegion), (r.base - 16#64, 16), (gotAddr "memcpy", 8), (gotAddr "memset", 8)]

/-- The environment of a state of the frame. -/
abbrev env (m : MachineData) (vars : Nat → BitVec 64 := fun _ ↦ 0) (ret : BitVec 64 := 0) :
    Sym.Env :=
  Sym.Env.ofMachine m r.frameRegs vars ret

theorem env_base0 (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (r.env m vars ret).base 0 = r.base := rfl

theorem env_base1 (m : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) :
    (r.env m vars ret).base 1 = r.base - 16#64 := rfl

/-- **The frame's environment is well formed**, in a state keeping the entry's mapped bytes. -/
theorem frame_wf (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (vars : Nat → BitVec 64) (ret : BitVec 64) : (r.env m vars ret).WF := by
  have hb := r.base_toNat hpre
  have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
  have h0 : Mapped m.dmem r.base frameRegion ∧ NoWrap r.base frameRegion := by
    refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
    · rw [Sym.toNat_add_ofNat _ _ (by rw [frameRegion_eq] at hi; omega)]
      omega
    · rw [Sym.toNat_add_ofNat _ _ (by rw [frameRegion_eq] at hi; omega)]
      rw [frameRegion_eq] at hi
      omega
    · unfold NoWrap
      rw [frameRegion_eq]
      omega
  have h1 : Mapped m.dmem (r.base - 16#64) 16 ∧ NoWrap (r.base - 16#64) 16 := by
    refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · rw [Sym.toNat_add_ofNat _ _ (by omega), hlo]
      omega
    · unfold NoWrap
      omega
  refine Sym.Env.wf_of ⟨h0, h1,
    ⟨fun i hi => hk _ ((r.got hpre).mapped (by simp : "memcpy" ∈ _) i hi),
      ((r.got hpre).1 "memcpy" (by simp)).2.1⟩,
    ⟨fun i hi => hk _ ((r.got hpre).mapped (by simp : "memset" ∈ _) i hi),
      ((r.got hpre).1 "memset" (by simp)).2.1⟩, trivial⟩ ?_
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · change Apart r.base frameRegion (r.base - 16#64) 16
      unfold Apart
      omega
    · exact (r.got_apart_frame hpre (by simp)).symm
    · exact (r.got_apart_frame hpre (by simp)).symm
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact (r.got_apart_below hpre (by simp)).symm
    · exact (r.got_apart_below hpre (by simp)).symm
  · simpa using (r.got hpre).2

/-- The slots `call` and `push` write below the frame: region 1. -/
abbrev frameAliases : List (Sym × Nat × Int) := [(.ptr 0 (-8), 1, 8), (.ptr 0 (-16), 1, 0)]

/-- The frame and loader bytes used by each fresh symbolic block state. -/
@[expose] def frameState (known : List (Reg64 × Sym)) (labels : List (Label × Nat) := [])
    (bounds : List (Sym × Nat) := []) (aliases : List (Sym × Nat × Int) := []) : Sym.SState :=
  ((Sym.init [frameRegion, 16, 8, 8] ((.rsp, .ptr 0 0) :: known) labels bounds
    (frameAliases ++ [(.gotSlot "memcpy", 2, 0), (.gotSlot "memset", 3, 0)] ++ aliases)).withKnownBytes
      2 0 8 (.label "memcpy")).withKnownBytes 3 0 8 (.label "memset")

omit [Labels] in
theorem alias8 :
    r.base + BitVec.ofInt 64 (-8) = (r.base - 16#64) + BitVec.ofInt 64 8 := by
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide, show BitVec.ofInt 64 8 = 8#64 by decide]
  bv_omega

/-- A fresh symbolic frame state with the loader bytes justified by the invariant. -/
theorem match_frame (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {known : List (Reg64 × Sym)} {labels : List (Label × Nat)}
    {bounds : List (Sym × Nat)} {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m vars ret)) known)
    (hlabels : Sym.AllOf (fun p ↦ (r.env m vars ret).base p.2 = (Labels.label p.1).toBitVec) labels)
    (hbounds : Sym.AllOf (fun p ↦ (p.1.eval (r.env m vars ret)).toNat < p.2) bounds)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.env m vars ret) =
      (r.env m vars ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.env m vars ret) (frameState known labels bounds aliases) m := by
  apply Sym.Match.withKnownBytes
  · apply Sym.Match.withKnownBytes
    · apply Sym.match_ofMachine
      · exact ⟨rfl, rfl, rfl, rfl, trivial⟩
      · exact ⟨by
          show rspOf m = r.base + BitVec.ofInt 64 0
          simpa only [BitVec.ofInt_ofNat, BitVec.add_zero] using hF.1, hknown⟩
      · exact hlabels
      · exact hbounds
      · refine ⟨alias8 r, ?_, ?_, ?_, haliases⟩
        · change r.base + BitVec.ofInt 64 (-16) = (r.base - 16#64) + BitVec.ofInt 64 0
          rw [show BitVec.ofInt 64 (-16) = -16#64 by decide, show BitVec.ofInt 64 0 = 0#64 by decide]
          bv_omega
        · simp [Sym.eval, Sym.Env.base, gotAddr]
        · simp [Sym.eval, Sym.Env.base, gotAddr]
    · intro i hi
      simpa [Sym.eval, Sym.Env.base, env, frameRegs] using
        r.got_byte hpre hF.2.2.1 (by simp : "memcpy" ∈ _) hi
  · intro i hi
    simpa [Sym.eval, Sym.Env.base, env, frameRegs] using
      r.got_byte hpre hF.2.2.1 (by simp : "memset" ∈ _) hi

/-- No write of a symbolic state touches the frame's bytes `o .. o + n`. -/
@[expose] def noWriteIn (S : Sym.SState) (o n : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && (decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off))) ||
    (w.r == 1 && decide (w.off + w.n ≤ 16))

/-- **Bytes a block does not write are kept**: the frame's bytes at `o`, where no write of the
block's literal state reaches (`noWriteIn`). -/
theorem bytesAt_kept (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : Sym.SState} (hm : Sym.Match (r.env m vars ret) S m')
    (hwf : (r.env m vars ret).WF) {o : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 21624)
    (h : BytesAt m.dmem (r.off o) bs) (hn : noWriteIn S o bs.length = true) :
    BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hn
  have hw := hn w hwm
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
  rcases hw with ⟨hr', hw⟩ | ⟨hr', hw⟩
  · rw [hr'] at hr
    cases hr
    omega
  · rw [hr'] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    rw [hlo] at h1 h2
    omega

/-- The writes of a symbolic state are in region 0 below the saved registers, or in region 1. -/
@[expose] def frameWrites (S : Sym.SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 21576)) || (w.r == 1 && decide (w.off + w.n ≤ 16))

/-- The places a block's writes (`frameWrites`) cover are in the stack area off the saved
registers. -/
theorem written_area (hpre : r.Pre) {m : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : Sym.SState} (hw : frameWrites S = true) :
    ∀ p, Sym.Written (r.env m vars ret) S p → r.StackArea p ∧ ¬InRange (r.off 21576) 48 p := by
  have hb := r.base_toNat hpre
  rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
  simp only [frameWrites, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw
  rcases hw w hwm with ⟨hw0, hwn⟩ | ⟨hw1, hwn⟩
  · rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 21576) (by decide) (by
      rw [show r.off 0 = r.base by simp [off], Sym.inRange_iff (by omega)]
      omega)
  · rw [hw1] at hr
    cases hr
    have hlo : (r.base - 16#64).toNat = r.base.toNat - 16 := toNat_sub_ofNat (by omega)
    have hs := r.off_toNat hpre (a := 21576) (by decide)
    rw [hlo] at h1 h2
    rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
    omega

/-- **The invariant after a block** run in the frame's environment: RSP the base, the writes in
the frame below the saved registers or in the slots below it (`frameWrites`). -/
theorem Frame.of_match (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.env m vars ret) S m') (hwf : (r.env m vars ret).WF)
    (hsp : S.reg .rsp = some (.ptr 0 0)) (hw : frameWrites S = true) : r.Frame m' :=
  Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2
    (by rw [rspOf, hm.regs .rsp _ hsp]; show r.base + BitVec.ofInt 64 0 = r.base; simp)
    (hm.sameOutside hwf) (r.written_area hpre hw) (hm.kept hwf)

/-- **At a call after a block** run in the frame's environment: RSP 8 below the base. -/
theorem AtCall.of_match (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.env m vars ret) S m') (hwf : (r.env m vars ret).WF)
    (hsp : S.reg .rsp = some (.ptr 0 (-8))) (hw : frameWrites S = true) : r.AtCall m' := by
  have hF' := Frame.of_change hF.2.1 hF.2.2.1 hF.2.2.2 (m' := { m' with regs := m.regs }) hF.1
    (hm.sameOutside hwf) (r.written_area hpre hw) (hm.kept hwf)
  refine ⟨?_, hF'.2.1, hF'.2.2.1, hF'.2.2.2⟩
  rw [rspOf, hm.regs .rsp _ hsp]
  show r.base + BitVec.ofInt 64 (-8) + 8#64 = r.base
  rw [show BitVec.ofInt 64 (-8) = -8#64 by decide]
  bv_omega

end Run

end

end NativeRustcX64.SphincsVerifyProof
