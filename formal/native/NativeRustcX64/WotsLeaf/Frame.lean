module

public import NativeRustcX64.WotsLeaf.Basic
public import NativeRustcX64.Sym.Run
public import NativeRustcX64.Got

/-!
# The frame's facts for calls and blocks

From the run's precondition and the frame's invariant at RSP `sp` (`Run.Pre`, `Run.FrameAt`;
`Run.Frame` at the base, `Run.CallFrame` 8 below it at a callee's entry): the frame's bytes are
mapped and do not wrap (`Run.frame_mapped`), apart from each other, from the round constants and
from a callee's stack (`Run.apart_off`, `Run.apart_rc`, `Run.apart_off_below`); RSP at a callee's
entry leaves it its stack (`Run.stackOk`) and the round constants (`Run.rcAt`). After a callee or
a block that writes only in the stack area off the saved registers, the invariant holds again
(`Run.FrameAt.of_block`, `Run.Frame.of_post`; the writes' places: `Run.inRange_off`,
`Run.inRange_below`), and the bytes it does not write are kept (`bytesAt_of_sameOutside`).

The executor's environment of a state of the frame (`Run.env`): region 0 the frame with the
return address and the stack arguments (`regionSize` bytes from the base), region 1 the 8 bytes
below the base where a call pushes its return address, reached by the alias `ptr 0 (-8)`.
-/

namespace NativeRustcX64.WotsLeafProof

open NativeRustc

public section

/-- Bytes no change covers are kept. -/
theorem bytesAt_of_sameOutside {d d' : DataMem} {a : BitVec 64} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : BytesAt d a bs) (hs : SameOutside d d' R)
    (hR : ∀ i < bs.length, ¬R (a + BitVec.ofNat 64 i)) : BytesAt d' a bs := fun i hi ↦ by
  rw [hs _ (hR i hi)]
  exact h i hi

/-- `SameOutside` of a smaller set of changes. -/
theorem SameOutside.mono {d d' : DataMem} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ p, R p → R' p) : SameOutside d d' R' := fun p hp ↦ h p fun h' ↦ hp (hR p h')

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

theorem addr_add_add (a : BitVec 64) (o i : Nat) :
    a + BitVec.ofNat 64 o + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

namespace Run

theorem frameSize_eq : frameSize = 2760 := rfl
theorem finalizeStack_eq : finalizeStack = 672 := rfl
theorem wotsLeafStack_eq' : wotsLeafStack = 3440 := rfl

/-- **The frame's invariant at RSP `sp`.** -/
@[expose] def FrameAt (r : Run) (sp : BitVec 64) (m : MachineData) : Prop :=
  reg m .rsp = sp ∧ BytesAt m.dmem (r.off 2712) (savedBytes r.m0) ∧
    SameOutside r.m0.dmem m.dmem r.StackArea ∧ Kept r.m0.dmem m.dmem

/-- The frame's invariant at a callee's entry: RSP 8 below the base. -/
abbrev CallFrame (r : Run) (m : MachineData) : Prop := r.FrameAt (r.base - 8#64) m

theorem FrameAt.rsp {r : Run} {sp : BitVec 64} {m : MachineData} (hF : r.FrameAt sp m) :
    rspOf m = sp := hF.1

theorem FrameAt.kept {r : Run} {sp : BitVec 64} {m : MachineData} (hF : r.FrameAt sp m) :
    Kept r.m0.dmem m.dmem := hF.2.2.2

theorem frame_iff (r : Run) (m : MachineData) : r.Frame m ↔ r.FrameAt r.base m := Iff.rfl

variable (r : Run) [Labels]

/-- The frame's base: `frameSize` below RSP at entry, a return address and the callees' stack
below it. -/
theorem base_toNat (hpre : r.Pre) :
    r.base.toNat + 2760 = (rspOf r.m0).toNat ∧ 680 ≤ r.base.toNat ∧
      (rspOf r.m0).toNat + 8 ≤ 2 ^ 64 := by
  have hle := hpre.1.1
  have hw := hpre.1.2.1
  rw [wotsLeafStack_eq'] at hle
  unfold base
  rw [frameSize_eq, toNat_sub_ofNat (by omega)]
  omega

/-- The frame's byte `a`. -/
theorem off_toNat (hpre : r.Pre) {a : Nat} (ha : a < 2784) :
    (r.off a).toNat = r.base.toNat + a := by
  have := r.base_toNat hpre
  have hm := hpre.2.2.2.1
  unfold NoWrap at hm
  exact Sym.toNat_add_ofNat _ _ (by omega)

/-- The region's end: the stack arguments' end does not wrap. -/
theorem base_top (hpre : r.Pre) : r.base.toNat + 2784 ≤ 2 ^ 64 := by
  have := r.base_toNat hpre
  have hm := hpre.2.2.2.1
  unfold NoWrap at hm
  omega

omit [Labels] in
/-- The frame's byte `i` of the bytes at `a`. -/
theorem off_add (a i : Nat) : r.off a + BitVec.ofNat 64 i = r.off (a + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The stack area's start: a return address and `finalizeStack` below the frame. -/
theorem below_toNat (hpre : r.Pre) :
    (stackBelow r.m0 wotsLeafStack).toNat + 680 = r.base.toNat := by
  have := r.base_toNat hpre
  have hle := hpre.1.1
  rw [wotsLeafStack_eq'] at hle ⊢
  unfold stackBelow
  rw [toNat_sub_ofNat (by omega)]
  omega

/-- The stack area's bytes are mapped, in any state keeping the entry's mapped bytes. -/
theorem area_mapped (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {p : BitVec 64}
    (h1 : r.base.toNat ≤ p.toNat + 680) (h2 : p.toNat < r.base.toNat + 2768) :
    (m.dmem.get? p).isSome := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have hp : p = stackBelow r.m0 wotsLeafStack +
      BitVec.ofNat 64 (p.toNat - (stackBelow r.m0 wotsLeafStack).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega
  have hm : (r.m0.dmem.get? (stackBelow r.m0 wotsLeafStack +
      BitVec.ofNat 64 (p.toNat - (stackBelow r.m0 wotsLeafStack).toNat))).isSome :=
    hpre.1.2.2 (p.toNat - (stackBelow r.m0 wotsLeafStack).toNat)
      (by simp only [wotsLeafStack_eq'] at *; omega)
  rw [← hp] at hm
  exact hk _ hm

/-- The stack arguments' bytes are mapped, in any state keeping the entry's mapped bytes. -/
theorem args_mapped (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {p : BitVec 64}
    (h1 : r.base.toNat + 2768 ≤ p.toNat) (h2 : p.toNat < r.base.toNat + 2784) :
    (m.dmem.get? p).isSome := by
  have hb := r.base_toNat hpre
  have hm := hpre.2.2.1
  have hw := hpre.2.2.2.1
  unfold NoWrap at hw
  have h8 : (rspOf r.m0 + 8#64).toNat = (rspOf r.m0).toNat + 8 :=
    Sym.toNat_add_ofNat _ 8 (by omega)
  have hp : p = rspOf r.m0 + 8#64 + BitVec.ofNat 64 (p.toNat - (rspOf r.m0 + 8#64).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega
  have := hm (p.toNat - (rspOf r.m0 + 8#64).toNat) (by omega)
  rw [← hp] at this
  exact hk _ this

/-- **The frame's bytes** `a .. a + n`, the return address and the stack arguments among them, are
mapped and do not wrap. -/
theorem frame_mapped_kept (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {a n : Nat}
    (h : a + n ≤ 2784) : Mapped m.dmem (r.off a) n ∧ NoWrap (r.off a) n := by
  have hb := r.base_toNat hpre
  have he := r.base_top hpre
  refine ⟨fun i hi ↦ ?_, ?_⟩
  · rw [off_add]
    have hi' := r.off_toNat hpre (a := a + i) (by omega)
    by_cases hlt : a + i < 2768
    · exact r.area_mapped hpre hk (by omega) (by omega)
    · exact r.args_mapped hpre hk (by omega) (by omega)
  · unfold NoWrap
    rcases Nat.lt_or_ge a 2784 with ha | ha
    · rw [r.off_toNat hpre ha]
      omega
    · have := (r.off a).isLt
      omega

/-- **The frame's bytes** `a .. a + n` are mapped and do not wrap. -/
theorem frame_mapped (hpre : r.Pre) {sp : BitVec 64} {m : MachineData} (hF : r.FrameAt sp m)
    {a n : Nat} (h : a + n ≤ 2784) : Mapped m.dmem (r.off a) n ∧ NoWrap (r.off a) n :=
  r.frame_mapped_kept hpre hF.2.2.2 h

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'` are apart when their offsets are. -/
theorem apart_off (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 2768) (ha' : a' + n' ≤ 2768)
    (h : a + n ≤ a' ∨ a' + n' ≤ a) : Apart (r.off a) n (r.off a') n' := by
  unfold Apart
  rw [r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)]
  omega

/-- The stack area is the frame, a return address and the `finalizeStack` bytes below it. -/
theorem stackArea_iff (hpre : r.Pre) (p : BitVec 64) :
    r.StackArea p ↔ r.base.toNat ≤ p.toNat + 680 ∧ p.toNat < r.base.toNat + 2760 := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  unfold StackArea
  rw [Sym.inRange_iff (by simp only [wotsLeafStack_eq'] at *; omega)]
  simp only [wotsLeafStack_eq'] at *
  omega

/-- No byte apart from the stack area is in it. -/
theorem not_area_of_apart (hpre : r.Pre) {a : BitVec 64} {n : Nat}
    (h : Apart a n (stackBelow r.m0 wotsLeafStack) (wotsLeafStack + 8)) (hw : NoWrap a n) {i : Nat}
    (hi : i < n) : ¬r.StackArea (a + BitVec.ofNat 64 i) := by
  rw [r.stackArea_iff hpre]
  have hw' := r.below_toNat hpre
  unfold Apart NoWrap at *
  simp only [wotsLeafStack_eq'] at *
  rw [Sym.toNat_add_ofNat _ _ (by omega)]
  omega

omit [Labels] in
/-- An input is apart from the stack area and the return address. -/
theorem input_apart {a : BitVec 64} {n : Nat} (h : WotsLeafPre.Input r.m0 a n) :
    Apart a n (stackBelow r.m0 wotsLeafStack) (wotsLeafStack + 8) := by
  have := h.2.2
  unfold Apart at *
  omega

/-- The bytes at `a`, apart from the stack area, are the entry's. -/
theorem bytesAt_entry (hpre : r.Pre) {sp : BitVec 64} {m : MachineData} (hF : r.FrameAt sp m)
    {a : BitVec 64} {bs : List UInt8} (h : BytesAt r.m0.dmem a bs)
    (hA : Apart a bs.length (stackBelow r.m0 wotsLeafStack) (wotsLeafStack + 8))
    (hw : NoWrap a bs.length) : BytesAt m.dmem a bs :=
  bytesAt_of_sameOutside h hF.2.2.1 fun _ hi ↦ r.not_area_of_apart hpre hA hw hi

/-- What the function may change: `out` and the stack area. -/
@[expose] def Changed (p : BitVec 64) : Prop := InRange r.out 75 p ∨ r.StackArea p

/-- The frame's bytes from `2760` on (the return address and the stack arguments) are the
entry's. -/
theorem bytesAt_top (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.Changed) {a n : Nat}
    (h1 : 2760 ≤ a) (h2 : a + n ≤ 2784) :
    BytesAt m.dmem (r.off a) (bytesOf r.m0.dmem (r.off a) n) := by
  have hb := r.base_toNat hpre
  have hw := r.below_toNat hpre
  obtain ⟨-, hnw, hap⟩ := hpre.2.2.2.2.1
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  have hp := r.off_toNat hpre (a := a + i) (by omega)
  have hn : ¬r.Changed (r.off a + BitVec.ofNat 64 i) := by
    rw [off_add]
    rintro (h | h)
    · unfold NoWrap Apart at *
      rw [show r.out = reg r.m0 .rdi from rfl, Sym.inRange_iff hnw, hp] at h
      simp only [wotsLeafStack_eq'] at hap hw
      omega
    · rw [r.stackArea_iff hpre, hp] at h
      omega
  rw [hs _ hn]
  obtain ⟨hm, -⟩ := r.frame_mapped_kept hpre (fun _ h ↦ h) (a := a) (n := n) h2
  have := hm i hi
  revert this
  cases r.m0.dmem.get? (r.off a + BitVec.ofNat 64 i) <;> simp

/-- **The round constants** are apart from the frame and its callees' stack. -/
theorem apart_rc (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 2768) :
    Apart (r.off a) n rcAddr 192 := by
  obtain ⟨_, hw, hA⟩ := hpre.2.1
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  have hb := r.base_toNat hpre
  unfold Apart NoWrap at *
  simp only [wotsLeafStack_eq'] at *
  omega

/-! ## A callee's entry -/

/-- RSP at a callee's entry, 8 below the base. -/
theorem callSp_toNat (hpre : r.Pre) : (r.base - 8#64).toNat + 8 = r.base.toNat := by
  have := r.base_toNat hpre
  rw [show (8#64) = BitVec.ofNat 64 8 from rfl, toNat_sub_ofNat (by omega)]
  omega

/-- The `n ≤ finalizeStack` bytes below RSP at a callee's entry. -/
theorem stackBelow_toNat (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64) {n : Nat}
    (hn : n ≤ finalizeStack) : (stackBelow m n).toNat + n + 8 = r.base.toNat := by
  rw [finalizeStack_eq] at hn
  have hb := r.base_toNat hpre
  have hc := r.callSp_toNat hpre
  unfold stackBelow
  rw [hsp, toNat_sub_ofNat (by omega)]
  omega

/-- **The callee's stack**: RSP at a callee's entry leaves it `n ≤ finalizeStack` bytes and its
return address. -/
theorem stackOk (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {n : Nat}
    (hn : n ≤ finalizeStack) : StackOk m n := by
  rw [finalizeStack_eq] at hn
  have hb := r.base_toNat hpre
  have hc := r.callSp_toNat hpre
  have hsp : rspOf m = r.base - 8#64 := hF.1
  unfold StackOk
  rw [hsp]
  refine ⟨by omega, by omega, fun i hi ↦ r.area_mapped hpre hF.2.2.2 ?_ ?_⟩
  · rw [Sym.toNat_add_ofNat _ _ (by rw [toNat_sub_ofNat (by omega)]; omega),
      toNat_sub_ofNat (by omega)]
    omega
  · rw [Sym.toNat_add_ofNat _ _ (by rw [toNat_sub_ofNat (by omega)]; omega),
      toNat_sub_ofNat (by omega)]
    omega

/-- What is apart from the stack area is apart from a callee's stack and return address. -/
theorem apart_below (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64) {a : BitVec 64}
    {n N : Nat} (hN : N ≤ finalizeStack)
    (h : Apart a n (stackBelow r.m0 wotsLeafStack) (wotsLeafStack + 8)) :
    Apart a n (stackBelow m N) (N + 8) := by
  have := r.stackBelow_toNat hpre hsp hN
  have := r.below_toNat hpre
  rw [finalizeStack_eq] at hN
  refine apart_of_sub h (by omega) ?_
  simp only [wotsLeafStack_eq'] at *
  omega

/-- The frame's bytes are apart from a callee's stack and return address. -/
theorem apart_off_below (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64)
    {a n N : Nat} (ha : a + n ≤ 2768) (hN : N ≤ finalizeStack) :
    Apart (r.off a) n (stackBelow m N) (N + 8) := by
  have := r.stackBelow_toNat hpre hsp hN
  unfold Apart
  rw [r.off_toNat hpre (by omega)]
  omega

/-- The frame's bytes are apart from a callee's return address. -/
theorem apart_off_ret (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64)
    {a n : Nat} (ha : a + n ≤ 2768) : Apart (r.off a) n (rspOf m) 8 := by
  have := r.callSp_toNat hpre
  unfold Apart
  rw [r.off_toNat hpre (by omega), hsp]
  omega

/-- **The round constants** for a callee using `n ≤ finalizeStack` bytes of stack. -/
theorem rcAt (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {n : Nat}
    (hn : n ≤ finalizeStack) : RcAt m n := by
  obtain ⟨hrc, hw, hA⟩ := hpre.2.1
  have hlen : rcBytes.length = 192 := by
    rw [show rcBytes = Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC from rfl,
      Native.Keccak.Proof.length_wordsBytes]
    rfl
  exact ⟨r.bytesAt_entry hpre hF hrc (hlen ▸ hA) (hlen ▸ hw), hw, r.apart_below hpre hF.1 hn hA⟩

/-- The loader's slots at the function entry. -/
theorem got (hpre : r.Pre) :
    GotAt r.m0 wotsLeafStack
      [(r.out, 75), (reg r.m0 .rsi, 16), (reg r.m0 .r8, (reg r.m0 .r9).toNat),
        (WotsLeafPre.rndPtr r.m0, 16), (WotsLeafPre.valuesPtr r.m0, 16 * 58),
        (rspOf r.m0 + 8#64, 16)] ["memcpy", "memset"] :=
  hpre.2.2.2.2.2.2.2.2.2

/-- GOT slots are apart from the frame and its return address. -/
theorem got_apart_off (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"])
    {a n : Nat} (ha : a + n ≤ 2768) : Apart (gotAddr l) 8 (r.off a) n := by
  have hg := ((r.got hpre).1 l hl).2.2.1
  have hb := r.below_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  simp only [stackBelow] at hb
  apply apart_of_sub hg (by omega)
  simp only [wotsLeafStack_eq'] at *
  omega

/-- A callee reads the same GOT bytes as the caller, with its smaller stack footprint. -/
theorem gotAt (hpre : r.Pre) {m : MachineData} (hF : r.CallFrame m) {n : Nat}
    (hn : n ≤ finalizeStack) {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hl : symbols.Sublist ["memcpy", "memset"])
    (ha : ∀ l ∈ symbols, ∀ a ∈ areas, Apart (gotAddr l) 8 a.1 a.2) :
    GotAt m n areas symbols := by
  apply ((r.got hpre).symbols hl).transport
  · intro l hl' i hi
    have hg := (r.got hpre).1 l (hl.subset hl')
    exact hF.2.2.1 _ (r.not_area_of_apart hpre hg.2.2.1 hg.2.1 hi)
  · intro l hl'
    exact r.apart_below hpre hF.rsp hn ((r.got hpre).1 l (hl.subset hl')).2.2.1
  · exact ha

/-! ## The invariant again -/

/-- A change in the frame's bytes `a .. a + n` before the saved registers is in the stack area,
off the saved registers. -/
theorem inRange_off (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 2712) {p : BitVec 64}
    (h : InRange (r.off a) n p) : r.StackArea p ∧ ¬InRange (r.off 2712) 48 p := by
  have hb := r.base_toNat hpre
  have ho := r.off_toNat hpre (a := a) (by omega)
  have hs := r.off_toNat hpre (a := 2712) (by decide)
  rw [Sym.inRange_iff (by rw [ho]; omega), ho] at h
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

/-- A change in a callee's stack or return address is in the stack area, off the saved
registers. -/
theorem inRange_below (hpre : r.Pre) {m : MachineData} (hsp : rspOf m = r.base - 8#64) {N : Nat}
    (hN : N ≤ finalizeStack) {p : BitVec 64} (h : InRange (stackBelow m N) (N + 8) p) :
    r.StackArea p ∧ ¬InRange (r.off 2712) 48 p := by
  have hb := r.base_toNat hpre
  have hl := r.stackBelow_toNat hpre hsp hN
  have hs := r.off_toNat hpre (a := 2712) (by decide)
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
/-- **The invariant after a block**: RSP `sp'`, the changes in the stack area off the saved
registers, the mapped bytes kept. -/
theorem FrameAt.of_block {sp sp' : BitVec 64} {m m' : MachineData} (hF : r.FrameAt sp m)
    (hsp : reg m' .rsp = sp') {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → r.StackArea p ∧ ¬InRange (r.off 2712) 48 p) (hk : Kept m.dmem m'.dmem) :
    r.FrameAt sp' m' :=
  ⟨hsp, bytesAt_of_sameOutside hF.2.1 hout fun _ hi h ↦ (hR _ h).2 (inRange_self_add
      (by rwa [length_savedBytes] at hi) (by decide)),
    fun p hp ↦ (hout p fun h ↦ hp (hR p h).1).trans (hF.2.2.1 p hp),
    fun p h ↦ hk p (hF.2.2.2 p h)⟩

/-! ## The frame as the executor's regions -/

/-- The environment of a state of the frame: region 0 the frame with the return address and the
stack arguments, region 1 the 8 bytes below it, the `extra` regions. -/
abbrev env (m : MachineData) (extra : List (BitVec 64 × Nat) := []) (vars : Nat → BitVec 64 := fun _ ↦ 0)
    (ret : BitVec 64 := 0) : Sym.Env :=
  Sym.Env.ofMachine m ((r.base, regionSize) :: (r.base - 8#64, 8) :: extra) vars ret

omit [Labels] in
theorem env_base (m : MachineData) (extra : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)
    (ret : BitVec 64) : (r.env m extra vars ret).base 0 = r.base := rfl

omit [Labels] in
theorem env_base1 (m : MachineData) (extra : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64)
    (ret : BitVec 64) : (r.env m extra vars ret).base 1 = r.base - 8#64 := rfl

omit [Labels] in
theorem off_zero : r.off 0 = r.base := by
  simp [off]

/-- The 8 bytes below the base are mapped and do not wrap. -/
theorem slot_mapped (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) :
    Mapped m.dmem (r.base - 8#64) 8 ∧ NoWrap (r.base - 8#64) 8 := by
  have hb := r.base_toNat hpre
  have hc := r.callSp_toNat hpre
  refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, by unfold NoWrap; omega⟩
  · rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega
  · rw [Sym.toNat_add_ofNat _ _ (by omega)]
    omega

/-- **The frame's environment is well formed**, with extra regions apart from it and from each
other. -/
theorem env_wf (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    {extra : List (BitVec 64 × Nat)}
    (hx : Sym.AllOf (fun e : BitVec 64 × Nat ↦ Mapped m.dmem e.1 e.2 ∧ NoWrap e.1 e.2) extra)
    (hxa : Sym.AllOf (fun e : BitVec 64 × Nat ↦ Apart r.base regionSize e.1 e.2 ∧
      Apart (r.base - 8#64) 8 e.1 e.2) extra)
    (hxp : extra.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2)
    (vars : Nat → BitVec 64) (ret : BitVec 64) : (r.env m extra vars ret).WF := by
  have h := r.frame_mapped_kept hpre hk (a := 0) (n := 2784) (by decide)
  rw [off_zero] at h
  have hb := r.base_toNat hpre
  have hc := r.callSp_toNat hpre
  refine Sym.Env.wf_of ⟨h, r.slot_mapped hpre hk, hx⟩ ?_
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ hxp)
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · have := r.base_top hpre
      unfold Apart regionSize
      dsimp only
      omega
    · exact (Sym.mem_of_allOf hxa he).1
  · intro e he
    exact (Sym.mem_of_allOf hxa he).2

/-- The frame's environment without extra regions is well formed. -/
theorem frame_wf (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem)
    (vars : Nat → BitVec 64) (ret : BitVec 64) : (r.env m [] vars ret).WF :=
  r.env_wf hpre hk (extra := []) trivial trivial List.Pairwise.nil vars ret

/-- Both GOT slots are apart from the frame including the caller's stack arguments. -/
theorem got_apart_regions (hpre : r.Pre) {l : Label} (hl : l ∈ ["memcpy", "memset"]) :
    Apart r.base regionSize (gotAddr l) 8 ∧ Apart (r.base - 8#64) 8 (gotAddr l) 8 := by
  have hg := (r.got hpre).1 l hl
  have hs := hg.2.2.1
  have ha := hg.2.2.2 (rspOf r.m0 + 8#64, 16) (by simp)
  have hb := r.below_toNat hpre
  have ht := r.base_top hpre
  have hc := r.callSp_toNat hpre
  have hsp := r.base_toNat hpre
  have h8 : (rspOf r.m0 + 8#64).toNat = (rspOf r.m0).toNat + 8 :=
    Sym.toNat_add_ofNat _ 8 (by omega)
  unfold Apart regionSize at *
  simp only [stackBelow, wotsLeafStack_eq'] at hs ha hb
  omega

/-- The frame invariant preserves the bytes that resolve indirect calls. -/
theorem got_byte (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.StackArea)
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (Sym.byteOf (Labels.label l).toBitVec i) := by
  have hg := (r.got hpre).1 l hl
  rw [hs _ (r.not_area_of_apart hpre hg.2.2.1 hg.2.1 hi)]
  exact (r.got hpre).byte hl hi

/-- Writing the final output also leaves the GOT slots unchanged. -/
theorem got_byte_changed (hpre : r.Pre) {m : MachineData}
    (hs : SameOutside r.m0.dmem m.dmem r.Changed)
    {l : Label} (hl : l ∈ ["memcpy", "memset"]) {i : Nat} (hi : i < 8) :
    m.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      some (Sym.byteOf (Labels.label l).toBitVec i) := by
  have hg := (r.got hpre).1 l hl
  rw [hs _ (by
    rintro (hout | hstack)
    · exact (hg.2.2.2 (r.out, 75) (by simp)).not_inRange hg.2.1
        hpre.2.2.2.2.1.2.1 hi hout
    · exact r.not_area_of_apart hpre hg.2.2.1 hg.2.1 hi hstack)]
  exact (r.got hpre).byte hl hi

/-- A fresh symbolic state for the frame: regions 0 and 1, RSP the base, the alias for a call's
return address, the `known` registers, labels, bounds and aliases as given. -/
@[expose] def frameInit (extra : List Nat := []) (known : List (Reg64 × Sym) := [])
    (labels : List (Label × Nat) := []) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : Sym.SState :=
  Sym.init (regionSize :: 8 :: extra) ((.rsp, .ptr 0 0) :: known) labels bounds
    ((.ptr 0 (-8), (1, 0)) :: aliases)

/-- **A fresh symbolic state for a state of the frame.** -/
theorem match_frame {m : MachineData} (hsp : reg m .rsp = r.base) {extra : List (BitVec 64 × Nat)}
    {sextra : List Nat} (hex : Sym.RegionsOk sextra extra) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {known : List (Reg64 × Sym)} {labels : List (Label × Nat)}
    {bounds : List (Sym × Nat)} {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ m.regs.get64 p.1 = p.2.eval (r.env m extra vars ret)) known)
    (hlabels : Sym.AllOf (fun p ↦ (r.env m extra vars ret).base p.2 = (Labels.label p.1).toBitVec)
      labels)
    (hbounds : Sym.AllOf (fun p ↦ (p.1.eval (r.env m extra vars ret)).toNat < p.2) bounds)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.env m extra vars ret) =
      (r.env m extra vars ret).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.env m extra vars ret) (frameInit sextra known labels bounds aliases) m :=
  Sym.match_ofMachine ⟨rfl, rfl, hex⟩
    ⟨by
      show reg m .rsp = r.base + BitVec.ofInt 64 0
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
      exact hsp, hknown⟩
    hlabels hbounds
    ⟨by
      show r.base + BitVec.ofInt 64 (-8) = r.base - 8#64 + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 (-8) = -8#64 by decide +kernel,
        show BitVec.ofInt 64 0 = 0#64 by decide +kernel, BitVec.add_zero, BitVec.sub_eq_add_neg],
      haliases⟩

/-- No write of a symbolic state touches the frame's bytes `o .. o + n`: its writes in the frame
miss them, its others are inside their regions. -/
@[expose] def noWriteIn (S : Sym.SState) (o n : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && (decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off))) ||
    (w.r != 0 && decide (w.off + w.n ≤ S.regions.getD w.r 0))

/-- **Bytes a block does not write are kept**: the frame's bytes at `o`, where no write of the
block's literal state reaches (`noWriteIn`). -/
theorem bytesAt_kept (hpre : r.Pre) {m m' : MachineData} {extra : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : Sym.SState}
    (hm : Sym.Match (r.env m extra vars ret) S m') (hwf : (r.env m extra vars ret).WF) {o : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 2768) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at hn
  rw [off_add, r.off_toNat hpre (by omega)] at h1 h2
  rcases hn w hwm with ⟨hw0, hw⟩ | ⟨hw1, hw⟩
  · rw [hw0] at hr
    cases hr
    omega
  · have hsz : w.off + w.n ≤ sz := by
      cases hS : S.regions[w.r]? with
      | none =>
        rw [List.getD_eq_getElem?_getD, hS, Option.getD_none] at hw
        omega
      | some n =>
        rw [List.getD_eq_getElem?_getD, hS, Option.getD_some] at hw
        obtain ⟨b', hb'⟩ := hm.regions _ _ hS
        rw [hb'] at hr
        cases hr
        exact hw
    have hd := hwf.disjoint 0 w.r r.base b regionSize sz (Ne.symm hw1) rfl hr
    unfold regionSize at hd
    omega

/-- The writes of a symbolic state: in region 0 below the saved registers, or in region 1. -/
@[expose] def frameWrites (S : Sym.SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 2712)) || (w.r == 1 && decide (w.off + w.n ≤ 8))

end Run

end

end NativeRustcX64.WotsLeafProof
