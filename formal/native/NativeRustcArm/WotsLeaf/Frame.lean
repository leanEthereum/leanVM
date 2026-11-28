module

public import NativeRustcArm.WotsLeaf.Basic
public import NativeRustcArm.Sym.Run

/-!
# The frame's facts for calls and blocks

From the run's precondition and the frame's invariant (`Run.Pre`, `Run.Frame`): the frame's bytes
are mapped and do not wrap (`Run.frame_mapped`), apart from each other, from the round constants
and from the callees' stack (`Run.apart_off`, `Run.apart_rc`, `Run.apart_off_below`); SP leaves
the callees their stack (`Run.stackOk`) and the round constants (`Run.rcAt`). After a callee or a block that writes only in the stack area off the saved registers,
the invariant holds again (`Run.Frame.of_post`, `Run.Frame.of_block`; the writes' places:
`Run.inRange_off`, `Run.inRange_below`), and the bytes it does not write are kept
(`bytesAt_of_sameOutside`).
-/

namespace NativeRustcArm.WotsLeafProof

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

theorem sp_toNat (m : MachineData) : m.regs.SP.toBitVec.toNat = m.regs.SP.toNat := rfl

theorem frameSize_eq : frameSize = 2752 := rfl
theorem finalizeStack_eq : finalizeStack = 576 := rfl
theorem wotsLeafStack_eq' : wotsLeafStack = 3328 := rfl

variable (r : Run) [Labels]

/-- The frame's base: `frameSize` below SP at entry, the callees' stack below it. -/
theorem base_toNat (hpre : r.Pre) :
    r.base.toNat + 2752 = r.m0.regs.SP.toNat ∧ 576 ≤ r.base.toNat := by
  have hle := hpre.1.2.1
  rw [wotsLeafStack_eq'] at hle
  unfold base
  rw [frameSize_eq, toNat_sub_ofNat (by rw [sp_toNat]; omega), sp_toNat]
  omega

/-- The frame's byte `a`. -/
theorem off_toNat (hpre : r.Pre) {a : Nat} (ha : a ≤ 2752) :
    (r.off a).toNat = r.base.toNat + a := by
  have := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  exact Sym.toNat_add_ofNat _ _ (by omega)

/-- The stack area's start: `finalizeStack` below the frame. -/
theorem below_toNat (hpre : r.Pre) :
    (stackBelow r.m0 wotsLeafStack).toNat + 576 = r.base.toNat := by
  have := r.base_toNat hpre
  have hle := hpre.1.2.1
  rw [wotsLeafStack_eq'] at hle ⊢
  unfold stackBelow
  rw [toNat_sub_ofNat (by rw [sp_toNat]; omega), sp_toNat]
  omega

/-- The stack area's bytes are mapped, in any state of the frame. -/
theorem area_mapped (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {p : BitVec 64}
    (h1 : r.base.toNat ≤ p.toNat + 576) (h2 : p.toNat < r.base.toNat + 2752) :
    (m.dmem.get? p).isSome := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
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

/-- **The frame's bytes** `a .. a + n` are mapped and do not wrap. -/
theorem frame_mapped_kept (hpre : r.Pre) {m : MachineData} (hk : Kept r.m0.dmem m.dmem) {a n : Nat}
    (h : a + n ≤ 2752) : Mapped m.dmem (r.off a) n ∧ NoWrap (r.off a) n := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have ho := r.off_toNat hpre (a := a) (by omega)
  refine ⟨fun i hi ↦ r.area_mapped hpre hk ?_ ?_, ?_⟩
  · rw [Sym.toNat_add_ofNat _ _ (by omega), ho]
    omega
  · rw [Sym.toNat_add_ofNat _ _ (by omega), ho]
    omega
  · unfold NoWrap
    omega

/-- **The frame's bytes** `a .. a + n` are mapped and do not wrap. -/
theorem frame_mapped (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n : Nat}
    (h : a + n ≤ 2752) : Mapped m.dmem (r.off a) n ∧ NoWrap (r.off a) n :=
  r.frame_mapped_kept hpre hF.2.2.2.2 h

/-- The frame's bytes `a .. a + n` and `a' .. a' + n'` are apart when their offsets are. -/
theorem apart_off (hpre : r.Pre) {a n a' n' : Nat} (ha : a + n ≤ 2752) (ha' : a' + n' ≤ 2752)
    (h : a + n ≤ a' ∨ a' + n' ≤ a) : Apart (r.off a) n (r.off a') n' := by
  unfold Apart
  rw [r.off_toNat hpre (by omega), r.off_toNat hpre (by omega)]
  omega

/-- The stack area is the frame and the `finalizeStack` bytes below it. -/
theorem stackArea_iff (hpre : r.Pre) (p : BitVec 64) :
    r.StackArea p ↔ r.base.toNat ≤ p.toNat + 576 ∧ p.toNat < r.base.toNat + 2752 := by
  have hw := r.below_toNat hpre
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  unfold StackArea
  rw [Sym.inRange_iff (by simp only [wotsLeafStack_eq'] at *; omega)]
  simp only [wotsLeafStack_eq'] at *
  omega

/-- No byte apart from the stack area is in it. -/
theorem not_area_of_apart (hpre : r.Pre) {a : BitVec 64} {n : Nat}
    (h : Apart a n (stackBelow r.m0 wotsLeafStack) wotsLeafStack) (hw : NoWrap a n) {i : Nat}
    (hi : i < n) : ¬r.StackArea (a + BitVec.ofNat 64 i) := by
  rw [r.stackArea_iff hpre]
  have hw' := r.below_toNat hpre
  unfold Apart NoWrap at *
  simp only [wotsLeafStack_eq'] at *
  rw [Sym.toNat_add_ofNat _ _ (by omega)]
  omega

/-- The bytes at `a`, apart from the stack area, are the entry's. -/
theorem bytesAt_entry (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a : BitVec 64}
    {bs : List UInt8} (h : BytesAt r.m0.dmem a bs)
    (hA : Apart a bs.length (stackBelow r.m0 wotsLeafStack) wotsLeafStack) (hw : NoWrap a bs.length) :
    BytesAt m.dmem a bs :=
  bytesAt_of_sameOutside h hF.2.2.2.1 fun _ hi ↦ r.not_area_of_apart hpre hA hw hi

omit [Labels] in
/-- SP inside the function is the frame's base. -/
theorem sp_eq {m : MachineData} (hF : r.Frame m) : m.regs.SP.toNat = r.base.toNat := by
  rw [← sp_toNat, hF.1]

/-- SP inside the function leaves `n ≤ finalizeStack` bytes to a callee. -/
theorem stackOk (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {n : Nat}
    (hn : n ≤ finalizeStack) : StackOk m n := by
  rw [finalizeStack_eq] at hn
  have hb := r.base_toNat hpre
  have h16 := hpre.1.1
  have := r.m0.regs.SP.toNat_lt
  unfold StackOk
  rw [r.sp_eq hF, hF.1]
  refine ⟨by omega, by omega, fun i hi ↦ r.area_mapped hpre hF.2.2.2.2 ?_ ?_⟩
  · rw [Sym.toNat_add_ofNat _ _ (by rw [toNat_sub_ofNat (by omega)]; omega),
      toNat_sub_ofNat (by omega)]
    omega
  · rw [Sym.toNat_add_ofNat _ _ (by rw [toNat_sub_ofNat (by omega)]; omega),
      toNat_sub_ofNat (by omega)]
    omega

/-- The `n ≤ finalizeStack` bytes below SP inside the function. -/
theorem stackBelow_toNat (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {n : Nat}
    (hn : n ≤ finalizeStack) : (stackBelow m n).toNat + n = r.base.toNat := by
  rw [finalizeStack_eq] at hn
  have hb := r.base_toNat hpre
  unfold stackBelow
  rw [hF.1, toNat_sub_ofNat (by omega)]
  omega

/-- What is apart from the stack area is apart from a callee's stack. -/
theorem apart_below (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a : BitVec 64} {n N : Nat}
    (hN : N ≤ finalizeStack) (h : Apart a n (stackBelow r.m0 wotsLeafStack) wotsLeafStack) :
    Apart a n (stackBelow m N) N := by
  have := r.stackBelow_toNat hpre hF hN
  have := r.below_toNat hpre
  rw [finalizeStack_eq] at hN
  refine apart_of_sub h (by omega) ?_
  simp only [wotsLeafStack_eq'] at *
  omega

/-- The frame's bytes are apart from a callee's stack. -/
theorem apart_off_below (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {a n N : Nat}
    (ha : a + n ≤ 2752) (hN : N ≤ finalizeStack) : Apart (r.off a) n (stackBelow m N) N := by
  have := r.stackBelow_toNat hpre hF hN
  unfold Apart
  rw [r.off_toNat hpre (by omega)]
  omega

/-- **The round constants** for a callee using `n ≤ finalizeStack` bytes of stack. -/
theorem rcAt (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {n : Nat}
    (hn : n ≤ finalizeStack) : RcAt m n := by
  obtain ⟨hrc, hw, hA⟩ := hpre.2.1
  have hlen : rcBytes.length = 192 := by
    rw [show rcBytes = Native.Keccak.wordsBytes LeanVM.Parameters.keccakRC from rfl,
      Native.Keccak.Proof.length_wordsBytes]
    rfl
  exact ⟨r.bytesAt_entry hpre hF hrc (hlen ▸ hA) (hlen ▸ hw), hw, r.apart_below hpre hF hn hA⟩

/-- The frame's bytes are apart from the round constants. -/
theorem apart_rc (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 2752) :
    Apart (r.off a) n rcAddr 192 := by
  obtain ⟨_, _, hA⟩ := hpre.2.1
  have := r.below_toNat hpre
  have := r.off_toNat hpre (a := a) (by omega)
  unfold Apart at *
  simp only [wotsLeafStack_eq'] at *
  omega

/-! ## The invariant again -/

/-- A change in the frame's bytes `a .. a + n` before the saved registers is in the stack area,
off the saved registers. -/
theorem inRange_off (hpre : r.Pre) {a n : Nat} (ha : a + n ≤ 2656) {p : BitVec 64}
    (h : InRange (r.off a) n p) : r.StackArea p ∧ ¬InRange (r.off 2656) 96 p := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have ho := r.off_toNat hpre (a := a) (by omega)
  have hs := r.off_toNat hpre (a := 2656) (by decide)
  rw [Sym.inRange_iff (by rw [ho]; omega), ho] at h
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

/-- A change in a callee's stack is in the stack area, off the saved registers. -/
theorem inRange_below (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {N : Nat}
    (hN : N ≤ finalizeStack) {p : BitVec 64} (h : InRange (stackBelow m N) N p) :
    r.StackArea p ∧ ¬InRange (r.off 2656) 96 p := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hl := r.stackBelow_toNat hpre hF hN
  have hs := r.off_toNat hpre (a := 2656) (by decide)
  rw [finalizeStack_eq] at hN
  rw [Sym.inRange_iff (by omega)] at h
  rw [r.stackArea_iff hpre, Sym.inRange_iff (by rw [hs]; omega), hs]
  omega

omit [Labels] in
theorem length_savedBytes (m : MachineData) : (savedBytes m).length = 96 := by
  rw [savedBytes, Native.Keccak.Proof.length_wordsBytes]
  rfl

omit [Labels] in
variable {r} in
/-- **The invariant after a block**: SP and X29 as they were, the changes in the stack area off
the saved registers, the mapped bytes kept. -/
theorem Frame.of_block {m m' : MachineData} (hF : r.Frame m)
    (hsp : m'.regs.SP.toBitVec = r.base) (hx29 : (m'.regs.getXReg .X29).toBitVec = r.off 2656)
    {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → r.StackArea p ∧ ¬InRange (r.off 2656) 96 p) (hk : Kept m.dmem m'.dmem) :
    r.Frame m' :=
  ⟨hsp, hx29, bytesAt_of_sameOutside hF.2.2.1 hout fun _ hi h ↦ (hR _ h).2 (inRange_self_add
      (by rwa [length_savedBytes] at hi) (by decide)),
    fun p hp ↦ (hout p fun h ↦ hp (hR p h).1).trans (hF.2.2.2.1 p hp),
    fun p h ↦ hk p (hF.2.2.2.2 p h)⟩

omit [Labels] in
variable {r} in
/-- **The invariant after a call**: the callee kept SP, X29 and the mapped bytes, and changed
bytes only in the stack area off the saved registers. -/
theorem Frame.of_post {m m' : MachineData} (hF : r.Frame m) (hS : Saved m m')
    {R : BitVec 64 → Prop} (hout : SameOutside m.dmem m'.dmem R)
    (hR : ∀ p, R p → r.StackArea p ∧ ¬InRange (r.off 2656) 96 p) : r.Frame m' :=
  hF.of_block (by rw [hS.2.1]; exact hF.1) (by rw [hS.1 .X29 rfl]; exact hF.2.1) hout hR
    hS.2.2

/-! ## The frame as the executor's region 0 -/

/-- The environment of a state of the frame, its region 0 the frame, then the regions `rest`. -/
abbrev envR (m : MachineData) (rest : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64 := fun _ ↦ 0) :
    Sym.Env :=
  Sym.Env.ofMachine m ((r.base, 2752) :: rest) vars

/-- The environment of a state of the frame, its region 0 the frame. -/
abbrev env (m : MachineData) (vars : Nat → BitVec 64 := fun _ ↦ 0) : Sym.Env := r.envR m [] vars

omit [Labels] in
theorem env_base (m : MachineData) (vars : Nat → BitVec 64) : (r.env m vars).base 0 = r.base := rfl

omit [Labels] in
theorem envR_base (m : MachineData) (rest : List (BitVec 64 × Nat)) (vars : Nat → BitVec 64) :
    (r.envR m rest vars).base 0 = r.base := rfl

omit [Labels] in
theorem off_zero : r.off 0 = r.base := by
  simp [off]

/-- **The frame's environment with more regions is well formed**: they are mapped, do not wrap,
are apart from the frame and from each other. -/
theorem frame_wfR (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {rest : List (BitVec 64 × Nat)}
    (hrest : Sym.AllOf (fun e : BitVec 64 × Nat ↦ Mapped m.dmem e.1 e.2 ∧ NoWrap e.1 e.2) rest)
    (hap : ∀ e ∈ rest, Apart r.base 2752 e.1 e.2)
    (hd : rest.Pairwise fun e e' ↦ Apart e.1 e.2 e'.1 e'.2) (vars : Nat → BitVec 64) :
    (r.envR m rest vars).WF := by
  have h := r.frame_mapped hpre hF (a := 0) (n := 2752) (by decide)
  rw [off_zero] at h
  exact Sym.Env.wf_of ⟨h, hrest⟩ (List.pairwise_cons.mpr ⟨hap, hd⟩)

/-- **The frame's environment is well formed.** -/
theorem frame_wf (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) (vars : Nat → BitVec 64) :
    (r.env m vars).WF :=
  r.frame_wfR hpre hF (rest := []) trivial (fun _ h ↦ by cases h) List.Pairwise.nil vars

/-- The frame's base is 16-byte aligned. -/
theorem base_aligned (hpre : r.Pre) : r.base.toNat % 16 = 0 := by
  have hb := r.base_toNat hpre
  have h16 := hpre.1.1
  omega

/-- **A fresh symbolic state for a state of the frame**, with more regions: region 0 the frame
(aligned), SP its base, the `known` registers, labels, bounds and aliases as given. -/
theorem match_frameR (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {vars : Nat → BitVec 64}
    {rest : List (BitVec 64 × Nat)} {srest : List (Nat × Bool)} (hrest : Sym.RegionsOk srest rest)
    {known : List (XReg × Sym)} {labels : List (Label × Nat)} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.envR m rest vars))
      known)
    (hlabels : Sym.AllOf (fun p ↦ (r.envR m rest vars).base p.2 = (Labels.label p.1).toBitVec)
      labels)
    (hbounds : Sym.AllOf (fun p ↦ (p.1.eval (r.envR m rest vars)).toNat < p.2) bounds)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.envR m rest vars) =
      (r.envR m rest vars).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.envR m rest vars)
      (Sym.init ((2752, true) :: srest) (.ptr 0 0) known labels bounds aliases) m :=
  Sym.match_ofMachine ⟨rfl, fun _ ↦ r.base_aligned hpre, hrest⟩
    (by show m.regs.SP.toBitVec = r.base + BitVec.ofInt 64 0; simp only [BitVec.ofInt_ofNat,
      BitVec.add_zero]; exact hF.1)
    hknown hlabels hbounds haliases

/-- **A fresh symbolic state for a state of the frame**: region 0 the frame (aligned), SP its
base, the `known` registers, labels, bounds and aliases as given. -/
theorem match_frame (hpre : r.Pre) {m : MachineData} (hF : r.Frame m) {vars : Nat → BitVec 64}
    {known : List (XReg × Sym)} {labels : List (Label × Nat)} {bounds : List (Sym × Nat)}
    {aliases : List (Sym × Nat × Int)}
    (hknown : Sym.AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec = p.2.eval (r.env m vars)) known)
    (hlabels : Sym.AllOf (fun p ↦ (r.env m vars).base p.2 = (Labels.label p.1).toBitVec) labels)
    (hbounds : Sym.AllOf (fun p ↦ (p.1.eval (r.env m vars)).toNat < p.2) bounds)
    (haliases : Sym.AllOf (fun p ↦ p.1.eval (r.env m vars) =
      (r.env m vars).base p.2.1 + BitVec.ofInt 64 p.2.2) aliases) :
    Sym.Match (r.env m vars) (Sym.init [(2752, true)] (.ptr 0 0) known labels bounds aliases) m :=
  r.match_frameR hpre hF (srest := []) trivial hknown hlabels hbounds haliases

/-- No write of a symbolic state touches the frame's bytes `o .. o + n`. -/
@[expose] def noWriteIn (S : Sym.SState) (o n : Nat) : Bool :=
  S.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + n ≤ w.off)

/-- **Bytes a block does not write are kept**: the frame's bytes at `o`, where no write of the
block's literal state reaches (`noWriteIn`). -/
theorem bytesAt_kept (hpre : r.Pre) {m m' : MachineData} {vars : Nat → BitVec 64}
    {S : Sym.SState} (hm : Sym.Match (r.env m vars) S m') (hwf : (r.env m vars).WF) {o : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 2752) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hn
  have hw := hn w hwm
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
  rcases hr' : w.r with _ | k
  · rw [hr'] at hr
    cases hr
    rw [hr'] at hw
    omega
  · rw [hr'] at hr
    simp at hr

/-- Each write of a symbolic state lies in its region. -/
@[expose] def inRegions (S : Sym.SState) : Bool :=
  S.mem.all fun w ↦ match S.regions[w.r]? with
    | some (sz, _) => decide (w.off + w.n ≤ sz)
    | none => false

/-- **Bytes a block does not write are kept**, in the frame's environment with more regions:
the frame's bytes at `o`, where no write of the block's literal state reaches. -/
theorem bytesAt_keptR (hpre : r.Pre) {m m' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {S : Sym.SState} (hm : Sym.Match (r.envR m rest vars) S m')
    (hwf : (r.envR m rest vars).WF) (hin : inRegions S = true) {o : Nat}
    {bs : List UInt8} (ho : o + bs.length ≤ 2752) (h : BytesAt m.dmem (r.off o) bs)
    (hn : noWriteIn S o bs.length = true) : BytesAt m'.dmem (r.off o) bs := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  have hoff := r.off_toNat hpre (a := o) (by omega)
  refine bytesAt_of_sameOutside h (hm.sameOutside hwf) fun i hi ⟨w, hwm, b, sz, hr, h1, h2⟩ ↦ ?_
  simp only [noWriteIn, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hn
  have hw := hn w hwm
  have hi' := List.all_eq_true.mp hin w hwm
  rw [Sym.toNat_add_ofNat _ _ (by omega), hoff] at h1 h2
  rcases hr' : w.r with _ | k
  · rw [hr'] at hr
    cases hr
    rw [hr'] at hw
    omega
  · rw [hr'] at hr hi'
    have hd := hwf.disjoint 0 (k + 1) r.base b 2752 sz (by omega) rfl hr
    cases hs : S.regions[k + 1]? with
    | none => rw [hs] at hi'; cases hi'
    | some p =>
      obtain ⟨sz', al⟩ := p
      rw [hs] at hi'
      obtain ⟨b', hb', -⟩ := hm.regions (k + 1) sz' al hs
      rw [hr] at hb'
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      simp only [decide_eq_true_eq] at hi'
      omega

/-- The writes of a symbolic state are in region 0 below the saved registers. -/
@[expose] def frameWrites (S : Sym.SState) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 2656)

/-- **The invariant after a block** run in the frame's environment: SP the base, X29 the saved
registers' address, the writes in the frame below them (`frameWrites`, decided on the literal
state). -/
theorem Frame.of_match (hpre : r.Pre) {m m' : MachineData} (hF : r.Frame m)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {S : Sym.SState} (hm : Sym.Match (r.envR m rest vars) S m') (hwf : (r.envR m rest vars).WF)
    (hsp : S.sp = .ptr 0 0) (hx29 : S.reg .X29 = some (.ptr 0 2656))
    (hw : frameWrites S = true) : r.Frame m' := by
  have hb := r.base_toNat hpre
  have := r.m0.regs.SP.toNat_lt
  refine hF.of_block ?_ ?_ (hm.sameOutside hwf) ?_ (hm.kept hwf)
  · rw [hm.sp, hsp]
    show r.base + BitVec.ofInt 64 0 = r.base
    simp
  · rw [hm.regs .X29 _ hx29]
    rfl
  · rintro p ⟨w, hwm, b, sz, hr, h1, h2⟩
    simp only [frameWrites, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hw
    obtain ⟨hw0, hwn⟩ := hw w hwm
    rw [hw0] at hr
    cases hr
    exact r.inRange_off hpre (a := 0) (n := 2656) (by decide) (by
      rw [off_zero, Sym.inRange_iff (by omega)]
      omega)

end Run

end

end NativeRustcArm.WotsLeafProof
