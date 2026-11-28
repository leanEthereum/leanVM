module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeVm.Equiv.Field
public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Spec.Bus

/-!
# `bus.rs`'s proofs: what they share (x86-64)

A function's state between its prologue and epilogue (`Body`): its frame (`Transcript.Frame`:
RSP at an offset of the `F` bytes below the entry's RSP, the pushed registers in their slots, the
return address and the other callee-saved registers the entry's) and memory changed only in its
`N` bytes of stack. The prologue makes it (`Body.of_prologue`), a block writing into the frame
keeps it (`Body.of_block`), and so does a callee changing only its stack (`Body.call`); the
epilogue returns with the entry's registers (`Body.epilogue`). Arguments apart from the stack
stay readable and apart from a callee's stack (`Body.sliceOk`, `Body.readable`,
`Body.offStack`) and read as at the entry (`Body.slice_eq`). Then: an `E` element compared by
`xor`, `or`, `sete` (`sete_ew`).
-/

namespace NativeRustcVmX64.Bus

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript

@[expose] public section

/-- **A function's body**: its frame, memory changed only in its `N` bytes of stack. -/
structure Body (m0 : MachineData) (F N : Nat) (slots : Slots) (o : Nat) (d : MachineData) :
    Prop where
  fr : Frame m0 F slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 N) N)

end

public section

variable {m0 d d' : MachineData} {F N : Nat} {slots : Slots}

theorem inRange_le {a q : BitVec 64} {n n' : Nat} (h : NativeRustcVm.InRange a n q)
    (hn : n ≤ n') : NativeRustcVm.InRange a n' q := by
  unfold NativeRustcVm.InRange at h ⊢
  omega

/-- **Bytes apart from the stack** are the entry's in a state that changed only the stack. -/
theorem get_keep (hst : StackOk m0 N)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 N) N))
    {a : BitVec 64} {n : Nat} (ha : NativeRustcVm.Apart a n (stackBelow m0 N) (N + 8))
    (hw : NativeRustcVm.NoWrap a n) {i : Nat} (hi : i < n) :
    d.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  hs _ fun h ↦ NativeRustcVm.Apart.not_inRange_add ha hw (noWrap_stackBelow hst) hi
    (inRange_le h (by omega))

theorem belowRet_of_pro {o : Nat} {S : SState} (h : ProOk F o slots S = true) :
    belowRet F S = true := by
  simp only [ProOk, Bool.and_eq_true] at h
  exact h.1.1.2

theorem belowRet_of_mid {o : Nat} {S : SState} (h : MidOk F o slots S = true) :
    belowRet F S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- A write of a block into region 0 below its offset `F` is in the frame. -/
theorem written_low [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hw : ∀ w ∈ S.mem, w.r = 0) (hbr : belowRet F S = true) {q : BitVec 64}
    (h : Written (frameEnv m0 d F rest vars ret) S q) :
    NativeRustcVm.InRange (stackBelow m0 F) F q := by
  obtain ⟨w, hwm, b, sz, hb, j, h1, h2, rfl⟩ := written_off hwf h
  have hr := hw w hwm
  have hnw := hwf.noWrap 0 (stackBelow m0 F) (F + 8) rfl
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have := belowRet_spec hbr w hwm hr
  exact inRange_off_self (by omega) (by omega)

/-- **The prologue** makes the body. -/
theorem Body.of_prologue [Labels] (hst : StackOk m0 N) (hF : F ≤ N)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    {o : Nat} (hwf : (frameEnv m0 m0 F rest vars ret).WF)
    (hm : Match (frameEnv m0 m0 F rest vars ret) S d) (hS : ProOk F o slots S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F)
    (hcs : ∀ p ∈ slots, calleeSaved p.2 = true) : Body m0 F N slots o d where
  fr := Frame.of_prologue Frame.entry hwf hm hS hle hcs
  same _ hq := hm.get?_mem0 hwf fun hW ↦
    hq (inRange_frame_stack hst.2.1 hst.1 hF (written_low hwf hw (belowRet_of_pro hS) hW))

/-- **A block writing into the frame** keeps the body. -/
theorem Body.of_block [Labels] (hst : StackOk m0 N) (hF : F ≤ N) {o : Nat}
    (hb : Body m0 F N slots o d) {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} {o' : Nat} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hS : MidOk F o' slots S = true)
    (hw : ∀ w ∈ S.mem, w.r = 0) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Body m0 F N slots o' d' where
  fr := Frame.of_block hb.fr hwf hm hS hle
  same q hq := (hm.get?_mem0 hwf fun hW ↦
    hq (inRange_frame_stack hst.2.1 hst.1 hF (written_low hwf hw (belowRet_of_mid hS) hW))).trans
      (hb.same q hq)

/-- RSP at a call is the frame's base. -/
theorem Body.sp0 (hb : Body m0 F N slots 0 d) : rspOf d = stackBelow m0 F := by
  rw [hb.fr.sp, off_zero]

/-- **A callee changing only its stack** keeps the body. -/
theorem Body.call (hst : StackOk m0 N) (hF : F ≤ N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    (hch : Changes d d' S' 0 0) (hle : ∀ p ∈ slots, p.1 + 8 ≤ F) : Body m0 F N slots 8 d' := by
  have hsp := hb.sp0
  have hz : ∀ q : BitVec 64, ¬ NativeRustcVm.InRange 0 0 q := fun q h ↦ by
    unfold NativeRustcVm.InRange at h; omega
  refine ⟨Frame.call hb.fr hsv hrsp hch (fun q hq ↦ ?_) (frame_noWrap hst hF) hle, fun q hq ↦ ?_⟩
  · rcases hq with hq | hq
    · exact absurd hq (hz q)
    · exact (inRange_callee hsp hst.2.1 hst.1 hFS hq).2
  · refine (hch q fun h ↦ hq ?_).trans (hb.same q hq)
    rcases h with h | h
    · exact absurd h (hz q)
    · exact (inRange_callee hsp hst.2.1 hst.1 hFS h).1

/-- A callee's stack below the frame. -/
theorem Body.stackOk (hst : StackOk m0 N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) : StackOk d S' :=
  stackOk_callee hst hb.fr.kept hb.sp0 hFS

/-- Bytes readable at the entry stay readable. -/
theorem Body.readable {o : Nat} (hb : Body m0 F N slots o d) {a : BitVec 64} {n : Nat}
    (h : Readable m0 a n) : Readable d a n :=
  ⟨Mapped.keeps h.1 hb.fr.kept, h.2⟩

/-- Bytes apart from the stack are apart from a callee's. -/
theorem Body.offStack (hst : StackOk m0 N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) {a : BitVec 64} {n : Nat} (h : OffStack m0 a n N) : OffStack d a n S' :=
  apart_callee h hb.sp0 hst.1 hFS

/-- A slice of the entry's, for a callee. -/
theorem Body.sliceOk (hst : StackOk m0 N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) {a n : BitVec 64} (h : SliceOk m0 a n N) : SliceOk d a n S' :=
  ⟨hb.readable h.1, hb.offStack hst hFS h.2⟩

/-- A slice apart from the stack reads as at the entry. -/
theorem Body.slice_eq (hst : StackOk m0 N) {o : Nat} (hb : Body m0 F N slots o d)
    {a n : BitVec 64} (h : SliceOk m0 a n N) : slice d a n = slice m0 a n :=
  congrArg List.toArray (NativeRustcVm.ewsOf_congr fun _ hi ↦ get_keep hst hb.same h.2 h.1.2 hi)

/-- **The epilogue** (no write): the entry's registers, RSP above the return address, memory
changed only in the stack. -/
theorem Body.epilogue [Labels] {o : Nat} (hb : Body m0 F N slots o d)
    {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 d F rest vars ret).WF) (hm : Match (frameEnv m0 d F rest vars ret) S d')
    (hS : EpiOk F slots S = true) (hmem : S.mem = []) :
    Saved m0 d' ∧ rspOf d' = rspOf m0 + 8#64 ∧
      NativeRustcVm.SameOutside m0.dmem d'.dmem (NativeRustcVm.InRange (stackBelow m0 N) N) := by
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hb.fr hwf hm hS
  have hd : d'.dmem = d.dmem := hm.dmem_eq hwf hmem
  exact ⟨hsv, hrsp, fun q hq ↦ by rw [hd]; exact hb.same q hq⟩

/-- The frame's environment, without other regions, is well formed. -/
theorem wf0 [Labels] (hst : StackOk m0 N) (hF : F ≤ N) (hk : Kept m0.dmem d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 d F [] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst hF) hk, frame_noWrap hst hF⟩ (by simp)
    (List.pairwise_singleton _ _)

/-- The frame's environment with one more region, readable and apart from the stack. -/
theorem wf1 [Labels] (hst : StackOk m0 N) (hF : F ≤ N) (hk : Kept m0.dmem d.dmem)
    {a : BitVec 64} {n : Nat} (hr : Readable m0 a n)
    (hap : NativeRustcVm.Apart a n (stackBelow m0 N) (N + 8))
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 d F [(a, n)] vars ret).WF :=
  frame_wf ⟨Mapped.keeps (frame_mapped hst hF) hk, frame_noWrap hst hF⟩
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨Mapped.keeps hr.1 hk, hr.2⟩)
    (List.pairwise_pair.mpr (Apart.symm' (apart_frame hap hst.1 hF)))

/-! ## The frame's words and arrays -/

/-- The frame's bytes are not in a callee's stack below it. -/
theorem not_callee (hst : StackOk m0 N) {n' j : Nat} (hsp : rspOf d = stackBelow m0 F)
    (hn : F + n' ≤ N) (hj : j < F + 8) :
    ¬NativeRustcVm.InRange (stackBelow d n') n' (off (stackBelow m0 F) j) := fun h ↦
  (inRange_callee hsp hst.2.1 hst.1 hn h).2
    (inRange_off_self hj (by have := hst.1; have := hst.2.1; omega))

/-- Words at offsets of the frame. -/
@[expose] def FrameWords (m0 : MachineData) (F : Nat) (d : DataMem) (ws : List (Nat × UInt64)) : Prop :=
  ∀ p ∈ ws, NativeRustcVm.WordAt d (off (stackBelow m0 F) p.1) p.2

/-- **The frame's words across a callee** changing only its stack. -/
theorem FrameWords.call (hst : StackOk m0 N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) (hch : Changes d d' S' 0 0) {ws : List (Nat × UInt64)}
    (hws : ∀ p ∈ ws, p.1 + 8 ≤ F + 8) (h : FrameWords m0 F d.dmem ws) :
    FrameWords m0 F d'.dmem ws := by
  intro p hp
  refine bytesAt_congr (h p hp) fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  refine hch _ fun hq ↦ ?_
  rcases hq with hq | hq
  · exact absurd hq (by unfold NativeRustcX64.InRange; omega)
  · exact not_callee hst hb.sp0 hFS (by have := hws p hp; omega) hq

/-- **The frame's words across a callee** changing its stack and an output apart from the
frame. -/
theorem FrameWords.call_out (hst : StackOk m0 N) (hb : Frame m0 F slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) {o : BitVec 64} {l : Nat} (hch : Changes d d' S' o l)
    (ho : ∀ q, NativeRustcVm.InRange o l q → ¬NativeRustcVm.InRange (stackBelow m0 F) (F + 8) q)
    {ws : List (Nat × UInt64)} (hws : ∀ p ∈ ws, p.1 + 8 ≤ F + 8) (h : FrameWords m0 F d.dmem ws) :
    FrameWords m0 F d'.dmem ws := by
  have hsp : rspOf d = stackBelow m0 F := by rw [hb.sp, off_zero]
  intro p hp
  refine bytesAt_congr (h p hp) fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  have hin : NativeRustcVm.InRange (stackBelow m0 F) (F + 8) (off (stackBelow m0 F) (p.1 + i)) :=
    inRange_off_self (by have := hws p hp; omega) (by have := hst.1; have := hst.2.1; omega)
  refine hch _ fun hq ↦ ?_
  rcases hq with hq | hq
  · exact ho _ hq hin
  · exact not_callee hst hsp hFS (by have := hws p hp; omega) hq

theorem writesIn_of_mid {o : Nat} {S : SState} (h : MidOk F o slots S = true) :
    writesIn S = true := by
  simp only [MidOk, Bool.and_eq_true] at h
  exact h.1.1.2

/-- **The frame's words across a block** writing elsewhere. -/
theorem FrameWords.block [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {S : SState} (hwf : (frameEnv m0 d F rest vars ret).WF)
    (hm : Match (frameEnv m0 d F rest vars ret) S d') (hin : writesIn S = true)
    {ws : List (Nat × UInt64)} (hws : ∀ p ∈ ws, p.1 + 8 ≤ F + 8)
    (hmiss : ∀ p ∈ ws, ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off)
    (h : FrameWords m0 F d.dmem ws) : FrameWords m0 F d'.dmem ws := by
  intro p hp
  refine bytesAt_congr (h p hp) fun i hi ↦ ?_
  have hi' : i < 8 := by simpa [LeanVM.Protocol.KeccakHash.wordBytes] using hi
  rw [off_add]
  rw [hm.get?_mem0 hwf (not_written0 hwf hm hin (by have := hws p hp; omega)
    fun w hw hr ↦ by rcases hmiss p hp w hw hr with h' | h' <;> omega)]
  rfl

/-- **An array of the frame**, `16 n` bytes at offset `o` above a callee's return address:
a slice a callee reads. -/
theorem local_sliceOk (hst : StackOk m0 N) (hb : Body m0 F N slots 0 d) {S' : Nat}
    (hFS : F + S' ≤ N) {o n : Nat} (h8 : 8 ≤ o) (hon : o + 16 * n ≤ F) :
    SliceOk d (off (stackBelow m0 F) o) (BitVec.ofNat 64 n) S' := by
  have hrsp := hst.1
  have htop := hst.2.1
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hbase : (stackBelow m0 F).toNat = (rspOf m0).toNat - F := stackBelow_toNat (by omega)
  have hoff : (off (stackBelow m0 F) o).toNat = (rspOf m0).toNat - F + o := by
    rw [toNat_off (by omega), hbase]
  unfold SliceOk Readable OffStack
  rw [hn]
  refine ⟨⟨mapped_off (Mapped.keeps (frame_mapped hst (by omega)) hb.fr.kept) (by omega), ?_⟩,
    ?_⟩
  · show NativeRustcVm.NoWrap _ _
    unfold NativeRustcVm.NoWrap; rw [hoff]; omega
  · show NativeRustcVm.Apart _ _ _ _
    rw [stackBelow_callee hb.sp0 (by omega)]
    unfold NativeRustcVm.Apart
    rw [hoff, stackBelow_toNat (by omega)]
    omega

/-- A slice holding `xs` reads `xs`. -/
theorem slice_of_ewsAt {m : MachineData} {a n : BitVec 64} {xs : List NativeVm.Model.EW}
    (h : NativeRustcVm.EWsAt m.dmem a xs) (hn : n.toNat = xs.length) : slice m a n = xs.toArray := by
  unfold slice
  rw [hn, NativeRustcVm.ewsOf_of_ewsAt h]

/-- Elements from their words, at offset `o` of `b`. -/
theorem ewsAt_words {d : DataMem} {b : BitVec 64} {o : Nat} {xs : List NativeVm.Model.EW}
    (h : ∀ i (hi : i < xs.length), NativeRustcVm.WordAt d (off b (o + 16 * i)) xs[i].c0 ∧
      NativeRustcVm.WordAt d (off b (o + 16 * i + 8)) xs[i].c1) :
    NativeRustcVm.EWsAt d (off b o) xs :=
  NativeRustcVm.Transcript.ewsAt_iff.mpr fun i hi ↦
    NativeRustcVm.Transcript.ewAt_iff.mpr
      ⟨by rw [off_off]; exact (h i hi).1, by rw [off_off, off_off]; exact (h i hi).2⟩

/-- **A word a block wrote**, its value given. -/
theorem wordAt_write_eq [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) (v : Sym)
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) {w : UInt64}
    (hv : v.eval env = w.toBitVec) : NativeRustcVm.WordAt m.dmem (off b o) w := by
  have e : UInt64.ofBitVec (v.eval env) = w := by rw [hv]
  rw [← e]
  exact wordAt_write hm hb hle hw

/-- **A word loaded** from the frame's words. -/
theorem load_frameWord [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {ws : List (Nat × UInt64)} (h : FrameWords m0 F d.dmem ws) {o : Nat}
    {w : UInt64} (hp : (o, w) ∈ ws) : (frameEnv m0 d F rest vars ret).load 0 o 8 = w.toBitVec :=
  load_ofMachine (m := d) (rs := (stackBelow m0 F, F + 8) :: rest) (vs := vars) (ret := ret)
    (r := 0) (n := F + 8) (o := o) (b := stackBelow m0 F) rfl (h (o, w) hp)

/-! ## The stack arguments -/

/-- The `k` argument words' address as a number. -/
theorem args_toNat {k : Nat} (hargs : ArgsOk m0 k) (hk : 0 < k) :
    (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
  have := hargs.2
  rw [BitVec.toNat_add, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]

/-- The `k` argument words do not wrap. -/
theorem args_noWrap {k : Nat} (hargs : ArgsOk m0 k) :
    NativeRustcVm.NoWrap (rspOf m0 + 8#64) (8 * k) := by
  unfold NativeRustcVm.NoWrap
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := (rspOf m0 + 8#64).isLt; omega
  · rw [args_toNat hargs hk]; exact hargs.2

/-- The `k` argument words are apart from the stack. -/
theorem args_apart (hst : StackOk m0 N) {k : Nat} (hargs : ArgsOk m0 k) (hk : 0 < k) :
    NativeRustcVm.Apart (rspOf m0 + 8#64) (8 * k) (stackBelow m0 N) (N + 8) := by
  unfold NativeRustcVm.Apart
  rw [args_toNat hargs hk, stackBelow_toNat hst.1]
  have := hst.1
  omega

/-- The environment of the frame and the `k` argument words. -/
theorem wf_args [Labels] (hst : StackOk m0 N) (hF : F ≤ N) (hk : Kept m0.dmem d.dmem) {k : Nat}
    (hargs : ArgsOk m0 k) (hk0 : 0 < k) {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d F [(rspOf m0 + 8#64, 8 * k)] vars ret).WF :=
  wf1 hst hF hk ⟨hargs.1, args_noWrap hargs⟩ (args_apart hst hargs hk0)

/-- **A stack argument loaded** from the arguments' region. -/
theorem load_arg [Labels] (hst : StackOk m0 N) {k : Nat} (hargs : ArgsOk m0 k)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (NativeRustcVm.InRange (stackBelow m0 N) N))
    {vars : Nat → BitVec 64} {ret : BitVec 64} {i : Nat} (hi : i < k) :
    (frameEnv m0 d F [(rspOf m0 + 8#64, 8 * k)] vars ret).load 1 (8 * i) 8 = stackArg m0 i := by
  rw [NativeRustcVmX64.Arrays.load8_eq]
  show (NativeRustcVm.wordOf d.dmem (rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i))).toBitVec = _
  rw [NativeRustcVm.wordOf_congr (d := m0.dmem) fun j hj ↦ ?_]
  · unfold stackArg
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm 8 (8 * i)]
  · rw [NativeRustcVm.addr_add_add]
    exact get_keep hst hs (args_apart hst hargs (by omega)) (args_noWrap hargs) (by omega)

/-- A frame offset above the return address, as the arguments' region's. -/
theorem alias_arg [Labels] {d : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64} {n : Nat} (i : Nat) :
    (Sym.ptr 0 ((F + 8 + 8 * i : Nat) : Int)).eval
        (frameEnv m0 d F ((rspOf m0 + 8#64, n) :: rest) vars ret) =
      (frameEnv m0 d F ((rspOf m0 + 8#64, n) :: rest) vars ret).base 1 +
        BitVec.ofInt 64 ((8 * i : Nat) : Int) := by
  show stackBelow m0 F + BitVec.ofInt 64 _ = (rspOf m0 + 8#64) + BitVec.ofInt 64 _
  rw [BitVec.ofInt_natCast, BitVec.ofInt_natCast, show F + 8 + 8 * i = F + (8 + 8 * i) by omega]
  rw [show stackBelow m0 F + BitVec.ofNat 64 (F + (8 + 8 * i)) =
    off (stackBelow m0 F) (F + (8 + 8 * i)) from rfl, frame_add, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-! ## Results -/

/-- A byte merged into a register: AL is the byte. -/
theorem merge8_toNat (x v : BitVec 64) :
    (BinOp.merge.apply .W8 x v).toNat % 256 = v.toNat % 256 := by
  show (((x.extractLsb' 8 (64 - 8)) ++ (v.setWidth 8)).setWidth 64).toNat % 256 = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_setWidth]
  have hv : v.toNat % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (by decide)
  rw [← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq,
    Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 2 ^ 64)]
  omega

/-- **`xor`, `xor`, `or`, `sete`**: AL is `1` iff two elements are equal. -/
theorem sete_ew (old a b c e : BitVec 64) :
    (BinOp.merge.apply .W8 old
      (if CmpOp.eq.apply .W64 (BinOp.or.apply .W64 (BinOp.xor.apply .W64 b e)
          (BinOp.xor.apply .W64 a c)) (BitVec.ofNat 64 0) = true then BitVec.ofNat 64 1
        else BitVec.ofNat 64 0)).toNat % 256 =
      (NativeRustcVmX64.okWord (ewArg a b == ewArg c e)).toNat := by
  rw [merge8_toNat]
  have hiff : ewArg a b = ewArg c e ↔ a = c ∧ b = e := by
    constructor
    · intro h
      exact ⟨congrArg (fun x : NativeVm.Model.EW ↦ x.c0.toBitVec) h,
        congrArg (fun x : NativeVm.Model.EW ↦ x.c1.toBitVec) h⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have key : CmpOp.eq.apply .W64 (BinOp.or.apply .W64 (BinOp.xor.apply .W64 b e)
      (BinOp.xor.apply .W64 a c)) (BitVec.ofNat 64 0) = (ewArg a b == ewArg c e) := by
    simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64]
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, hiff,
      show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff,
      BitVec.xor_eq_zero_iff, and_comm]
  rw [key]
  cases ewArg a b == ewArg c e <;> rfl

end

end NativeRustcVmX64.Bus
