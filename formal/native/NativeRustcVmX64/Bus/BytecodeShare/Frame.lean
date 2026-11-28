module

public import NativeRustcVmX64.Bus.BytecodeShare.Exec
public import NativeRustcVmX64.Bus.BytecodeShare.Model
public import NativeRustcVmX64.Sumcheck.Ctx
public import NativeRustcX64.Got
public import NativeRustcVmX64.Spec.Bus

/-!
# `bytecode_share`'s frame, its blocks and calls, its exits (x86-64)

`BF m0 O o d`: the frame (`Frame`, RSP at offset `o`), memory changed only in `O` and the stack,
RBX, RBP, R12 to R14 the entry's RDI, R8, R9, RCX, RDX. The outputs grow as the proof goes: the
`TState` (`OT`) until the copy, then the point (`OP`), then the output (`OA`). A body block keeps
it (`BF.block`), a call too where the callee's changes miss the frame's pushed registers
(`BF.call`). From it, `b16` returns (`exit16`); `b15` first writes the tag `0` (`none15`).
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Bus (busPointCap)

@[expose] public section

/-- The frame: 432 bytes below the entry's RSP. -/
abbrev fa (m0 : MachineData) : BitVec 64 := stackBelow m0 432

/-- The output (RDI), the `TState` (RSI), the weights (RDX), `bytecode_low` (RCX, R8), the point
(R9) at the entry. -/
abbrev oAt (m0 : MachineData) : BitVec 64 := reg m0 .rdi
abbrev tAt (m0 : MachineData) : BitVec 64 := reg m0 .rsi
abbrev wAt (m0 : MachineData) : BitVec 64 := reg m0 .rdx
abbrev bAt (m0 : MachineData) : BitVec 64 := reg m0 .rcx
abbrev nB (m0 : MachineData) : Nat := (reg m0 .r8).toNat
abbrev pAt (m0 : MachineData) : BitVec 64 := reg m0 .r9

/-- The point's bytes. -/
abbrev ptBytes : Nat := 16 * sharePointSlots

theorem ptBytes_eq : ptBytes = 1072 := rfl

/-- The stack. -/
abbrev Stk (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 bytecodeShareStack) bytecodeShareStack q

/-- The outputs before the copy: the `TState`. -/
def OT (m0 : MachineData) (q : BitVec 64) : Prop := NativeRustcVm.InRange (tAt m0) tstateBytes q

/-- The outputs during the copy: the `TState` and the point. -/
def OP (m0 : MachineData) (q : BitVec 64) : Prop :=
  OT m0 q ∨ NativeRustcVm.InRange (pAt m0) ptBytes q

/-- All the outputs. -/
def OA (m0 : MachineData) (q : BitVec 64) : Prop := NativeRustcVm.InRange (oAt m0) 48 q ∨ OP m0 q

/-- **The frame**, RSP at offset `o`, the outputs `O`. -/
structure BF (m0 : MachineData) (O : BitVec 64 → Prop) (o : Nat) (d : MachineData) : Prop where
  frame : Frame m0 432 slots o d
  same : NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦ O q ∨ Stk m0 q)
  rbx : reg d .rbx = oAt m0
  rbp : reg d .rbp = reg m0 .r8
  r12 : reg d .r12 = pAt m0
  r13 : reg d .r13 = bAt m0
  r14 : reg d .r14 = wAt m0

/-- A byte not among the frame's pushed registers and return address (offsets `384` to `440`). -/
def NotHigh (m0 : MachineData) (q : BitVec 64) : Prop :=
  ∀ j, 384 ≤ j → j < 440 → q ≠ off (fa m0) j

/-- A body block's environment: the frame. -/
abbrev envB (m0 d : MachineData) (ret : BitVec 64) : Env := frameEnv m0 d 432 [] (fun _ ↦ 0) ret

/-- The weights as the model reads them. -/
abbrev wts (m0 : MachineData) : Array EW := (NativeRustcVm.ewsOf m0.dmem (wAt m0) 16).toArray

/-- The model's result. -/
abbrev res (s0 : TState) (m0 : MachineData) : Option ((EW × Array EW × EW) × TState) :=
  (bytecodeShare (wts m0) (slice m0 (bAt m0) (reg m0 .r8))).run s0

/-- What `bytecode_share` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s0 : TState) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ BytecodeSharePost a s0 m0 st.data

end

public section

theorem N_ge : 432 ≤ bytecodeShareStack := by decide
theorem le_rs : 432 + readScalarStack ≤ bytecodeShareStack := by decide
theorem le_sc : 432 + sumcheckPlainStack ≤ bytecodeShareStack := by decide
theorem le_ek : 432 + eqKernelStack ≤ bytecodeShareStack := by decide
theorem le_dot : 432 + dotStack ≤ bytecodeShareStack := by decide
theorem le_mul : 432 + ewMulStack ≤ bytecodeShareStack := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 432 := by decide
theorem slots_range : ∀ p ∈ slots, 384 ≤ p.1 ∧ p.1 + 8 ≤ 432 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

theorem OT_OP {m0 : MachineData} : ∀ q, OT m0 q → OP m0 q := fun _ h ↦ .inl h
theorem OP_OA {m0 : MachineData} : ∀ q, OP m0 q → OA m0 q := fun _ h ↦ .inr h
theorem OT_OA {m0 : MachineData} : ∀ q, OT m0 q → OA m0 q := fun _ h ↦ .inr (.inl h)

theorem KeepsB.reg {S : SState} {rs : List Reg64} (h : KeepsB S rs = true) {r : Reg64}
    (hr : r ∈ rs) : S.reg r = some (.reg r) := by
  simp only [KeepsB, List.all_eq_true, beq_iff_eq] at h
  exact h r hr

theorem KeepsB.mono {S : SState} {rs rs' : List Reg64} (h : KeepsB S rs = true)
    (hsub : ∀ r ∈ rs', r ∈ rs) : KeepsB S rs' = true := by
  simp only [KeepsB, List.all_eq_true, beq_iff_eq] at h ⊢
  exact fun r hr ↦ h r (hsub r hr)

theorem BF.mono {m0 d : MachineData} {O O' : BitVec 64 → Prop} {o : Nat} (hf : BF m0 O o d)
    (hO : ∀ q, O q → O' q) : BF m0 O' o d :=
  ⟨hf.frame, NativeRustcVm.SameOutside.mono hf.same fun q hq ↦ hq.imp_left (hO q), hf.rbx, hf.rbp,
    hf.r12, hf.r13, hf.r14⟩

/-- A write list in region 0 below offset `lo` (but the callee's return address) or from `hi`
misses the bytes `o` to `o + l` (`8 ≤ o`, `o + l ≤ lo` or `hi ≤ o`). -/
theorem miss_of_writesF {S : SState} {lo hi : Nat} (h : WritesF S lo hi) {o l : Nat}
    (h8 : 8 ≤ o) (hlh : o + l ≤ lo ∨ hi ≤ o) :
    ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ o ∨ o + l ≤ w.off := fun w hw _ ↦ by
  rcases (h w hw).2 with h1 | ⟨h1, h2⟩ <;> omega

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- The precondition's parts. -/
theorem pre_parts (h : BytecodeSharePre a s0 m0) :
    StackOk m0 bytecodeShareStack ∧ RcAt m0 bytecodeShareStack ∧ TStateAt m0.dmem (tAt m0) a s0 ∧
      TStateOk m0 (tAt m0) a bytecodeShareStack ∧ EWsOk m0 (wAt m0) 16 bytecodeShareStack ∧
      nB m0 ≤ busPointCap ∧ SliceOk m0 (bAt m0) (reg m0 .r8) bytecodeShareStack ∧
      OutOk m0 (tAt m0) a (oAt m0) 48 bytecodeShareStack ∧
      OutOk m0 (tAt m0) a (pAt m0) ptBytes bytecodeShareStack ∧
      Apart (oAt m0) 48 (pAt m0) ptBytes ∧ Apart (pAt m0) ptBytes (bAt m0) (16 * nB m0) ∧
      Apart (wAt m0) (16 * 16) (tAt m0) tstateBytes ∧
      Apart (bAt m0) (16 * nB m0) (tAt m0) tstateBytes := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, _⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The context of `bytecode_share`. -/
theorem ctx_of (h : BytecodeSharePre a s0 m0) : Ctx m0 (tAt m0) a bytecodeShareStack 432 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.1.footprint, N_ge⟩

theorem oOk (h : BytecodeSharePre a s0 m0) :
    OutOk m0 (tAt m0) a (oAt m0) 48 bytecodeShareStack := (pre_parts h).2.2.2.2.2.2.2.1

theorem pOk (h : BytecodeSharePre a s0 m0) :
    OutOk m0 (tAt m0) a (pAt m0) ptBytes bytecodeShareStack := (pre_parts h).2.2.2.2.2.2.2.2.1

theorem pre_got (h : BytecodeSharePre a s0 m0) :
    GotAt m0 bytecodeShareStack [(tAt m0, tstateBytes), (a.words, 8 * a.len),
      (oAt m0, 48), (pAt m0, ptBytes), (wAt m0, 16 * 16), (bAt m0, 16 * nB m0),
      (rcAddr, 192)] ["memcpy"] := h.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Preserve the loader slots across the complete output/stack frame. -/
theorem BF.got_same (h : BytecodeSharePre a s0 m0)
    {O : BitVec 64 → Prop} {o : Nat} {d : MachineData} (hf : BF m0 O o d)
    (hO : ∀ q, O q → OA m0 q) :
    ∀ l ∈ ["memcpy"], ∀ i < 8, d.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
      m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  refine got_keep (pre_got h) h.1
    (writes := [(oAt m0, 48), (tAt m0, tstateBytes), (pAt m0, ptBytes)])
    (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl | rfl <;> simp)
    (by
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (oOk h).2.1
      · exact (ctx_of h).fp.1.2
      · exact (pOk h).2.1)
    (NativeRustcVm.SameOutside.mono hf.same ?_)
  intro q hq
  rcases hq with hq | hq
  · rcases hO q hq with hq | hq | hq
    · exact .inl ⟨(oAt m0, 48), by simp, hq⟩
    · exact .inl ⟨(tAt m0, tstateBytes), by simp, hq⟩
    · exact .inl ⟨(pAt m0, ptBytes), by simp, hq⟩
  · exact .inr hq

theorem BF.got_callee (h : BytecodeSharePre a s0 m0)
    {O : BitVec 64 → Prop} {d : MachineData} (hf : BF m0 O 0 d)
    (hO : ∀ q, O q → OA m0 q) {n : Nat} (hn : 432 + n ≤ bytecodeShareStack)
    {areas : List (BitVec 64 × Nat)}
    (ha : ∀ l ∈ ["memcpy"], ∀ b ∈ areas, Apart (gotAddr l) 8 b.1 b.2) :
    GotAt d n areas ["memcpy"] :=
  NativeRustcVmX64.Transcript.got_callee (pre_got h) (hf.got_same h hO)
    (by rw [hf.frame.sp, off_zero]) h.1.1 hn ha

/-- The outputs and the stack are apart from the round constants. -/
theorem not_rc (h : BytecodeSharePre a s0 m0) {q : BitVec 64} (hq : OA m0 q ∨ Stk m0 q) :
    ¬ NativeRustcVm.InRange rcAddr 192 q := by
  have c := ctx_of h
  rcases hq with (hq | hq | hq) | hq
  · exact c.out_not_rc (oOk h) hq
  · exact c.not_rc_tstate hq
  · exact c.out_not_rc (pOk h) hq
  · exact c.not_rc_stack hq

/-- The outputs are apart from the frame's region. -/
theorem not_frame (h : BytecodeSharePre a s0 m0) {q : BitVec 64} (hq : OA m0 q) :
    ¬ NativeRustcVm.InRange (fa m0) 440 q := by
  have c := ctx_of h
  rcases hq with hq | hq | hq
  · exact not_inRange_of_apart (apart_frame (oOk h).2.2.2.2.1 c.spN N_ge) (oOk h).2.1
      c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame c.tok.1 c.spN N_ge) c.fp.1.2 c.noWrap_frame hq
  · exact not_inRange_of_apart (apart_frame (pOk h).2.2.2.2.1 c.spN N_ge) (pOk h).2.1
      c.noWrap_frame hq

/-- Outside the frame's region: not its high bytes. -/
theorem notHigh_of_not_frame (h : BytecodeSharePre a s0 m0) {q : BitVec 64}
    (hq : ¬ NativeRustcVm.InRange (fa m0) 440 q) : NotHigh m0 q := by
  rintro j - hj rfl
  exact hq (inRange_off_self hj (by
    have := (ctx_of h).noWrap_frame; unfold NativeRustcVm.NoWrap at this; omega))

/-- A local of the frame below its pushed registers: not its high bytes. -/
theorem notHigh_local (h : BytecodeSharePre a s0 m0) {o n : Nat} (hon : o + n ≤ 384)
    {q : BitVec 64} (hq : NativeRustcVm.InRange (off (fa m0) o) n q) : NotHigh m0 q := by
  have hnw := (ctx_of h).noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  rintro j hj1 hj2 rfl
  rw [inRange_off_iff (by omega) (by omega)] at hq
  omega

/-- A local of the frame is in the stack. -/
theorem stk_local (h : BytecodeSharePre a s0 m0) {o n : Nat} (hon : o + n ≤ 432) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (off (fa m0) o) n q) : Stk m0 q :=
  (ctx_of h).inRange_frame (inRange_of_off ((ctx_of h).noWrap_frame.mono (by omega)) hon hq)

/-- Two locals of the frame, one before the other, are apart. -/
theorem not_local (h : BytecodeSharePre a s0 m0) {o n j : Nat} (hj : j < o ∨ o + n ≤ j)
    (hon : o + n ≤ 440) (hj' : j < 440) :
    ¬ NativeRustcVm.InRange (off (fa m0) o) n (off (fa m0) j) := by
  have hnw := (ctx_of h).noWrap_frame
  unfold NativeRustcVm.NoWrap at hnw
  rw [inRange_off_iff (by omega) (by omega)]
  omega

/-- The `TState` is apart from the frame's locals. -/
theorem not_local_t (h : BytecodeSharePre a s0 m0) {o n : Nat} (hon : o + n ≤ 440) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (tAt m0) tstateBytes q) :
    ¬ NativeRustcVm.InRange (off (fa m0) o) n q := fun h' ↦
  not_frame h (OT_OA q hq) (inRange_of_off (ctx_of h).noWrap_frame hon h')

/-- The round constants' bytes under `BF`. -/
theorem BF.rc (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop} {o : Nat} {d : MachineData}
    (hf : BF m0 O o d) (hO : ∀ q, O q → OA m0 q) :
    ∀ i < 192, d.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
      m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) :=
  rc_keep hf.same fun _ hq ↦ not_rc h (hq.imp_left (hO _))

/-- At a call. -/
theorem BF.at (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop} {d : MachineData}
    (hf : BF m0 O 0 d) (hO : ∀ q, O q → OA m0 q) : At m0 432 d :=
  At.of_frame hf.frame (hf.rc h hO)

theorem wf_envB (h : BytecodeSharePre a s0 m0) {d : MachineData} (hk : Kept m0.dmem d.dmem)
    (ret : BitVec 64) : (envB m0 d ret).WF := by
  have c := ctx_of h
  exact frame_wf ⟨c.mapped_frame hk, c.noWrap_frame⟩ (by simp) (List.pairwise_singleton _ _)

theorem match_bodyS {O : BitVec 64 → Prop} {d : MachineData} (hf : BF m0 O 8 d)
    (ret : BitVec 64) : Match (envB m0 d ret) bodyS d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨hf.frame.rsp_eval, trivial⟩ trivial trivial trivial

omit [Labels] in
/-- A body block's writes, below the pushed registers' end. -/
theorem written_fr {d : MachineData} {ret : BitVec 64} {S : SState} (hbr : belowRet 432 S = true)
    (hfnw : NativeRustcVm.NoWrap (fa m0) 440) {q : BitVec 64}
    (hw : Written (envB m0 d ret) S q) : NativeRustcVm.InRange (fa m0) 432 q := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
  match hr : w.r, hb with
  | 0, hb =>
    cases hb
    have := belowRet_spec hbr w hw hr
    rw [inRange_iff' (hfnw.mono (by omega))]
    have e : (fa m0).toNat = (stackBelow m0 432).toNat := rfl
    omega
  | r + 1, hb => simp at hb

/-- **A body block** keeps the frame; it writes only the frame below its pushed registers. -/
theorem BF.block (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop} {d d' : MachineData}
    {ret : BitVec 64} {S : SState} (hf : BF m0 O 8 d) (hm : Match (envB m0 d ret) S d') {o : Nat}
    (hmid : MidOk 432 o slots S = true) (hk : KeepsB S [.rbx, .rbp, .r12, .r13, .r14] = true) :
    BF m0 O o d' ∧
      NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) 432) := by
  have c := ctx_of h
  have hwf := wf_envB h hf.frame.kept ret
  have hs : NativeRustcVm.SameOutside d.dmem d'.dmem (NativeRustcVm.InRange (fa m0) 432) :=
    fun q hq ↦ hm.get?_mem0 hwf fun hw ↦ hq (written_fr (belowRet_of_mid hmid) c.noWrap_frame hw)
  refine ⟨⟨Frame.of_block hf.frame hwf hm hmid slots_le,
    NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ ?_,
    (hm.regs .rbx _ (KeepsB.reg hk (by simp))).trans hf.rbx,
    (hm.regs .rbp _ (KeepsB.reg hk (by simp))).trans hf.rbp,
    (hm.regs .r12 _ (KeepsB.reg hk (by simp))).trans hf.r12,
    (hm.regs .r13 _ (KeepsB.reg hk (by simp))).trans hf.r13,
    (hm.regs .r14 _ (KeepsB.reg hk (by simp))).trans hf.r14⟩, hs⟩
  rcases hq with hq | hq
  · exact hq
  · exact .inr (c.inRange_frame hq)

/-- **A call** keeps the frame where the callee's changes miss its high bytes. -/
theorem BF.call (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop} {d d' : MachineData}
    (hf : BF m0 O 0 d) (hO : ∀ q, O q → OA m0 q) {Nc : Nat}
    (hle : 432 + Nc ≤ bytecodeShareStack) (hsv : Saved d d') (hrsp : rspOf d' = rspOf d + 8#64)
    {R : BitVec 64 → Prop} (hR : ∀ q, R q → (O q ∨ Stk m0 q) ∧ NotHigh m0 q)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q)) : BF m0 O 8 d' := by
  have c := ctx_of h
  have hat := hf.at h hO
  have hall : ∀ q, (R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q) →
      (O q ∨ Stk m0 q) ∧ NotHigh m0 q := fun q hq ↦ hq.elim (hR q) fun hq ↦ by
    obtain ⟨h1, h2⟩ := c.inRange_callee hat hle hq
    exact ⟨.inr h1, notHigh_of_not_frame h h2⟩
  refine ⟨Frame.call_slots hf.frame hsv hrsp hso (fun p hp i hi hq ↦ ?_)
      (fun j hj hq ↦ (hall _ hq).2 (432 + j) (by omega) (by omega) rfl),
    NativeRustcVm.SameOutside.mono (hf.same.trans hso) fun q hq ↦ hq.elim id fun hq ↦ (hall q hq).1,
    (hsv.1 .rbx rfl).trans hf.rbx, (hsv.1 .rbp rfl).trans hf.rbp, (hsv.1 .r12 rfl).trans hf.r12,
    (hsv.1 .r13 rfl).trans hf.r13, (hsv.1 .r14 rfl).trans hf.r14⟩
  have hp' := slots_range p hp
  exact (hall _ hq).2 (p.1 + i) (by omega) (by omega) rfl

/-- **Frame bytes from `o ≥ 8` kept by a call** whose changes `R` miss them. -/
theorem keep_call (h : BytecodeSharePre a s0 m0) {d d' : MachineData} (hat : At m0 432 d)
    {Nc : Nat} (hle : 432 + Nc ≤ bytecodeShareStack) {R : BitVec 64 → Prop}
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ R q ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {bs : List UInt8} (ho : 8 ≤ o) (hon : o + bs.length ≤ 432)
    (hR : ∀ i < bs.length, ¬ R (off (fa m0) (o + i)))
    (hb : NativeRustcVm.BytesAt d.dmem (off (fa m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fa m0) o) bs := by
  have c := ctx_of h
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  refine NativeRustcVm.BytesAt.of_sameOutside hb hso fun i hi hq ↦ ?_
  rw [off_add] at hq
  rcases hq with hq | hq
  · exact hR i hi hq
  · have hA := c.apart_frame_callee hat hle (o := o) (n := bs.length) ho hon
    have hin : NativeRustcVm.InRange (off (fa m0) o) bs.length (off (fa m0) (o + i)) := by
      rw [← off_add]; exact inRange_off_self hi (by omega)
    exact not_inRange_of_apart hA (by unfold NativeRustcVm.NoWrap; rw [toNat_off (by omega)]; omega)
      (noWrap_stackBelow (c.stackOk hat hle)) hin (inRange_mono hq (by omega))

/-- **The `TState` kept** where the memory changed only in the point, the output and the stack. -/
theorem tstate_keep (h : BytecodeSharePre a s0 m0) {d d' : Mem 64} {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d d' R) (hk : Kept d d')
    (hR : ∀ q, R q → NativeRustcVm.InRange (pAt m0) ptBytes q ∨
      NativeRustcVm.InRange (oAt m0) 48 q ∨ Stk m0 q)
    {s' : TState} (ht : TStateAt d (tAt m0) a s') : TStateAt d' (tAt m0) a s' := by
  have c := ctx_of h
  refine ht.frame hk (fun q hq ↦ ?_) hs
  rcases hR q hq with hq | hq | hq
  · exact c.out_not_t (pOk h) hq
  · exact c.out_not_t (oOk h) hq
  · exact c.stack_not_t hq

end

variable [Host] {a : DecArea} {s0 : TState} {m0 : MachineData} {k : Nat}

/-- **The epilogue** `NativeRustcVmX64.Vm.BytecodeShare.label_15` (`b16`): the result as the memory has it. -/
theorem exit16 (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {d : MachineData}
    (hf : BF m0 (OA m0) 8 d)
    (hout : OptShareAt d.dmem (oAt m0) ((res s0 m0).map (·.1)))
    (hpt : ∀ x s', res s0 m0 = some (x, s') →
      NativeRustcVm.EWsAt d.dmem (pAt m0) x.2.1.toList ∧ TStateAt d.dmem (tAt m0) a s') :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b16Offset)⟩ := by
  have c := ctx_of h
  have hwf := wf_envB h hf.frame.kept 0
  refine exec_then (infix_of b16_in_code (by simp [b16]) hp) exit_b16 hwf nofun
    (match_bodyS hf 0) fun st hm' hpc ↦ ?_
  obtain ⟨hepi, hmem⟩ := ok_b16
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hf.frame hwf hm' hepi
  have hd : st.data.dmem = d.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk, Sym.eval] at hpc
  refine .done _ ⟨hpc.trans (hf.frame.load_ret c.stack N_ge), hrsp, ?_, fun x s' hx ↦ ?_, ?_, hsv⟩
  · rw [hd]; exact hout
  · rw [hd]; exact hpt x s' hx
  · intro q hq
    rw [hd]
    refine hf.same q fun h' ↦ hq ?_
    rcases h' with (h' | h' | h') | h'
    · exact .inl h'
    · exact .inr (.inr (.inl h'))
    · exact .inr (.inl h')
    · exact .inr (.inr (.inr h'))

/-- **The tag `0`** (`NativeRustcVmX64.Vm.BytecodeShare.label_14`, `b15`): the model failed. -/
theorem none15 (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {O : BitVec 64 → Prop}
    {d : MachineData} (hf : BF m0 O 8 d) (hO : ∀ q, O q → OA m0 q) (hr : res s0 m0 = none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b15Offset)⟩ := by
  have c := ctx_of h
  have ho := oOk h
  let env := frameEnv m0 d 432 [(oAt m0, 48)] (fun _ ↦ 0) 0
  have hwf : env.WF :=
    frame_wf ⟨c.mapped_frame hf.frame.kept, c.noWrap_frame⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨Mapped.keeps ho.1 hf.frame.kept, ho.2.1⟩)
      (List.pairwise_pair.mpr (Apart.symm' (apart_frame ho.2.2.2.2.1 c.spN N_ge)))
  have hm : Match env outS d :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.frame.rsp_eval, known_ptr rfl hf.rbx, trivial⟩
      trivial trivial trivial
  refine exec_then (infix_of b15_in_code (by simp [b15]) hp) exit_b15 hwf nofun hm
    fun st hm' hpc ↦ ?_
  obtain ⟨hmid, hk, hrbx, hW0, hws⟩ := ok_b15
  have hs : NativeRustcVm.SameOutside d.dmem st.data.dmem (fun q ↦
      NativeRustcVm.InRange (fa m0) 432 q ∨ NativeRustcVm.InRange (oAt m0) 48 q) :=
    fun q hq ↦ hm'.get?_mem0 hwf fun hw ↦ hq (written_frame2 hm' (writesIn_of_mid hmid)
      (belowRet_of_mid hmid) ho.2.1 c.noWrap_frame hw)
  have hf' : BF m0 (OA m0) 8 st.data :=
    ⟨Frame.of_block hf.frame hwf hm' hmid slots_le,
      NativeRustcVm.SameOutside.mono (hf.same.trans hs) fun q hq ↦ by
        rcases hq with (hq | hq) | hq | hq
        · exact .inl (hO q hq)
        · exact .inr hq
        · exact .inr (c.inRange_frame hq)
        · exact .inl (.inl hq),
      (hm'.regs .rbx _ hrbx).trans (eval_ptr rfl),
      (hm'.regs .rbp _ (KeepsB.reg hk (by simp))).trans hf.rbp,
      (hm'.regs .r12 _ (KeepsB.reg hk (by simp))).trans hf.r12,
      (hm'.regs .r13 _ (KeepsB.reg hk (by simp))).trans hf.r13,
      (hm'.regs .r14 _ (KeepsB.reg hk (by simp))).trans hf.r14⟩
  have hw0 : NativeRustcVm.WordAt st.data.dmem (off (oAt m0) 0) 0 :=
    wordAt_written hm' (r := 1) rfl (by omega) hW0 rfl
  rw [off_zero] at hw0
  simp only [PcOk] at hpc
  obtain ⟨d', pc⟩ := st
  simp only at hpc
  subst hpc
  refine exit16 hp h hf' (by rw [hr]; exact hw0) fun x s' hx ↦ ?_
  rw [hr] at hx
  cases hx

end

end NativeRustcVmX64.Bus.BytecodeShare
