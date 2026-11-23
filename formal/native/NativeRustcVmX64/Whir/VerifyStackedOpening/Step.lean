module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.Basic
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Got

/-!
# `verify_stacked_opening`: blocks and calls in its frame (x86-64)

`Ok.run`: a block run from a literal state in the frame's environment (region 0 the frame, then
`rest`), writing the frame only: `Ok` after it, the frame's bytes the block writes the only ones
changed. `Ok.mul`: `EW::mul` from a state at its call. The callees' stack, round constants and
read-only data (`Ok.stackOk`, `Ok.rcAt`, `Ok.rodataAt`); the round constants and the read-only data
are none of what may change (`Parts.rc_not_wr`, `Parts.ro_not_wr`).
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

theorem Parts.fnw : NativeRustcVm.NoWrap (stackBelow m0 512) (512 + 8) := by
  have : (stackBelow m0 512).toNat = (rspOf m0).toNat - 512 := h.fbn
  have := h.rsp
  unfold NativeRustcVm.NoWrap
  omega

/-- The frame in a state of the frame: mapped, not wrapping. -/
theorem Ok.frame_ok {st : MachineData} {o : Nat} (hok : Ok m0 st o) :
    NativeRustcVm.Mapped st.dmem (stackBelow m0 512) (512 + 8) ∧
      NativeRustcVm.NoWrap (stackBelow m0 512) (512 + 8) :=
  ⟨Mapped.keeps (frame_mapped h.wt.1 (by rw [stack_eq]; omega)) hok.fr.kept, h.fnw⟩

/-- The frame alone, as an environment. -/
theorem Ok.wf0 {st : MachineData} {o : Nat} (hok : Ok m0 st o) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 st 512 [] vars ret).WF :=
  frame_wf (hok.frame_ok h) (by simp) (List.pairwise_singleton _ _)

/-- An area apart from the stack, apart from the frame. -/
theorem Parts.apart_fr {x : BitVec 64} {n : Nat}
    (hx : NativeRustcVm.Apart x n (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8)) :
    NativeRustcVm.Apart (stackBelow m0 512) (512 + 8) x n :=
  Apart.symm' (apart_frame hx h.wt.1.1 (by rw [stack_eq]; omega))

/-- The frame and one more area, apart from the stack, as an environment. -/
theorem Ok.wf1 {st : MachineData} {o : Nat} (hok : Ok m0 st o) {x : BitVec 64} {n : Nat}
    (hm : NativeRustcVm.Mapped m0.dmem x n) (hnw : NativeRustcVm.NoWrap x n)
    (hx : NativeRustcVm.Apart x n (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8))
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 st 512 [(x, n)] vars ret).WF :=
  frame_wf (hok.frame_ok h) (by
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨Mapped.keeps hm hok.fr.kept, hnw⟩)
    (List.pairwise_pair.mpr (h.apart_fr hx))

/-- All allowed writes remain apart from the actual loader-slot bytes. -/
theorem Ok.got_bytes {st : MachineData} {o : Nat} (hok : Ok m0 st o) :
    ∀ l ∈ ["memcpy", "memset"], ∀ i < 8,
      st.dmem.get? (gotAddr l + BitVec.ofNat 64 i) =
        m0.dmem.get? (gotAddr l + BitVec.ofNat 64 i) := by
  have hg := h.got.areas
    (areas' := [(tA m0, tstateBytes), (scA m0, scalesBytes), (pA m0, whirBytes)])
    (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har; rcases har with rfl | rfl | rfl <;> simp)
  apply NativeRustcVmX64.GotAt.unchanged_vm hg h.wt.1
  · intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl
    · exact h.ts.footprint.1.2
    · exact h.so.1.2.1
    · exact h.po.1.2.1
  · intro q hq
    apply hok.so q
    rintro ((hp | hsc | ht) | hs)
    · exact hq (.inr ⟨(pA m0, whirBytes), by simp, hp⟩)
    · exact hq (.inr ⟨(scA m0, scalesBytes), by simp, hsc⟩)
    · exact hq (.inr ⟨(tA m0, tstateBytes), by simp, ht⟩)
    · exact hq (.inl hs)

/-- The copy's GOT region is read-only and disjoint from the symbolic stack frame. -/
theorem Ok.got_wf {st : MachineData} {o : Nat} (hok : Ok m0 st o)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 st 512 [(gotAddr "memcpy", 8)] vars ret).WF :=
  hok.wf1 h (h.got.mapped (by simp)) (h.got.1 "memcpy" (by simp)).2.1
    (h.got.1 "memcpy" (by simp)).2.2.1

/-- The copy reads a label only after matching its loader bytes. -/
theorem Ok.m_copy {st : MachineData} (hok : Ok m0 st 8)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    Match (frameEnv m0 st 512 [(gotAddr "memcpy", 8)] vars ret) copyS st := by
  have hm : Match (frameEnv m0 st 512 [(gotAddr "memcpy", 8)] vars ret)
      (init [520, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memcpy", 1, 0)]) st :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨(BitVec.add_zero _).symm, trivial⟩
  apply hm.withKnownBytes
  intro i hi
  simpa [Env.base, Sym.eval] using
    (hok.got_bytes h "memcpy" (by simp) i hi).trans (h.got.byte (by simp) hi)

/-- Transport the exact reached slots to a callee's contained stack and data areas. -/
theorem Ok.got_callee {st : MachineData} (hok : Ok m0 st 0) {N : Nat}
    {areas : List (BitVec 64 × Nat)} {symbols : List Label}
    (hN : 512 + N ≤ verifyStackedOpeningStack)
    (hlabels : symbols.Sublist ["memcpy", "memset"])
    (hcover : ∀ ar ∈ areas, ∃ b ∈
      (stackBelow m0 verifyStackedOpeningStack, verifyStackedOpeningStack + 8) ::
        ([(tA m0, tstateBytes), (a.words, 8 * a.len), (scA m0, scalesBytes), (pA m0, whirBytes)] ++
          (vsoInputs m0).map (fun r => (r.addr, r.size)) ++ rodataAreas),
      b.1.toNat ≤ ar.1.toNat ∧ ar.1.toNat + ar.2 ≤ b.1.toNat + b.2) :
    GotAt st N areas symbols := by
  have hsp : rspOf st = stackBelow m0 512 := by simpa [off] using hok.fr.sp
  have hd : (stackBelow st N).toNat = (rspOf m0).toNat - 512 - N := by
    rw [stackBelow_toNat (by rw [hsp, h.fbn]; have := h.rsp.1; rw [stack_eq] at hN; omega),
      hsp, h.fbn]
  apply NativeRustcVmX64.GotAt.callee (h.got.symbols hlabels)
    (fun l hl i hi => hok.got_bytes h l (hlabels.subset hl) i hi) _ _ hcover <;>
    rw [hd, h.sb] <;> have := h.rsp.1 <;> rw [stack_eq] at * <;> omega

/-- The frame and two more areas, apart from the stack and each other, as an environment. -/
theorem Ok.wf2 {st : MachineData} {o : Nat} (hok : Ok m0 st o) {x y : BitVec 64} {n l : Nat}
    (hm : NativeRustcVm.Mapped m0.dmem x n) (hnw : NativeRustcVm.NoWrap x n)
    (hx : NativeRustcVm.Apart x n (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8))
    (hm' : NativeRustcVm.Mapped m0.dmem y l) (hnw' : NativeRustcVm.NoWrap y l)
    (hy : NativeRustcVm.Apart y l (stackBelow m0 verifyStackedOpeningStack)
      (verifyStackedOpeningStack + 8))
    (hxy : NativeRustcVm.Apart x n y l)
    {vars : Nat → BitVec 64} {ret : BitVec 64} : (frameEnv m0 st 512 [(x, n), (y, l)] vars ret).WF :=
  frame_wf (hok.frame_ok h) (rest2_ok ⟨hm, hnw⟩ ⟨hm', hnw'⟩ hok.fr.kept)
    (pairwise3 (h.apart_fr hx) (h.apart_fr hy) hxy)

/-! ## Callees -/

/-- A callee's stack. -/
theorem Ok.stackOk {st : MachineData} (hok : Ok m0 st 0) {n' : Nat}
    (hn' : 512 + n' ≤ verifyStackedOpeningStack) : StackOk st n' :=
  stackOk_callee h.wt.1 hok.fr.kept (by rw [hok.fr.sp, off_zero]) hn'

omit [Labels] h in
theorem Ok.sp {st : MachineData} (hok : Ok m0 st 0) : rspOf st = stackBelow m0 512 := by
  rw [hok.fr.sp, off_zero]

/-- The round constants' bytes are none of what may change. -/
theorem Parts.rc_not_wr {q : BitVec 64} (hq : NativeRustcVm.InRange rcAddr 192 q) : ¬ Wr m0 q := by
  have hrc := h.wt.2.1
  rintro ((hq' | hq' | hq') | hq')
  · exact not_inRange_of_apart (Apart.symm' h.po.1.2.2.2.2.2) hrc.2.1 h.p_nat.1 hq hq'
  · exact not_inRange_of_apart (Apart.symm' h.so.1.2.2.2.2.2) hrc.2.1 h.sc_nat.1 hq hq'
  · exact not_inRange_of_apart (Apart.symm' h.wt.2.2.2.1.2.2) hrc.2.1 h.t_nat.1 hq hq'
  · exact not_inRange_of_apart hrc.2.2 hrc.2.1 (noWrap_stackBelow h.wt.1) hq
      (inRange_mono hq' (by omega))

/-- A read-only datum's bytes are none of what may change. -/
theorem Parts.ro_not_wr (t : NativeRustcVm.Data.Item) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (rodataAddr t) t.bytes.length q) : ¬ Wr m0 q := by
  have hro := h.wt.2.2.1
  have hnw := NativeRustcVm.RodataAt.noWrap hro t
  rintro ((hq' | hq' | hq') | hq')
  · exact not_inRange_of_apart (Apart.symm' (h.po.2 t)) hnw h.p_nat.1 hq hq'
  · exact not_inRange_of_apart (Apart.symm' (h.so.2 t)) hnw h.sc_nat.1 hq hq'
  · exact not_inRange_of_apart (Apart.symm' (h.wt.2.2.2.2 t)) hnw h.t_nat.1 hq hq'
  · exact not_inRange_of_apart (NativeRustcVm.RodataAt.apart hro t) hnw
      (noWrap_stackBelow h.wt.1) hq (inRange_mono hq' (by omega))

/-- The round constants for a callee. -/
theorem Ok.rcAt {st : MachineData} (hok : Ok m0 st 0) {n' : Nat}
    (hn' : 512 + n' ≤ verifyStackedOpeningStack) : RcAt st n' :=
  RcAt.callee h.wt.2.1 (fun i hi ↦ hok.so _ (h.rc_not_wr (inRange_off_self hi (by omega))))
    hok.sp h.wt.1.1 hn'

/-- The read-only data for a callee. -/
theorem Ok.rodataAt {st : MachineData} (hok : Ok m0 st 0) {n' : Nat}
    (hn' : 512 + n' ≤ verifyStackedOpeningStack) : RodataAt st n' := by
  have hro := h.wt.2.2.1
  unfold RodataAt NativeRustcVm.RodataAt
  intro t
  have hnw := NativeRustcVm.RodataAt.noWrap hro t
  refine ⟨(NativeRustcVm.RodataAt.bytesAt hro t).of_sameOutside hok.so fun i hi ↦
      h.ro_not_wr t (NativeRustcVm.inRange_add hi (by unfold NativeRustcVm.NoWrap at hnw; omega)),
    hnw, apart_callee (NativeRustcVm.RodataAt.apart hro t) hok.sp h.wt.1.1 hn'⟩

end

/-! ## Blocks -/

section
variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **`EW::mul`** from a state of the frame at its call: the product in RAX, RDX, the frame's
bytes unchanged. -/
theorem Parts.mul (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {env : Env} {st : MachineState} (hok : Ok m0 st.data 0) {next : Int64}
    (hpc : PcOk env (.call NativeRustcVmX64.Vm.EWMul.entryLabel) next st) {R : MachineState → Prop}
    (cont : ∀ st2 : MachineState, st2.pc = next → Ok m0 st2.data 8 →
      FrameSame m0 st.data.dmem st2.data.dmem →
      ewRet st2.data = EW.mul (ewArg (reg st.data .rdi) (reg st.data .rsi))
        (ewArg (reg st.data .rdx) (reg st.data .rcx)) →
      (∀ r, calleeSaved r = true → reg st2.data r = reg st.data r) →
      Keeps st.data.dmem st2.data.dmem →
      NativeRustcVm.SameOutside st.data.dmem st2.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
          verifyStackedOpeningStack) →
      Eventually (step1 Host.exe) R st2) :
    Eventually (step1 Host.exe) R st := by
  have hN : 512 + ewMulStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  refine call_then (P := EWMulPre) (Q := EWMulPost) hpc hmul (hok.stackOk h hN)
    fun st2 hpc2 hrsp2 ⟨hax, hdx, hso, hsv⟩ ↦ ?_
  obtain ⟨hok2, hfs⟩ := hok.call h hsv hrsp2 (N' := ewMulStack) (Rw := fun _ ↦ False)
    hN (fun _ h ↦ h.elim) (NativeRustcVm.SameOutside.mono hso fun _ hq ↦ .inr hq)
  refine cont st2 hpc2 hok2 hfs ?_ hsv.1 hsv.2
    (NativeRustcVm.SameOutside.mono hso fun _ hq ↦ (h.callee_stack (Ok.sp hok) hN hq).1)
  unfold ewRet ewArg
  rw [hax, hdx, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]

/-- **A block** from a state of the frame (RSP at offset `8`) at its address, run from the literal
state `S` in the frame's environment with `rest`, writing the frame only (below its return
address) and leaving RSP at offset `o`: `Ok` after it, the frame below its return address the
only bytes changed. -/
theorem Parts.run (h : Parts a s layout target coefficients point slices cs z value m0)
    {F : List Directive} (hp : Placed F k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt F j)
    (hne : b ≠ []) {st : MachineState} (hpc : st.pc = Host.addrOf (k + j))
    (hok : Ok m0 st.data 8) {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    (hwf : (frameEnv m0 st.data 512 rest vars
      (Host.addrOf (k + j + b.length)).toBitVec).WF)
    {S S' : SState} {x : Exit}
    (hm : Match (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec)
      S st.data)
    (hrun : exec b S = some (S', x)) {o : Nat} (hS : MidOk 512 o slots S' = true)
    (hw : ∀ w ∈ S'.mem, w.r = 0) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, Ok m0 st'.data o →
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 512) 512) →
      Match (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec) S'
        st'.data →
      PcOk (frameEnv m0 st.data 512 rest vars (Host.addrOf (k + j + b.length)).toBitVec) x
        (Host.addrOf (k + j + b.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at (infix_of hb hne hp) hrun hwf (fun _ _ ↦ rfl) hpc hm fun st' hm' hpc' ↦
    have hb' := hok.block h hwf hm' hS hw
    cont st' hb'.1 hb'.2 hm' hpc'

end

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
