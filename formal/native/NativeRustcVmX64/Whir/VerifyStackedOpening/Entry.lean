module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.CountLoop
public import NativeRustcVmX64.Whir.VerifyStackedOpening.Words

/-!
# `verify_stacked_opening`: the prologue (x86-64)

`entry_b0`: `b0` pushes the callee-saved registers, keeps the arguments (`CB`; the ring switch's
output at the frame's offset `64`) and reads the claims' count: none, `NativeRustcVmX64.Vm.VerifyStackedOpening.label_3`
(`b3`). Else `b1`: one claim, `b2` to `NativeRustcVmX64.Vm.VerifyStackedOpening.label_12` (`b16`, the last claim with
none counted, `AtB15`); more, `b5` to the counting loop's head (`Head 0`) (`entry_step`).
`Parts.cbRun`: a block of registers only keeping `CB`'s.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **A block of registers only** from a state of `CB`, keeping `CB`'s registers. -/
theorem Parts.cbRun (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) {st : MachineState} (hpc : st.pc = Host.addrOf (k + j))
    (hc : CB a s cs m0 st.data) {S' : SState} {x : Exit} (hrun : exec b regS = some (S', x))
    (hS : MidOk 512 8 slots S' = true) (hmem : S'.mem = []) (hk : keeps cbRegs S' = true)
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, CB a s cs m0 st'.data → st'.data.dmem = st.data.dmem →
      Match (frameEnv m0 st.data 512 [] (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec) S'
        st'.data →
      PcOk (frameEnv m0 st.data 512 [] (fun _ ↦ 0) (Host.addrOf (k + j + b.length)).toBitVec) x
        (Host.addrOf (k + j + b.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  h.run hp hb hne hpc hc.ok (hc.ok.wf0 h) hc.ok.m_reg hrun hS
    (fun w hw ↦ by rw [hmem] at hw; cases hw) fun st' hok' _ hm' hpc' ↦
    have hd := hm'.dmem_eq (hc.ok.wf0 h) hmem
    cont st' (hc.keep hok' hd fun r hr ↦ kept_reg hm' hk hr) hd hm' hpc'

/-- **The prologue**: no claim (`b3`), one claim (`b1`), more (`b1`). -/
theorem entry_b0 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) {R : MachineState → Prop}
    (cont0 : ∀ st, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b3Offset) → CB a s cs m0 st.data → cs.size = 0 →
      Eventually (step1 Host.exe) R st)
    (cont1 : ∀ st, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b1Offset) → CB a s cs m0 st.data → 0 < cs.size →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b0Offset)⟩ := by
  have hn := h.n_le
  have hcin := (h.ins _ mem_cl).1
  have hcb : NativeRustcVm.Layout.claimsBytes = 97288 := rfl
  simp only [hcb] at hcin
  have hwf0 : (frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0).WF :=
    frame_wf ⟨frame_mapped h.wt.1 (by rw [stack_eq]; omega), h.fnw⟩
      (by
        intro y hy
        rw [List.mem_singleton] at hy
        subst hy
        exact ⟨fun i hi ↦ hcin.1.1 i (by omega), by
          have : (clA m0).toNat + 97288 ≤ 2 ^ 64 := hcin.1.2
          show (clA m0).toNat + 8 ≤ 2 ^ 64; omega⟩)
      (List.pairwise_pair.mpr (h.apart_fr (x := clA m0) (n := 8) (by
        have : NativeRustcVm.Apart (clA m0) 97288 (stackBelow m0 verifyStackedOpeningStack)
          (verifyStackedOpeningStack + 8) := hcin.2
        unfold NativeRustcVm.Apart at this ⊢
        omega)))
  have hm0 : Match (frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial
      ⟨by show reg m0 .r9 = _
          rw [Env.base_ofMachine _ _ _ _ (r := 1) rfl, show BitVec.ofInt 64 0 = 0#64 from rfl,
            BitVec.add_zero], trivial⟩
  refine exec_then (infix_of b0_in_code (List.cons_ne_nil _ _) hp) run_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ ?_
  have hfr : Frame m0 512 slots 8 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 (by decide +kernel) slots_le slots_cs
  have hlow := sameOutside_low hwf0 hm1 (r := 0) rfl (hi := 512) (by omega) (by decide +kernel)
  have hok : Ok m0 st1.data 8 :=
    ⟨hfr, fun q hq ↦ hlow q fun h' ↦ hq (.inr (h.frame_stack h'))⟩
  have hload : (frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0).load 1 0 8 =
      cs.size.toUInt64.toBitVec :=
    load_ofMachine (r := 1) rfl (by rw [off_zero]; exact h.cl.len)
  have hcnt : ((Sym.load 1 0 8).eval (frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0)).toNat =
      cs.size := by
    show ((frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0).load 1 0 8).toNat = _
    rw [hload]; exact u64n (by omega)
  have hlt : ((Sym.load 1 0 8).eval (frameEnv m0 m0 512 [(clA m0, 8)] (fun _ ↦ 0) 0)).toNat <
      161 := by rw [hcnt]; omega
  have hcb1 : CB a s cs m0 st1.data := by
    refine ⟨hok, h.ts.frame (hm1.kept hwf0) (fun q hq ↦ h.frame_not_t (inRange_mono hq (by omega)))
      hlow, hm1.regs .rbp _ rfl, hm1.regs .r12 _ rfl, ?_, hm1.regs .r14 _ rfl, ?_,
      hm1.regs .rdi _ rfl, hm1.regs .r8 _ rfl,
      fw_write hm1 (o := 64) (by omega) (v := .reg .rcx) (by decide +kernel)⟩
    · rw [show reg st1.data .r13 = _ from hm1.regs .r13 _ rfl, eval_ite_ult _ _ _ hlt (by decide)]
      rfl
    · rw [show reg st1.data .r15 = _ from hm1.regs .r15 _ rfl, eval_ite_ult _ _ _ hlt (by decide)]
      exact hcnt
  simp only [PcOk] at hpc1
  rw [eval_test0, eval_ite_ult _ _ _ hlt (by decide), hcnt] at hpc1
  by_cases hz : cs.size = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_3_at] at hpc1
    exact cont0 st1 hpc1 hcb1 hz
  · simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    exact cont1 st1 (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b0_next)) hcb1
      (Nat.pos_of_ne_zero hz)

/-- **After the prologue**, with claims: one (`b2`, to `b16` with `AtB15`), more (`b5`, to the
loop's head `Head 0`). -/
theorem entry_step (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b1Offset))
    (hc : CB a s cs m0 st.data) (hpos : 0 < cs.size)
    {R : MachineState → Prop}
    (contT : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b16Offset) → AtB15 a s layout cs m0 st'.data →
      cs.size % 2 = 1 → Eventually (step1 Host.exe) R st')
    (contH : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b9Offset) → Head a s layout cs m0 0 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hn := h.n_le
  refine h.cbRun hp b1_in_code (List.cons_ne_nil _ _) hpc hc run_b1 (by decide +kernel) rfl
    (by decide +kernel) fun st1 hc1 _ hm1 hpc1 ↦ ?_
  have hrax : reg st1.data .rax = off (layA m0) 120 := by
    rw [show reg st1.data .rax = _ from hm1.regs .rax _ rfl, eval_add64]
    show reg st.data .rbp + _ = _
    rw [hc.rbp]; rfl
  simp only [PcOk] at hpc1
  rw [eval_ne_lit _ (by decide)] at hpc1
  have h15 : ((Sym.reg .r15).eval (frameEnv m0 st.data 512 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b1Offset + b1.length)).toBitVec)).toNat = cs.size := hc.r15
  rw [h15] at hpc1
  by_cases h1 : cs.size = 1
  · simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    refine h.cbRun hp b2_in_code (List.cons_ne_nil _ _)
      (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.VerifyStackedOpening.b1_next)) hc1 run_b2 (by decide +kernel) rfl
      (by decide +kernel) fun st2 hc2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_12_at] at hpc2
    refine contT st2 hpc2 ⟨hc2, ?_, ?_, ?_⟩ (by omega)
    · rw [show reg st2.data .rax = _ from hm2.regs .rax _ rfl]; exact hrax
    · rw [show reg st2.data .rcx = 0#64 from hm2.regs .rcx _ rfl, h1]; rfl
    · rw [show reg st2.data .rbx = 0#64 from hm2.regs .rbx _ rfl, h1]; rfl
  · simp only [h1, decide_false, Bool.not_false, ↓reduceIte] at hpc1
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_4_at] at hpc1
    refine h.cbRun hp b5_in_code (List.cons_ne_nil _ _) hpc1 hc1 run_b5 (by decide +kernel) rfl
      (by decide +kernel) fun st2 hc2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_7_at] at hpc2
    have h15' : reg st1.data .r15 = BitVec.ofNat 64 cs.size :=
      BitVec.eq_of_toNat_eq (by rw [hc1.r15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
    refine contH st2 hpc2 ⟨hc2, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show reg st2.data .rax = _ from hm2.regs .rax _ rfl]; exact hrax
    · rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ rfl]
      show (BinOp.apply .and .W32 (UnOp.apply .trunc .W32 (reg st1.data .r15))
        (BitVec.ofNat 64 254)).toNat = _
      rw [h15']
      exact and254 _ (by omega)
    · rw [show reg st2.data .rcx = 0#64 from hm2.regs .rcx _ rfl]; rfl
    · rw [show reg st2.data .rsi = _ from hm2.regs .rsi _ rfl]
      exact hc1.r13
    · rw [show reg st2.data .rbx = 0#64 from hm2.regs .rbx _ rfl]; rfl

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
