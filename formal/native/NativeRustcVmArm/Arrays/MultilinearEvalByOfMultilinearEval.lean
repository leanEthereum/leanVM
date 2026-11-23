module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval.Step

/-!
# `multilinear_eval_by` (`multilinear_eval`'s closure) on AArch64

**`mleOfMultilinearEval_spec`**: rustc's `multilinear_eval_by(n, |i| mle[i], point)`, placed
anywhere in the program, meets `MleOfMultilinearEvalPre`/`MleOfMultilinearEvalPost` given
`EW::mul`'s contract. The prologue (`b0`) saves X19-X30 in its 1232-byte frame and zeroes the
pending entries and the `full` flags; `n = 0` returns `0` (`b16`), `|point| = 0` returns `mle[0]`
(`b14`, `b15`); otherwise `b2` stores the arguments in the frame and the loops
(`outerLoop`) stream the entries (`NativeRustcVm.Mle.stream`, `= multilinearEval` by
`stream_eq`).
-/

namespace NativeRustcVmArm.Arrays.MleOfMultilinearEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf ewOf ewsOf)
open NativeRustcVm.Mle (stream cont setP)

public section

theorem frameOk_props {sl : List (Nat × XReg)} {S : SState} (h : FrameOk sl S = true) :
    (∀ p ∈ sl, p.1 + 8 ≤ 1232 ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i)) ∧
      (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 1232) ∧ S.sp = .ptr 0 0 := by
  simp only [FrameOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨fun p hp ↦ ⟨(h1 p hp).1, fun i hi ↦ (h1 p hp).2 i hi⟩, h2, h3⟩

/-- The body after the prologue, from the frame's facts. -/
theorem body_of [Labels] {m0 st : MachineData} {sl : List (Nat × XReg)} {S : SState}
    (hS : StackOk m0 mleStack) (hm : Match (frameEnv m0 m0 1232) S st) (h : FrameOk sl S = true)
    (hk : (calleeRegs.filter fun r ↦ !inSlots sl r) = []) : Body m0 1232 mleStack sl 0 0 st := by
  obtain ⟨hw, hmem, hsp⟩ := frameOk_props h
  refine Body.of_entry hS (by decide) hm hsp hw (fun r hr hn ↦ ?_) hmem
  have : r ∈ calleeRegs.filter fun r ↦ !inSlots sl r := List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  rw [hk] at this
  cases this

variable [Host] {k : Nat}

/-- **The outer loop**: from entry `0`, the postcondition. -/
theorem outerLoop (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : MleOfMultilinearEvalPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset)) (hO : Outer m0 0 s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b3Offset) ∧ ∃ i, nn m0 - i = n ∧ Outer m0 i s.data)
    (fun n s ⟨hpc, i, hn, hO⟩ ↦ ?_) ⟨hpc, 0, rfl, hO⟩
  refine Eventually.bind (outer hp hpre hpc hO) fun s1 ⟨hpc1, hI⟩ ↦ ?_
  refine Eventually.mono (innerLoop hp hmul hpre hpc1 hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hO'⟩
  · exact Or.inl h
  · exact Or.inr ⟨nn m0 - (i + 1), by have := hO.hi; omega, hpc', i + 1, rfl, hO'⟩

/-- **`multilinear_eval_by` (`multilinear_eval`'s closure) meets its contract.** -/
theorem mleOfMultilinearEval_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, h02, h64, hrM, hrP⟩ := hpre
  obtain ⟨hwf, hm⟩ := entry_match hS (show 1232 ≤ mleStack by decide) rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b0_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have e02 : m0.regs.X0.toNat = m0.regs.X2.toNat := congrArg UInt64.toNat h02
  by_cases hz : m0.regs.X2.toNat = 0
  · -- `n = 0`: `0`.
    have hpc2 := hpc1'.1 (by
      show ((m0.regs.getXReg .X0).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      show m0.regs.X0.toNat = 0
      omega)
    have bd1 := body_of hS hm1 (after_eq run_b0 ▸ b0_frame) kept_nil.2
    refine exec_at (hb16 hp) run_b16 (Env.wf_nil _) (hpc2.trans (lbl_12 hp)) (match_nil _)
      fun s2 hm2 hpc2' ↦ ?_
    have bd2 := bd1.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (by rw [kept_nil.2]; exact after_eq run_b16 ▸ keeps.2.2.2.2.2.2.2.2.2.2.1)
    simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b16_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b16Length] at hpc2'
    refine finish hp hS b17_restores.1 (by simp [slots0]) hpc2' bd2 ?_
    have he : ents m0 = [] := List.eq_nil_of_length_eq_zero (by simp [hz])
    rw [target, he]
    show (⟨s2.data.regs.getXReg .X23, s2.data.regs.getXReg .X24⟩ : EW) = stream _ [] _
    rw [reg_of hm2 (r := .X23) rfl, reg_of hm2 (r := .X24) rfl]
    rfl
  · have hpc2 := hpc1'.2 (by
      show ¬((m0.regs.getXReg .X0).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      exact hz (e02 ▸ this))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc2 hm1 fun s2 hm2 hpc3 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b1_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b1Length] at hpc3
    sym_simp at hpc3
    have hpc3' := pc_cond hpc3
    by_cases hz4 : m0.regs.X4.toNat = 0
    · -- `|point| = 0`: `mle[0]`.
      have hpc4 := hpc3'.1 (by
        show ((m0.regs.getXReg .X4).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        exact BitVec.eq_of_toNat_eq hz4)
      refine exec_at (hb14 hp) (exec_after run_b1 run_b14) hwf (hpc4.trans (lbl_10 hp)) hm2
        fun s3 hm3 hpc5 ↦ ?_
      have bd3 := body_of hS hm3 (after_eq run_b14 ▸ b14_frame) kept_nil.2
      simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b14_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b14Length] at hpc5
      sym_simp at hpc5
      have hpc5' := (pc_cond hpc5).2 (by
        show ¬((m0.regs.getXReg .X2).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        intro h
        exact hz (congrArg BitVec.toNat h))
      have hx1 := hm3.regs .X1 _ rfl
      refine load_step (lo := .X23) (hi' := .X24) (hb15 hp) run_b15 rfl rfl
        (by rw [kept_nil.2]; exact after_eq run_b15 ▸ keeps.2.2.2.2.2.2.2.2.2.2.2) [] rfl bd3 hS
        hrM.1 hrM.2 (apart_zero _ _) noWrap_zero (Nat.pos_of_ne_zero hz) hpc5'
        (by
          rw [hx1]
          show (m0.regs.getXReg .X1).toBitVec =
            m0.regs.X1.toBitVec + BitVec.ofNat 64 0 + BitVec.ofInt 64 0
          rw [add_ofNat_zero]
          exact (BitVec.add_zero _).symm) fun s4 hm4 hpc6 bd4 hv _ ↦ ?_
      simp only [PcOk] at hpc6
      refine finish hp hS b17_restores.1 (by simp [slots0]) (hpc6.trans (lbl_13 hp)) bd4 ?_
      have hd : (ents m0).drop 0 = _ := List.drop_eq_getElem_cons (by simp; omega)
      rw [List.drop_zero] at hd
      rw [target, hd, NativeRustcVm.Mle.stream_cons, NativeRustcVm.Mle.cont_top _ (by simp [hz4])]
      exact hv
    · have hpc4 := hpc3'.2 (by
        show ¬((m0.regs.getXReg .X4).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        intro h
        exact hz4 (congrArg BitVec.toNat h))
      refine exec_at (hb2 hp) (exec_after run_b1 run_b2) hwf hpc4 hm2 fun s3 hm3 hpc5 ↦ ?_
      simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b2_length, NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.b2Length] at hpc5
      have bd3 := body_of hS hm3 (after_eq run_b2 ▸ b2_frame) kept_nil.1
      have hw := after_eq run_b2 ▸ b2_words
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hw
      have hfl : ∀ j < 64, s3.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (1072 + j)) = some 0 := by
        intro j hj
        have := hm3.mem 0 (fbOf m0) 1232 rfl (1072 + j) (by omega)
        rw [this]
        unfold memByte
        rw [hw.1 j hj]
        simp [Sym.eval, byteOf]
      refine outerLoop hp hmul ⟨hS, h02, h64, hrM, hrP⟩ (k := k) hpc5 ⟨⟨bd3, ?_, ?_⟩, Nat.pos_of_ne_zero hz,
        Nat.pos_of_ne_zero hz4, ?_, ?_⟩
      · have hb := hm3.bytesAt_write (r := 0) rfl (show 24 + 8 ≤ 1232 by decide) hw.2
        have hv : Sym.eval (frameEnv m0 m0 1232) (.bin .add .W64 (.reg .X3) (.lit 8)) =
            m0.regs.X3.toBitVec + BitVec.ofNat 64 8 := by
          simp [Sym.eval, BinOp.apply]
          rfl
        rw [hv, ← UInt64.toBitVec_ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 8),
          byteOf_wordBytes] at hb
        show (wordOf s3.data.dmem
          (m0.regs.SP.toBitVec - BitVec.ofNat 64 1232 + BitVec.ofNat 64 24)).toBitVec = _
        rw [NativeRustcVm.wordOf_of_wordAt hb]
      · exact fun j hj ↦ .inl (hfl j hj)
      · show (s3.data.regs.getXReg .X29).toNat = 0
        rw [reg_of hm3 (r := .X29) rfl]
        rfl
      · rw [pendOf_zero hfl, List.drop_zero]

end

end NativeRustcVmArm.Arrays.MleOfMultilinearEval
