module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue.Step

/-!
# `multilinear_eval_by` (`computed_bytecode_value`'s closure) on AArch64

**`mleOfComputedBytecodeValue_spec`**: rustc's `multilinear_eval_by(n, |i| EW::of_k(words[i]),
point)`, placed anywhere in the program, meets `MleOfComputedBytecodeValuePre`/
`MleOfComputedBytecodeValuePost` given `EW::mul`'s contract. The prologue (`b0`) saves X19-X30 in
its 1232-byte frame; `|point| > 63` returns `0` (`b17`; the model's value is `0` too,
`Mle.multilinearEval_eq_zero`); `b1` zeroes the pending entries and the `full` flags; `n = 0`
returns `0`, `|point| = 0` returns `words[0]` (`b15`, `b16`); otherwise `b3` stores the arguments in
the frame and the loops (`outerLoop`) stream the entries (`NativeRustcVm.Mle.stream`,
`= multilinearEval` by `stream_eq`).
-/

namespace NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue
open NativeVm.Model NativeRustcArm NativeRustcVmArm.Arrays.MleFrame
open NativeRustcVm (wordOf wordsOf ewOf ewsOf)
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

/-- `b.hi` after `cmp x, #63`. -/
theorem gt63_iff (x : BitVec 64) :
    ((!((low .W64 x).ult (low .W64 (BitVec.ofNat 64 63)))) &&
      !(low .W64 x == low .W64 (BitVec.ofNat 64 63))) = true ↔ 63 < x.toNat := by
  rw [low_W64, low_W64]
  have h1 : x.ult (BitVec.ofNat 64 63) = decide (x.toNat < 63) := by
    rw [Bool.eq_iff_iff, BitVec.ult_iff_lt, BitVec.lt_def, decide_eq_true_iff]
    simp
  have h2 : (x == BitVec.ofNat 64 63) = decide (x.toNat = 63) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
    simp
  rw [h1, h2]
  by_cases a : x.toNat < 63 <;> by_cases b : x.toNat = 63 <;> simp [a, b] <;> omega

variable [Host] {k : Nat}

/-- **The outer loop**: from entry `0`, the postcondition. -/
theorem outerLoop (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : LPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset)) (hO : Outer m0 0 s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b4Offset) ∧ ∃ i, nn m0 - i = n ∧ Outer m0 i s.data)
    (fun n s ⟨hpc, i, hn, hO⟩ ↦ ?_) ⟨hpc, 0, rfl, hO⟩
  refine Eventually.bind (outer hp hpre hpc hO) fun s1 ⟨hpc1, hI⟩ ↦ ?_
  refine Eventually.mono (innerLoop hp hmul hpre hpc1 hI) fun s' h ↦ ?_
  rcases h with h | ⟨hpc', hO'⟩
  · exact Or.inl h
  · exact Or.inr ⟨nn m0 - (i + 1), by have := hO.hi; omega, hpc', i + 1, rfl, hO'⟩

/-- **`0` returned** (`b17`, the epilogue) when the value is `0`. -/
theorem zero (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 mleStack) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Offset)) (hb : Body m0 1232 mleStack slots0 0 0 s.data)
    (h0 : target m0 = 0) : Eventually (step1 Host.exe) (Post m0) s :=
  exec_at (hb17 hp) run_b17 (Env.wf_nil _) hpc (match_nil _) fun s2 hm2 hpc2 ↦ by
    have bd2 := hb.of_block (match_nil _) hm2 (Env.wf_nil _) rfl
      (by rw [kept_nil.2]; exact after_eq run_b17 ▸ keeps.2.2.2.2.2.2.2.2.2.2.1)
    simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b17Length] at hpc2
    refine finish hp hS b18_restores.1 (by simp [slots0]) hpc2 bd2 ?_
    rw [h0]
    show (⟨s2.data.regs.getXReg .X22, s2.data.regs.getXReg .X23⟩ : EW) = 0
    rw [reg_of hm2 (r := .X22) rfl, reg_of hm2 (r := .X23) rfl]
    rfl

/-- **`multilinear_eval_by` (`computed_bytecode_value`'s closure) meets its contract.** -/
theorem mleOfComputedBytecodeValue_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel) MleOfComputedBytecodeValuePre
      MleOfComputedBytecodeValuePost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, h02, hrW, hoW, hrP⟩ := hpre
  obtain ⟨hwf, hm⟩ := entry_match hS (show 1232 ≤ mleStack by decide) rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b0_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b0Length] at hpc1
  have hpc1' := pc_cond hpc1
  have e02 : m0.regs.X0.toNat = m0.regs.X2.toNat := congrArg UInt64.toNat h02
  have e4 : (m0.regs.getXReg .X4).toBitVec.toNat = m0.regs.X4.toNat := rfl
  by_cases h64 : 63 < m0.regs.X4.toNat
  · -- `|point| > 63`: `0`.
    have hpc2 := hpc1'.1 (by
      show ((!((low .W64 (m0.regs.getXReg .X4).toBitVec).ult (low .W64 (BitVec.ofNat 64 63)))) &&
        !(low .W64 (m0.regs.getXReg .X4).toBitVec == low .W64 (BitVec.ofNat 64 63))) = true
      rw [gt63_iff, e4]; exact h64)
    refine zero hp hS (hpc2.trans (lbl_13 hp)) (body_of hS hm1 (after_eq run_b0 ▸ b0_frame)
      kept_nil.2) ?_
    rw [target_eq, NativeRustcVm.Mle.multilinearEval_eq_zero]
    simp only [wordSliceE, slice, List.size_toArray, List.length_map, NativeRustcVm.length_wordsOf,
      NativeRustcVm.length_ewsOf]
    exact Nat.lt_of_lt_of_le m0.regs.X2.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega))
  · have hpc2 := hpc1'.2 (by
      show ¬((!((low .W64 (m0.regs.getXReg .X4).toBitVec).ult (low .W64 (BitVec.ofNat 64 63)))) &&
        !(low .W64 (m0.regs.getXReg .X4).toBitVec == low .W64 (BitVec.ofNat 64 63))) = true
      rw [gt63_iff, e4]; exact h64)
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc2 hm1 fun s2 hm2 hpc3 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b1_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b1Length] at hpc3
    sym_simp at hpc3
    have hpc3' := pc_cond hpc3
    by_cases hz : m0.regs.X2.toNat = 0
    · -- `n = 0`: `0`.
      have hpc4 := hpc3'.1 (by
        show ((m0.regs.getXReg .X0).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        apply BitVec.eq_of_toNat_eq
        show m0.regs.X0.toNat = 0
        omega)
      refine zero hp hS (hpc4.trans (lbl_13 hp)) (body_of hS hm2 (after_eq run_b1 ▸ b1_frame)
        kept_nil.2) ?_
      have he : ents m0 = [] := List.eq_nil_of_length_eq_zero (by simp [hz])
      rw [target, he]
      rfl
    have hoW' := hoW (Nat.pos_of_ne_zero hz)
    have hpc4 := hpc3'.2 (by
      show ¬((m0.regs.getXReg .X0).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
      exact hz (e02 ▸ this))
    refine exec_at (hb2 hp) (exec_after run_b1 run_b2) hwf hpc4 hm2 fun s3 hm3 hpc5 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b2_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b2Length] at hpc5
    sym_simp at hpc5
    have hpc5' := pc_cond hpc5
    by_cases hz4 : m0.regs.X4.toNat = 0
    · -- `|point| = 0`: `words[0]`.
      have hpc6 := hpc5'.1 (by
        show ((m0.regs.getXReg .X4).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        exact BitVec.eq_of_toNat_eq hz4)
      refine exec_at (hb15 hp) (exec_after run_b2 run_b15) hwf (hpc6.trans (lbl_11 hp)) hm3
        fun s4 hm4 hpc7 ↦ ?_
      have bd4 := body_of hS hm4 (after_eq run_b15 ▸ b15_frame) kept_nil.2
      simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b15_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b15Length] at hpc7
      sym_simp at hpc7
      have hpc7' := (pc_cond hpc7).2 (by
        show ¬((m0.regs.getXReg .X2).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        intro h
        exact hz (congrArg BitVec.toNat h))
      have hx1 : (s4.data.regs.getXReg .X1).toBitVec = m0.regs.X1.toBitVec := hm4.regs .X1 _ rfl
      obtain ⟨st, pc⟩ := s4
      simp only at hpc7' bd4 hx1
      have hel := word_mapped (i := 0) hrW bd4.kept (Nat.pos_of_ne_zero hz)
      rw [Nat.mul_zero, add_ofNat_zero] at hel
      have hwf5 := wf_one hel.1 hel.2 (m := st)
      have hm5 : Match (Env.ofMachine st [(m0.regs.X1.toBitVec, 8)]) wordS st :=
        match_ofMachine ⟨rfl, nofun, trivial⟩ rfl ⟨hx1.trans (BitVec.add_zero _).symm, trivial⟩
          trivial trivial trivial
      refine exec_at (hb16 hp) run_b16 hwf5 hpc7' hm5 fun s5 hm6 hpc8 ↦ ?_
      have bd5 := bd4.of_block hm5 hm6 hwf5 rfl
        (by rw [kept_nil.2]; exact after_eq run_b16 ▸ keeps.2.2.2.2.2.2.2.2.2.2.2)
      simp only [PcOk] at hpc8
      refine finish hp hS b18_restores.1 (by simp [slots0]) (hpc8.trans (lbl_14 hp)) bd5 ?_
      have hw0 := word_of_apart (i := 0) bd4.same hS hrW.2 hoW' (Nat.pos_of_ne_zero hz)
      rw [Nat.mul_zero, add_ofNat_zero] at hw0
      have hd : (ents m0).drop 0 = _ := List.drop_eq_getElem_cons (by simp; omega)
      rw [List.drop_zero] at hd
      rw [target, hd, NativeRustcVm.Mle.stream_cons, NativeRustcVm.Mle.cont_top _ (by simp [hz4]),
        List.getElem_map, ← hw0]
      show (⟨s5.data.regs.getXReg .X22, s5.data.regs.getXReg .X23⟩ : EW) = ⟨_, 0⟩
      rw [reg_of hm6 (r := .X22) rfl, reg_of hm6 (r := .X23) rfl]
      simp only [Sym.eval]
      rw [load8_eq]
      show (⟨UInt64.ofBitVec (wordOf st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 0)).toBitVec,
        _⟩ : EW) = _
      rw [add_ofNat_zero, UInt64.ofBitVec_toBitVec]
      rfl
    · have hpc6 := hpc5'.2 (by
        show ¬((m0.regs.getXReg .X4).toBitVec == 0#64) = true
        rw [beq_iff_eq]
        intro h
        exact hz4 (congrArg BitVec.toNat h))
      refine exec_at (hb3 hp) (exec_after run_b2 run_b3) hwf hpc6 hm3 fun s4 hm4 hpc7 ↦ ?_
      simp only [PcOk, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b3_length, NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.b3Length] at hpc7
      have bd4 := body_of hS hm4 (after_eq run_b3 ▸ b3_frame) kept_nil.1
      have hw := after_eq run_b3 ▸ b3_words
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hw
      have hfl : ∀ j < 64, s4.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 (1072 + j)) = some 0 := by
        intro j hj
        have := hm4.mem 0 (fbOf m0) 1232 rfl (1072 + j) (by omega)
        rw [this]
        unfold memByte
        rw [hw.1 j hj]
        simp [Sym.eval, byteOf]
      refine outerLoop hp hmul ⟨hS, h02, by omega, ⟨hrW, hoW'⟩, hrP⟩ (k := k) hpc7
        ⟨⟨bd4, ?_, ?_⟩, Nat.pos_of_ne_zero hz, Nat.pos_of_ne_zero hz4, ?_, ?_⟩
      · have hb := hm4.bytesAt_write (r := 0) rfl (show 24 + 8 ≤ 1232 by decide) hw.2
        have hv : Sym.eval (frameEnv m0 m0 1232) (.bin .add .W64 (.reg .X3) (.lit 8)) =
            m0.regs.X3.toBitVec + BitVec.ofNat 64 8 := by
          simp [Sym.eval, BinOp.apply]
          rfl
        rw [hv, ← UInt64.toBitVec_ofBitVec (m0.regs.X3.toBitVec + BitVec.ofNat 64 8),
          byteOf_wordBytes] at hb
        show (wordOf s4.data.dmem
          (m0.regs.SP.toBitVec - BitVec.ofNat 64 1232 + BitVec.ofNat 64 24)).toBitVec = _
        rw [NativeRustcVm.wordOf_of_wordAt hb]
      · exact fun j hj ↦ .inl (hfl j hj)
      · show (s4.data.regs.getXReg .X29).toNat = 0
        rw [reg_of hm4 (r := .X29) rfl]
        rfl
      · rw [pendOf_zero hfl, List.drop_zero]

end

end NativeRustcVmArm.Arrays.MleOfComputedBytecodeValue
