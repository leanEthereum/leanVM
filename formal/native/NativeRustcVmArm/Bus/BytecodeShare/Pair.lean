module

public import NativeRustcVmArm.Bus.BytecodeShare.Loop

/-!
# `bytecode_share`: the pair loop and the copy's entry

`pair`: a turn of `b18` from the head `.LBytecodeShare_12`, back there or (`b19`) to `b22` or the
odd tail. `copy_spec`: `b12` to `b17`, then the loop.
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr

public section

variable [Host] {a : DecArea} {s0 : TState} {m0 m : MachineData} {k : Nat} {sh v : EW}

/-- **A turn of the pair loop.** -/
theorem pair (hp : Placed code k) (h : BytecodeSharePre a s0 m0) (F : Fin a s0 m0 m sh v k)
    {j : Nat} {st : MachineData} (hd : PairHead m0 m sh v j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Goal a s0 m0 st' ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b18Offset) ∧ PairHead m0 m sh v (j + 2) st'.data))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b18Offset)⟩ := by
  obtain ⟨hS, -, -, -, -, -, hbl, -, hpo, -⟩ := pre_parts h
  have A := addr_of h
  have hN := A.sp
  have hlen := A.len
  have hc := hd.cp
  have hlt := hd.lt
  have hev := hd.even
  have hj16 : 16 * j + 32 ≤ 16 * m0.regs.X4.toNat := by omega
  obtain ⟨hmB, hnwB, hB⟩ := sub_range (d := st.dmem) (o := 16 * j) (n := 32)
    (fun i hi ↦ hc.fr.kept _ (hbl.1.1 i hi)) A.bnw hj16
  obtain ⟨hmP, hnwP, hP⟩ := sub_range (d := st.dmem) (o := 16 * j) (n := 32)
    (fun i hi ↦ hc.fr.kept _ (hpo.1 i hi)) A.pnw (by show _ ≤ 1072; omega)
  have hB' := hB (by omega)
  have hP' := hP (by show _ < 1072; omega)
  have hwf : (Env.ofMachine st [(base m0 432, 432),
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 32),
      (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j), 32)]).WF :=
    wf_frame3 hS N_ge hc.fr.kept hmB hnwB hmP hnwP
      (by have := A.bst; unfold Apart at this ⊢; rw [hB']; omega)
      (by have := A.pst; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hP']; omega)
      (by have := A.pb; rw [ptBytes_eq] at this; unfold Apart at this ⊢; rw [hB', hP']; omega)
  have hm := match_frame3 (n1 := 32) (n2 := 32) (c1 := 16) (c2 := 16) hS N_ge rfl hc.fr.sp
    (r1 := .X11) (r2 := .X12) (x1 := m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j))
    (x2 := m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j))
    (by rw [hd.x11, NativeRustcVm.addr_add_add]) (by rw [hd.x12, NativeRustcVm.addr_add_add])
  refine exec_then (b18_in_code.trans hp.1 (by simp [b18])) run_b18 hwf hm fun st2 hm2 hpc2 ↦ ?_
  have hW : ∀ w ∈ (after b18 frPair).mem, w.r = 2 ∧ w.off + w.n ≤ 32 := by
    rw [Bus.after_eq run_b18]; decide
  rw [Bus.after_eq run_b18] at hW
  have hfr2 : Fr m0 432 bytecodeShareStack slots keep (outsP m0) st2.data :=
    Fr.ofBlockW hc.fr hm hm2 hwf rfl rfl (fun r hr ↦ absurd hr List.not_mem_nil) rfl N_ge hN
      slots_le fun w hw ↦ writeOk_r2 (fun i hi ↦ .inr (by
        rw [NativeRustcVm.addr_add_add]
        exact NativeRustcVm.inRange_add (by show _ < 1072; omega) (by show 1072 ≤ _; omega)))
        (hW w hw)
  have hs := same_r2 hm2 hwf hW
  have hcpy := copy_words hm2 (rd := 2) (rr := 1) (od := 0) (os := 0) (nw := 4) rfl rfl
    (by omega) (by rw [NativeRustcVm.addr_add_zero]; exact hmB) (by decide)
  have hb := Fr.bytes_eq hc.fr hS A.bnw A.bst (b_not_outsP h)
  have hpn : m0.regs.X5.toBitVec.toNat + 1072 ≤ 2 ^ 64 := A.pnw
  have hc2 : Cp m0 m sh v (j + 2) st2.data := by
    refine ⟨hfr2, Regs.block hc.regs hm2 (by decide), (mov_reg hm2 rfl).trans hc.x8,
      by rw [mov_reg hm2 rfl]; exact hc.x9, by omega, fun i hi ↦ ?_, fun q hq ↦ ?_,
      kept_trans hc.kept (hm2.kept hwf)⟩
    · rcases Nat.lt_or_ge i (16 * j) with hi' | hi'
      · rw [hs _ fun hq ↦ ?_]
        · exact hc.cpy i hi'
        · rw [Sym.inRange_iff hnwP, hP', toNat_in A.pnw (by show _ < 1072; omega)] at hq
          omega
      · have e := hcpy (i - 16 * j) (by omega)
        simp only [Nat.zero_add, NativeRustcVm.addr_add_add] at e
        rw [show 16 * j + (i - 16 * j) = i by omega] at e
        rw [e, hb i (by omega)]
    · have h1 : ¬InRange (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j)) 32 q := fun h' ↦ hq (by
        rw [Sym.inRange_iff hnwP, hP'] at h'
        rw [Sym.inRange_iff (by omega)]
        omega)
      have h2 : ¬InRange m0.regs.X5.toBitVec (16 * j) q := fun h' ↦ hq (by
        rw [Sym.inRange_iff (by omega)] at h' ⊢
        omega)
      rw [hs q h1]
      exact hc.same q h2
  have e13 := hm2.regs .X13 _ rfl
  have e11 := hm2.regs .X11 _ rfl
  have e12 := hm2.regs .X12 _ rfl
  rw [show Sym.ptr 1 48 = Sym.ptr 1 ((48 : Nat) : Int) from rfl, eval_ptr_off _ _ rfl,
    NativeRustcVm.addr_add_add] at e11
  rw [show Sym.ptr 2 48 = Sym.ptr 2 ((48 : Nat) : Int) from rfl, eval_ptr_off _ _ rfl,
    NativeRustcVm.addr_add_add] at e12
  simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs] at e13
  have h13 := hd.x13
  have h13' : (st2.data.regs.getXReg .X13).toNat + (j + 2) =
      m0.regs.X4.toNat - m0.regs.X4.toNat % 2 := by
    have t2 : (BitVec.ofNat 64 2).toNat = 2 := rfl
    rw [← UInt64.toNat_toBitVec, e13, BitVec.toNat_sub_of_le, UInt64.toNat_toBitVec, t2]
    · omega
    · rw [BitVec.le_def]; show 2 ≤ (st.regs.getXReg .X13).toNat; omega
  have hcond : SBool.eval (Env.ofMachine st [(base m0 432, 432),
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (16 * j), 32),
      (m0.regs.X5.toBitVec + BitVec.ofNat 64 (16 * j), 32)])
      (.not (.cmp .eq .W64 (.reg .X13) (.lit 2))) =
      !decide ((st.regs.getXReg .X13).toNat = 2) := by
    show (!(SBool.cmp .eq .W64 (.reg .X13) (.lit 2)).eval _) = _
    rw [eval_eq_lit _ _ _ _ (by decide)]
  simp only [PcOk, hcond] at hpc2
  by_cases h2 : (st.regs.getXReg .X13).toNat = 2
  · -- out of the loop: `b19`.
    have hf : (!decide ((st.regs.getXReg .X13).toNat = 2)) = false := by rw [h2]; rfl
    rw [hf] at hpc2
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
    refine Eventually.mono (at_pc hpc2 ?_) fun _ h ↦ Or.inl h
    refine Fr.runBlock hS N_ge rfl hfr2 (b19_in_code.trans hp.1 (by simp [b19])) run_b19 rfl rfl
      (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
    have hc3 := Cp.ofRun hc2 hfr3 hd3 hm3 (by decide)
    have hx10 : (st2.data.regs.getXReg .X10).toNat = m0.regs.X4.toNat - m0.regs.X4.toNat % 2 := by
      rw [mov_reg hm2 rfl]; exact hd.x10
    have hc19 : SBool.eval (Env.ofMachine st2.data [(base m0 432, 432)])
        (.cmp .eq .W64 (.reg .X22) (.reg .X10)) =
        decide (m0.regs.X4.toNat = m0.regs.X4.toNat - m0.regs.X4.toNat % 2) := by
      rw [eval_eq_reg, hc2.regs.x22, hx10]
    simp only [PcOk, hc19] at hpc3
    by_cases he : m0.regs.X4.toNat = m0.regs.X4.toNat - m0.regs.X4.toNat % 2
    · rw [decide_eq_true he] at hpc3
      simp only [↓reduceIte] at hpc3
      refine at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b22Offset) NativeRustcVmArm.Vm.BytecodeShare.label_16_at)) (F.fin _ ?_)
      rw [show m0.regs.X4.toNat = j + 2 by omega]
      exact hc3
    · rw [decide_eq_false he] at hpc3
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc3
      refine at_pc hpc3 (odd hp h F hc3 ?_ (by omega))
      rw [mov_reg hm3 rfl, hx10]
      omega
  · have hf : (!decide ((st.regs.getXReg .X13).toNat = 2)) = true := by simp [h2]
    rw [hf] at hpc2
    simp only [↓reduceIte] at hpc2
    refine .done _ (.inr ⟨hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b18Offset) NativeRustcVmArm.Vm.BytecodeShare.label_12_at), hc2, by omega, by omega, ?_, h13',
      by rw [e11, show 16 * j + 48 = 16 * (j + 2) + 16 by omega],
      by rw [e12, show 16 * j + 48 = 16 * (j + 2) + 16 by omega]⟩)
    rw [mov_reg hm2 rfl]; exact hd.x10

/-- **The copy**, from `b12`: every element of `bytecode_low`, then `b22`. -/
theorem copy_spec (hp : Placed code k) (h : BytecodeSharePre a s0 m0) {st : MachineData}
    (F : Fin a s0 m0 st sh v k) (hfr : Fr m0 432 bytecodeShareStack slots keep (outsP m0) st)
    (hr : Regs m0 sh v st) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b12Offset)⟩ := by
  obtain ⟨hS, -⟩ := pre_parts h
  have A := addr_of h
  have hlen := A.len
  refine Fr.runBlock hS N_ge rfl hfr (b12_in_code.trans hp.1 (by simp [b12])) run_b12 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have e8 := hm1.regs .X8 _ rfl
  have e9 := hm1.regs .X9 _ rfl
  simp only [Sym.eval, BinOp.apply, UnOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs,
    shiftW, hr.x22, hr.x23] at e8 e9
  have hc1 : Cp m0 st sh v 0 st1.data := by
    refine ⟨hfr1, Regs.block hr hm1 (by decide), ?_, ?_, Nat.zero_le _, fun i hi ↦ absurd hi (by omega),
      fun q _ ↦ by rw [hd1], by rw [hd1]; exact fun _ h ↦ h⟩
    · apply UInt64.toBitVec_inj.mp
      rw [e8, UInt64.toBitVec_add]
      rfl
    · rw [e9]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]
      simp only [show MemWidth.W64.bits = 64 from rfl]
      omega
  have c12 : SBool.eval (Env.ofMachine st [(base m0 432, 432)]) (.cmp .eq .W64 (.reg .X22) (.lit 0)) =
      decide (m0.regs.X4.toNat = 0) := by
    rw [eval_eq_lit _ _ _ _ (by decide), hr.x22]
  simp only [PcOk, c12] at hpc1
  by_cases h0 : m0.regs.X4.toNat = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc1
    refine at_pc (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b22Offset) NativeRustcVmArm.Vm.BytecodeShare.label_16_at)) (F.fin _ ?_)
    rw [h0]; exact hc1
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine at_pc hpc1 (Fr.runBlock hS N_ge rfl hfr1 (b13_in_code.trans hp.1 (by simp [b13])) run_b13
    rfl rfl (by decide) (by decide) fun st2 hfr2 hd2 hm2 hpc2 ↦ ?_)
  have hc2 := Cp.ofRun hc1 hfr2 hd2 hm2 (by decide)
  have c13 : SBool.eval (Env.ofMachine st1.data [(base m0 432, 432)])
      (.not (.cmp .eq .W64 (.reg .X22) (.lit 1))) = !decide (m0.regs.X4.toNat = 1) := by
    show (!(SBool.cmp .eq .W64 (.reg .X22) (.lit 1)).eval _) = _
    rw [eval_eq_lit _ _ _ _ (by decide), hc1.regs.x22]
  simp only [PcOk, c13] at hpc2
  by_cases h1 : m0.regs.X4.toNat = 1
  · simp only [h1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc2
    refine at_pc hpc2 (Fr.runBlock hS N_ge rfl hfr2 (b14_in_code.trans hp.1 (by simp [b14]))
      run_b14 rfl rfl (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_)
    have hc3 := Cp.ofRun hc2 hfr3 hd3 hm3 (by decide)
    simp only [PcOk] at hpc3
    refine at_pc (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b20Offset) NativeRustcVmArm.Vm.BytecodeShare.label_14_at)) (odd hp h F hc3 ?_ (by omega))
    have := reg_lit hm3 (r := .X10) (n := 0) rfl
    rw [← UInt64.toNat_toBitVec, this]
    rfl
  simp only [h1, decide_false, Bool.not_false, ↓reduceIte] at hpc2
  refine at_pc (hpc2.trans (hp.label (j := NativeRustcVmArm.Vm.BytecodeShare.b17Offset) NativeRustcVmArm.Vm.BytecodeShare.label_11_at)) (Fr.runBlock hS N_ge rfl hfr2
    (b17_in_code.trans hp.1 (by simp [b17])) run_b17 rfl rfl (by decide) (by decide)
    fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_)
  have hc3 := Cp.ofRun hc2 hfr3 hd3 hm3 (by decide)
  have e10 := hm3.regs .X10 _ rfl
  have e11 := hm3.regs .X11 _ rfl
  have e12 := hm3.regs .X12 _ rfl
  have e13 := hm3.regs .X13 _ rfl
  simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs,
    hc2.regs.x22, hc2.regs.x23, hc2.regs.x24] at e10 e11 e12 e13
  have a62 := and62 m0.regs.X4 (by omega)
  simp only [PcOk] at hpc3
  have hI : PairHead m0 st sh v 0 st3.data := by
    refine ⟨hc3, rfl, by omega, ?_, ?_, ?_, ?_⟩
    · rw [← UInt64.toNat_toBitVec, e10, a62]
    · have := congrArg BitVec.toNat e13
      rw [UInt64.toNat_toBitVec, a62] at this
      omega
    · rw [e11]
    · rw [e12]
  refine Sym.loop (fun n (s : MachineState) ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BytecodeShare.b18Offset) ∧ ∃ j,
      m0.regs.X4.toNat - j = n ∧ PairHead m0 st sh v j s.data)
    (fun n st' ⟨hpc', j, hn, hI'⟩ ↦ ?_) ⟨hpc3, 0, rfl, hI⟩
  obtain ⟨d', pc'⟩ := st'
  simp only at hpc'
  subst hpc'
  refine Eventually.mono (pair hp h F hI') fun st'' h ↦ ?_
  rcases h with h | ⟨hpc'', hI''⟩
  · exact .inl h
  · exact .inr ⟨m0.regs.X4.toNat - (j + 2), by have := hI'.lt; omega, hpc'', j + 2, rfl, hI''⟩

end

end NativeRustcVmArm.Bus.BytecodeShare
