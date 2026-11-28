module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Bus.GkrStep.Eval

/-!
# `gkr_step`'s new values, `b23` to `b28`

`eval_spec`: from `AtEval` to `AtCopy` (or the failure exit, never taken: `|xs| + step ≤ 63`).
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVmArm.Bus.Gkr
open NativeRustcVmArm.Sumcheck (Ctx At)

public section
variable [Host] {a : DecArea} {s0 : TState} {g0 : GkrStateW} {m0 : MachineData} {k : Nat}

omit [Host] in
theorem len16 (x : EW) : ([x].flatMap NativeRustcVm.ewBytes).length ≤ 16 := by
  rw [NativeRustcVm.length_ewsBytes, List.length_singleton]

/-- **The new values** (`b23` to `b26`), then the point (`b27`, `b28`). -/
theorem eval_spec (hp : Placed code k) (h : GkrStepPre a s0 g0 m0)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {xs h0 h1 h2 y : Array EW} {s' : TState}
    (hcopy : ∀ m, AtCopy a s0 g0 m0 xs y
      #[multilinearEval h0 y, multilinearEval h1 y, multilinearEval h2 y] s' m →
      Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b29Offset)⟩)
    {m : MachineData} (hi : AtEval a s0 g0 m0 xs h0 h1 h2 y s' m) :
    Eventually (step1 Host.exe) (Goal a s0 g0 m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.GkrStep.b23Offset)⟩ := by
  have hS := pre_stack h
  have hn := two_pow_le h
  have hxl := xs_le hi.size
  have hstep := pre_step h
  have hyl : y.toList.length = m0.regs.X1.toNat := by rw [Array.length_toList, hi.ysize]
  have R := hi.regs
  -- `b23`
  refine Fr.runBlock hS N_ge rfl hi.fr (b23_in_code.trans hp.1 (by simp [b23])) run_b23 rfl rfl
    (by decide) (by decide) fun st hfr hd hm hpc ↦ ?_
  have R1 := R.block hm (by decide +kernel) ((reg_of hm rfl).trans R.x19)
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b23_length, NativeRustcVmArm.Vm.GkrStep.b23Length, show k + NativeRustcVmArm.Vm.GkrStep.b23Offset + 6 = k + NativeRustcVmArm.Vm.GkrStep.b24Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b23_length, NativeRustcVmArm.Vm.GkrStep.b23Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b23_next] at hpc
  refine mle_call h hmle (o := 1024) (by omega) hfr hpc (by rw [hd]; exact hi.c0)
    (by rw [hd]; exact hi.ys) hi.s0' hi.ysize
    ((reg_of hm (r := .X0) (r' := .X26) rfl).trans (reg_of hm (r := .X2) (r' := .X26) rfl).symm)
    (by show (st.data.regs.getXReg .X1).toBitVec = _; rw [hm.regs .X1 _ rfl]; rfl)
    (by show (st.data.regs.getXReg .X2).toBitVec.toNat = _
        rw [reg_of hm (r := .X2) (r' := .X26) rfl, R.x26,
          NativeRustcVm.toNat_ofNat_of_lt (by omega)])
    (by show (st.data.regs.getXReg .X3).toBitVec = _; rw [hm.regs .X3 _ rfl]; rfl)
    ((reg_of hm (r := .X4) (r' := .X20) rfl).trans R.x20)
    fun m2 hfr2 hv0 hcs2 hc2 hk2 ↦ ?_
  have R2 := R1.call hcs2
  have kx2 := ews_leaf hS hfr.sp le_mle hc2 (o := 16) (xs := xs.toList) (by omega)
    (by rw [hd]; exact hi.hxs)
  have kc1 := ews_leaf hS hfr.sp le_mle hc2 (o := 1088) (xs := h1.toList) (by
    rw [Array.length_toList, hi.s1']; omega) (by rw [hd]; exact hi.c1)
  have kc2 := ews_leaf hS hfr.sp le_mle hc2 (o := 1152) (xs := h2.toList) (by
    rw [Array.length_toList, hi.s2']; omega) (by rw [hd]; exact hi.c2)
  have ky2 := ews_leaf hS hfr.sp le_mle hc2 (o := 1264) (xs := y.toList) (by omega)
    (by rw [hd]; exact hi.ys)
  have kt2 := ts_leaf h hfr le_mle hc2 hk2 (by rw [hd]; exact hi.ts)
  -- `b24`: values[0]
  have hm3 := match_p h hfr2 R2.x19
  have hwf3 := wf_p h hfr2
  refine exec_then (b24_in_code.trans hp.1 (by simp [b24])) run_b24 hwf3 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hfr3 := fr_p h hfr2 hm3 hm3' rfl (by decide +kernel)
  have R3 := R2.block hm3' (by decide +kernel)
    (UInt64.toBitVec_inj.mp ((hm3'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl)))
  have V0 : NativeRustcVm.EWsAt st3.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 0)
      [multilinearEval h0 y] := by
    have w0 := Transcript.wordAt_write hm3' (r := 1) (o := 0) rfl (by omega) (v := .reg .X0)
      (by decide +kernel)
    have w8 := Transcript.wordAt_write hm3' (r := 1) (o := 8) rfl (by omega) (v := .reg .X1)
      (by decide +kernel)
    exact ew_words (by rw [← hv0]; exact w0) (by rw [← hv0]; exact w8)
  have kx3 := ews_p hm3' hwf3 (by decide +kernel) (o := 16) (by omega) kx2
  have kc13 := ews_p hm3' hwf3 (by decide +kernel) (o := 1088) (by
    rw [Array.length_toList, hi.s1']; omega) kc1
  have kc23 := ews_p hm3' hwf3 (by decide +kernel) (o := 1152) (by
    rw [Array.length_toList, hi.s2']; omega) kc2
  have ky3 := ews_p hm3' hwf3 (by decide +kernel) (o := 1264) (by omega) ky2
  have kt3 := ts_p h hm3' hwf3 (by decide +kernel) kt2
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b24_length, NativeRustcVmArm.Vm.GkrStep.b24Length, show k + NativeRustcVmArm.Vm.GkrStep.b24Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b25Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b24_length, NativeRustcVmArm.Vm.GkrStep.b24Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b24_next] at hpc3
  refine mle_call h hmle (o := 1088) (by omega) hfr3 hpc3 kc13 ky3 hi.s1' hi.ysize
    ((reg_of hm3' (r := .X0) (r' := .X26) rfl).trans
      (reg_of hm3' (r := .X2) (r' := .X26) rfl).symm)
    (by show (st3.data.regs.getXReg .X1).toBitVec = _
        rw [hm3'.regs .X1 _ rfl]
        show BinOp.apply .add .W64 (m2.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 64) = _
        rw [R2.x27, add_loc])
    (by show (st3.data.regs.getXReg .X2).toBitVec.toNat = _
        rw [reg_of hm3' (r := .X2) (r' := .X26) rfl, R2.x26,
          NativeRustcVm.toNat_ofNat_of_lt (by omega)])
    (by show (st3.data.regs.getXReg .X3).toBitVec = _; rw [hm3'.regs .X3 _ rfl]; rfl)
    ((reg_of hm3' (r := .X4) (r' := .X20) rfl).trans R2.x20)
    fun m4 hfr4 hv1 hcs4 hc4 hk4 ↦ ?_
  have R4 := R3.call hcs4
  have kx4 := ews_leaf hS hfr3.sp le_mle hc4 (o := 16) (xs := xs.toList) (by omega) kx3
  have kc24 := ews_leaf hS hfr3.sp le_mle hc4 (o := 1152) (xs := h2.toList) (by
    rw [Array.length_toList, hi.s2']; omega) kc23
  have ky4 := ews_leaf hS hfr3.sp le_mle hc4 (o := 1264) (xs := y.toList) (by omega) ky3
  have kt4 := ts_leaf h hfr3 le_mle hc4 hk4 kt3
  have V04 := out_leaf h hfr3 le_mle hc4 (o := 0) (by rw [NativeRustcVm.length_ewsBytes]; simp) V0
  -- `b25`: values[1]
  have hm5 := match_p h hfr4 R4.x19
  have hwf5 := wf_p h hfr4
  refine exec_then (b25_in_code.trans hp.1 (by simp [b25])) run_b25 hwf5 hm5 fun st5 hm5' hpc5 ↦ ?_
  have hfr5 := fr_p h hfr4 hm5 hm5' rfl (by decide +kernel)
  have R5 := R4.block hm5' (by decide +kernel)
    (UInt64.toBitVec_inj.mp ((hm5'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl)))
  have V1 : NativeRustcVm.EWsAt st5.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 16)
      [multilinearEval h1 y] := by
    have w0 := Transcript.wordAt_write hm5' (r := 1) (o := 16) rfl (by omega) (v := .reg .X0)
      (by decide +kernel)
    have w8 := Transcript.wordAt_write hm5' (r := 1) (o := 24) rfl (by omega) (v := .reg .X1)
      (by decide +kernel)
    exact ew_words (by rw [← hv1]; exact w0) (by rw [← hv1]; exact w8)
  have V05 := out_p hm5' hwf5 (o := 0) (L := 16) (by omega) (by decide +kernel) (len16 _) V04
  have kx5 := ews_p hm5' hwf5 (by decide +kernel) (o := 16) (by omega) kx4
  have kc25 := ews_p hm5' hwf5 (by decide +kernel) (o := 1152) (by
    rw [Array.length_toList, hi.s2']; omega) kc24
  have ky5 := ews_p hm5' hwf5 (by decide +kernel) (o := 1264) (by omega) ky4
  have kt5 := ts_p h hm5' hwf5 (by decide +kernel) kt4
  simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b25_length, NativeRustcVmArm.Vm.GkrStep.b25Length, show k + NativeRustcVmArm.Vm.GkrStep.b25Offset + 7 = k + NativeRustcVmArm.Vm.GkrStep.b26Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b25_length, NativeRustcVmArm.Vm.GkrStep.b25Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b25_next] at hpc5
  refine mle_call h hmle (o := 1152) (by omega) hfr5 hpc5 kc25 ky5 hi.s2' hi.ysize
    ((reg_of hm5' (r := .X0) (r' := .X26) rfl).trans
      (reg_of hm5' (r := .X2) (r' := .X26) rfl).symm)
    (by show (st5.data.regs.getXReg .X1).toBitVec = _
        rw [hm5'.regs .X1 _ rfl]
        show BinOp.apply .add .W64 (m4.regs.getXReg .X27).toBitVec (BitVec.ofNat 64 128) = _
        rw [R4.x27, add_loc])
    (by show (st5.data.regs.getXReg .X2).toBitVec.toNat = _
        rw [reg_of hm5' (r := .X2) (r' := .X26) rfl, R4.x26,
          NativeRustcVm.toNat_ofNat_of_lt (by omega)])
    (by show (st5.data.regs.getXReg .X3).toBitVec = _; rw [hm5'.regs .X3 _ rfl]; rfl)
    ((reg_of hm5' (r := .X4) (r' := .X20) rfl).trans R4.x20)
    fun m6 hfr6 hv2 hcs6 hc6 hk6 ↦ ?_
  have R6 := R5.call hcs6
  have kx6 := ews_leaf hS hfr5.sp le_mle hc6 (o := 16) (xs := xs.toList) (by omega) kx5
  have ky6 := ews_leaf hS hfr5.sp le_mle hc6 (o := 1264) (xs := y.toList) (by omega) ky5
  have kt6 := ts_leaf h hfr5 le_mle hc6 hk6 kt5
  have V06 := out_leaf h hfr5 le_mle hc6 (o := 0) (by rw [NativeRustcVm.length_ewsBytes]; simp) V05
  have V16 := out_leaf h hfr5 le_mle hc6 (o := 16) (by rw [NativeRustcVm.length_ewsBytes]; simp) V1
  -- `b26`: values[2], the length's check.
  have hm7 := match_p h hfr6 R6.x19
  have hwf7 := wf_p h hfr6
  refine exec_then (b26_in_code.trans hp.1 (by simp [b26])) run_b26 hwf7 hm7 fun st7 hm7' hpc7 ↦ ?_
  have hfr7 := fr_p h hfr6 hm7 hm7' rfl (by decide +kernel)
  have R7 := R6.block hm7' (by decide +kernel)
    (UInt64.toBitVec_inj.mp ((hm7'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl)))
  have V2 : NativeRustcVm.EWsAt st7.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 32)
      [multilinearEval h2 y] := by
    have w0 := Transcript.wordAt_write hm7' (r := 1) (o := 32) rfl (by omega) (v := .reg .X0)
      (by decide +kernel)
    have w8 := Transcript.wordAt_write hm7' (r := 1) (o := 40) rfl (by omega) (v := .reg .X1)
      (by decide +kernel)
    exact ew_words (by rw [← hv2]; exact w0) (by rw [← hv2]; exact w8)
  have V07 := out_p hm7' hwf7 (o := 0) (L := 16) (by omega) (by decide +kernel) (len16 _) V06
  have V17 := out_p hm7' hwf7 (o := 16) (L := 16) (by omega) (by decide +kernel) (len16 _) V16
  have kx7 := ews_p hm7' hwf7 (by decide +kernel) (o := 16) (by omega) kx6
  have ky7 := ews_p hm7' hwf7 (by decide +kernel) (o := 1264) (by omega) ky6
  have kt7 := ts_p h hm7' hwf7 (by decide +kernel) kt6
  have hsum : (BinOp.apply .add .W64 (m6.regs.getXReg .X23).toBitVec
      (m6.regs.getXReg .X20).toBitVec).toNat = xs.size + m0.regs.X1.toNat := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add]
    rw [show (m6.regs.getXReg .X23).toBitVec.toNat = (m6.regs.getXReg .X23).toNat from rfl, R6.x23,
      R6.x20]
    have := hi.size
    have e : m0.regs.X1.toBitVec.toNat = m0.regs.X1.toNat := rfl
    unfold busPointCap at this
    rw [e]
    exact Nat.mod_eq_of_lt (by omega)
  have e8 : (st7.data.regs.getXReg .X8).toNat = xs.size + m0.regs.X1.toNat := by
    show (st7.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm7'.regs .X8 _ rfl]
    exact hsum
  have hc7 : SBool.eval (envP m0 m6)
      (.and (.not (.cmp .ult .W64 (.bin .add .W64 (.reg .X23) (.reg .X20)) (.lit 63)))
        (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X23) (.reg .X20)) (.lit 63)))) = false := by
    show ((!CmpOp.ult.apply .W64 (BinOp.apply .add .W64 (m6.regs.getXReg .X23).toBitVec
        (m6.regs.getXReg .X20).toBitVec) (BitVec.ofNat 64 63)) &&
      (!CmpOp.eq.apply .W64 (BinOp.apply .add .W64 (m6.regs.getXReg .X23).toBitVec
        (m6.regs.getXReg .X20).toBitVec) (BitVec.ofNat 64 63))) = false
    rw [ult_lit64 _ _ (by decide), eq_lit64 _ _ (by decide), hsum]
    have := hi.size
    unfold busPointCap at this
    by_cases h63 : xs.size + m0.regs.X1.toNat = 63
    · simp [h63]
    · simp [show xs.size + m0.regs.X1.toNat < 63 by omega]
  simp only [PcOk, hc7, Bool.false_eq_true, ↓reduceIte, NativeRustcVmArm.Vm.GkrStep.b26_length, NativeRustcVmArm.Vm.GkrStep.b26Length,
    show k + NativeRustcVmArm.Vm.GkrStep.b26Offset + 4 = k + NativeRustcVmArm.Vm.GkrStep.b27Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b26_length, NativeRustcVmArm.Vm.GkrStep.b26Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b26_next] at hpc7
  -- `b27`: the length, `y[0]`.
  have hm8 := match_p h hfr7 R7.x19
  have hwf8 := wf_p h hfr7
  refine at_pc hpc7 (exec_then (b27_in_code.trans hp.1 (by simp [b27])) run_b27 hwf8 hm8
    fun st8 hm8' hpc8 ↦ ?_)
  have hfr8 := fr_p h hfr7 hm8 hm8' rfl (by decide +kernel)
  have R8 := R7.block hm8' (by decide +kernel)
    (UInt64.toBitVec_inj.mp ((hm8'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl)))
  have V08 := out_p hm8' hwf8 (o := 0) (L := 16) (by omega) (by decide +kernel) (len16 _) V07
  have V18 := out_p hm8' hwf8 (o := 16) (L := 16) (by omega) (by decide +kernel) (len16 _) V17
  have V28 := out_p hm8' hwf8 (o := 32) (L := 16) (by omega) (by decide +kernel) (len16 _) V2
  have kx8 := ews_p hm8' hwf8 (by decide +kernel) (o := 16) (by omega) kx7
  have ky8 := ews_p hm8' hwf8 (by decide +kernel) (o := 1264) (by omega) ky7
  have kt8 := ts_p h hm8' hwf8 (by decide +kernel) kt7
  have hy0 : 0 < y.toList.length := by omega
  obtain ⟨y00, y08⟩ := ews_words (b := base m0 1392) (o := 1264) ky7 hy0
  have L0 : (envP m0 st7.data).load 0 1264 8 = (y.toList[0]'hy0).c0.toBitVec :=
    Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl y00
  have L8 : (envP m0 st7.data).load 0 1272 8 = (y.toList[0]'hy0).c1.toBitVec :=
    Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl y08
  have hlen : NativeRustcVm.WordAt st8.data.dmem (off m0.regs.X3.toBitVec 48)
      (y.size + xs.size).toUInt64 := by
    have w := Transcript.wordAt_write hm8' (r := 1) (o := 48) rfl (by omega) (v := .reg .X8)
      (by decide +kernel)
    have : UInt64.ofBitVec ((Sym.reg .X8).eval (envP m0 st7.data)) = (y.size + xs.size).toUInt64 := by
      apply UInt64.toNat_inj.mp
      show (st7.data.regs.getXReg .X8).toNat = _
      rw [e8, Nat.toUInt64_eq, UInt64.toNat_ofNat', hi.ysize]
      have := hi.size
      unfold busPointCap at this
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [← this]
    exact w
  have Y0 : NativeRustcVm.EWsAt st8.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 56)
      [y.toList[0]'hy0] := by
    have w0 := Transcript.wordAt_write hm8' (r := 1) (o := 56) rfl (by omega)
      (v := .load 0 1264 8) (by decide +kernel)
    have w8 := Transcript.wordAt_write hm8' (r := 1) (o := 64) rfl (by omega)
      (v := .load 0 1272 8) (by decide +kernel)
    simp only [Sym.eval] at w0 w8
    rw [L0] at w0
    rw [L8] at w8
    exact ew_words w0 w8
  have hc8 : SBool.eval (envP m0 st7.data) (.cmp .eq .W64 (.reg .X20) (.lit 1)) =
      decide (m0.regs.X1.toNat = 1) := by
    show CmpOp.eq.apply .W64 (st7.data.regs.getXReg .X20).toBitVec (BitVec.ofNat 64 1) = _
    rw [eq_lit64 _ _ (by decide), R7.x20]
    rfl
  simp only [PcOk, hc8, NativeRustcVmArm.Vm.GkrStep.b27_length, NativeRustcVmArm.Vm.GkrStep.b27Length, show k + NativeRustcVmArm.Vm.GkrStep.b27Offset + 6 = k + NativeRustcVmArm.Vm.GkrStep.b28Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b27_length, NativeRustcVmArm.Vm.GkrStep.b27Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b27_next] at hpc8
  have hrun : run0 s0 g0 m0 = some (⟨#[multilinearEval h0 y, multilinearEval h1 y,
      multilinearEval h2 y], y ++ xs⟩, s') := hi.run
  have vals : ∀ d : DataMem,
      NativeRustcVm.EWsAt d (m0.regs.X3.toBitVec + BitVec.ofNat 64 0) [multilinearEval h0 y] →
      NativeRustcVm.EWsAt d (m0.regs.X3.toBitVec + BitVec.ofNat 64 16) [multilinearEval h1 y] →
      NativeRustcVm.EWsAt d (m0.regs.X3.toBitVec + BitVec.ofNat 64 32) [multilinearEval h2 y] →
      NativeRustcVm.EWsAt d m0.regs.X3.toBitVec
        #[multilinearEval h0 y, multilinearEval h1 y, multilinearEval h2 y].toList := by
    intro d a0 a1 a2
    have := ews_cons a0 (ews_cons a1 a2)
    rwa [NativeRustcVm.addr_add_zero] at this
  by_cases hs1 : m0.regs.X1.toNat = 1
  · simp only [hs1, decide_true, ↓reduceIte] at hpc8
    have hy1 : y.toList = [y.toList[0]'hy0] := by
      obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp (hyl.trans hs1)
      simp [hz]
    refine at_pc (hpc8.trans (hp.label (j := NativeRustcVmArm.Vm.GkrStep.b29Offset) NativeRustcVmArm.Vm.GkrStep.label_11_at)) (hcopy st8.data
      { fr := hfr8
        x19 := R8.x19
        x20 := R8.x20
        x23 := R8.x23
        size := hi.size
        ysize := hi.ysize
        vsize := rfl
        hxs := kx8
        vals := vals _ V08 V18 V28
        len := hlen
        ys := by rw [hy1]; exact Y0
        ts := kt8
        run := hrun })
  · simp only [hs1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc8
    have hs2 : m0.regs.X1.toNat = 2 := by omega
    have hy1' : 1 < y.toList.length := by omega
    -- `b28`: `y[1]`.
    have hm9 := match_p h hfr8 R8.x19
    have hwf9 := wf_p h hfr8
    refine exec_at (b28_in_code.trans hp.1 (by simp [b28])) run_b28 hwf9 hpc8 hm9
      fun st9 hm9' hpc9 ↦ ?_
    have hfr9 := fr_p h hfr8 hm9 hm9' rfl (by decide +kernel)
    have R9 := R8.block hm9' (by decide +kernel)
      (UInt64.toBitVec_inj.mp ((hm9'.regs .X19 _ rfl).trans (Transcript.eval_ptr rfl)))
    obtain ⟨y10, y18⟩ := ews_words (b := base m0 1392) (o := 1264) ky8 hy1'
    have L0' : (envP m0 st8.data).load 0 1280 8 = (y.toList[1]'hy1').c0.toBitVec :=
      Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl y10
    have L8' : (envP m0 st8.data).load 0 1288 8 = (y.toList[1]'hy1').c1.toBitVec :=
      Transcript.load_ofMachine (b := base m0 1392) (n := 1392) rfl y18
    have Y1 : NativeRustcVm.EWsAt st9.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 72)
        [y.toList[1]'hy1'] := by
      have w0 := Transcript.wordAt_write hm9' (r := 1) (o := 72) rfl (by omega)
        (v := .load 0 1280 8) (by decide +kernel)
      have w8 := Transcript.wordAt_write hm9' (r := 1) (o := 80) rfl (by omega)
        (v := .load 0 1288 8) (by decide +kernel)
      simp only [Sym.eval] at w0 w8
      rw [L0'] at w0
      rw [L8'] at w8
      exact ew_words w0 w8
    have hy2 : y.toList = [y.toList[0]'hy0, y.toList[1]'hy1'] := by
      apply List.ext_getElem (by rw [hyl, hs2]; rfl)
      intro i h1 _
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl
    simp only [PcOk, NativeRustcVmArm.Vm.GkrStep.b28_length, NativeRustcVmArm.Vm.GkrStep.b28Length, show k + NativeRustcVmArm.Vm.GkrStep.b28Offset + 3 = k + NativeRustcVmArm.Vm.GkrStep.b29Offset by simpa only [NativeRustcVmArm.Vm.GkrStep.b28_length, NativeRustcVmArm.Vm.GkrStep.b28Length, Nat.add_assoc] using congrArg (k + ·) NativeRustcVmArm.Vm.GkrStep.b28_next] at hpc9
    exact at_pc hpc9 (hcopy st9.data
      { fr := hfr9
        x19 := R9.x19
        x20 := R9.x20
        x23 := R9.x23
        size := hi.size
        ysize := hi.ysize
        vsize := rfl
        hxs := ews_p hm9' hwf9 (by decide +kernel) (o := 16) (by omega) kx8
        vals := vals _
          (out_p hm9' hwf9 (o := 0) (L := 16) (by omega) (by decide +kernel) (len16 _) V08)
          (out_p hm9' hwf9 (o := 16) (L := 16) (by omega) (by decide +kernel) (len16 _) V18)
          (out_p hm9' hwf9 (o := 32) (L := 16) (by omega) (by decide +kernel) (len16 _) V28)
        len := out_p hm9' hwf9 (o := 48) (L := 8) (by omega) (by decide +kernel)
          (by rw [NativeRustcVm.length_wordBytes]) hlen
        ys := by
          rw [hy2]
          exact ews_cons (out_p hm9' hwf9 (o := 56) (L := 16) (by omega) (by decide +kernel)
            (len16 _) Y0) Y1
        ts := ts_p h hm9' hwf9 (by decide +kernel) kt8
        run := hrun })

end

end NativeRustcVmArm.Bus.GkrStep
