module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.SomeTail

/-!
# `sumcheck_round_poly` in equality mode, after `read_scalars`

At `.L2` (`b2`): a rejection, or the tail's sum (`sum_e`, `b3`), then `some_b4`.
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

public section

variable [Host] {a : DecArea} {s : TState} {ev : EW} {m0 : MachineData} {k : Nat}

/-- **After `read_scalars`**, at `b2`: the tail's sum, or a rejection. -/
theorem some_b2 (hp : Placed code k)
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hpre : RoundPolyPre a s (some ev) m0) {m : MachineData}
    (hf : RFrame m0 m) (hg : SomeRegs m0 ev m)
    (hx0 : m.regs.X0 = okWord ((readScalars (cnt m0 - 1)).run s).isSome)
    (htail : ∀ tail s1, (readScalars (cnt m0 - 1)).run s = some (tail, s1) →
      NativeRustcVm.EWsAt m.dmem (msgAt m0 + BitVec.ofNat 64 16) tail.toList ∧
        TStateAt m.dmem (tAt m0) a s1) :
    Eventually (step1 Host.exe)
      (fun st ↦ st.pc = retOf m0 ∧ RoundPolyPost a s (some ev) m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b2Offset)⟩ := by
  have hc2 : 2 ≤ cnt m0 := hpre.2.2.2.2.1
  have hc5 : cnt m0 ≤ maxCount := hpre.2.2.2.2.2.1
  have hmc : maxCount = 5 := rfl
  have hwf := wf_envB hpre hf
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b2Offset) := b2_in_code.trans hp.1 (by simp [b2])
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b3Offset) := b3_in_code.trans hp.1 (by simp [b3])
  have hl8 : Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) :=
    hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.label_8_at
  refine exec_then hk2 run_b2 hwf (match_bodyS hpre hf hg.x19) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hf2, -⟩ := RFrame.of_block hpre hf hm2 rfl rfl rfl rfl
  have hm2' : Match (envB m0 m) (after b2 bodyS) st2.data := by rw [after_eq run_b2]; exact hm2
  have hX0 : (envB m0 m).regs .X0 = m.regs.X0.toBitVec := rfl
  simp only [PcOk, SBool.eval, Sym.eval, hX0, getLsbD_low_zero] at hpc2
  cases hr1 : (readScalars (cnt m0 - 1)).run s with
  | none =>
    rw [hr1] at hx0
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b18Offset) := by
      rw [hpc2, hx0]; simp [okWord, hl8]
    obtain ⟨d2, pc2⟩ := st2
    simp only at hpc
    subst hpc
    refine Eventually.mono (fail_spec hp hpre hf2) fun st ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, ?_⟩
    refine post_none ?_ h2 (h3 ▸ hf2.same) h4
    simp [runR, roundPoly_some_run, hr1]
  | some p =>
    obtain ⟨tail, s1⟩ := p
    rw [hr1] at hx0
    obtain ⟨htl, hts⟩ := htail tail s1 hr1
    have hsz : tail.size = cnt m0 - 1 := readScalars_size hr1
    have hpc : st2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b3Offset) := by
      rw [hpc2, hx0]; simp [okWord]; rfl
    refine exec_at hk3 run_b3 hwf hpc hm2' fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hf3, hd3⟩ := RFrame.of_block hpre hf hm3 rfl rfl rfl rfl
    have hg3 := hg.of_block hm3 rfl rfl rfl rfl rfl rfl rfl
    have ht3 : TailAt m0 a tail s1 st3.data := ⟨hf3, hd3 ▸ htl, hd3 ▸ hts⟩
    have h30 : st3.data.regs.X0.toBitVec = msgAt m0 + BitVec.ofNat 64 16 :=
      reg_msg (r := .X0) (o := 16) hm3 rfl
    have h31 : st3.data.regs.X1.toNat = cnt m0 - 1 := by
      rw [show st3.data.regs.X1 = st3.data.regs.getXReg .X1 from rfl,
        reg_of_match' (r := .X1) (r' := .X27) hm3 rfl]
      exact hg.x27
    have ho := msgOk hpre
    rw [hmc] at ho
    refine call_then hpc3 hsum ?pre fun st4 hpc4 hpost4 ↦ ?_
    case pre =>
      have hr : Readable st3.data st3.data.regs.X0.toBitVec (16 * st3.data.regs.X1.toNat) := by
        rw [h30, h31]
        exact ⟨NativeRustcVm.Mapped.sub (fun i hi ↦ hf3.at_.kept _ (ho.1 i hi)) (by omega),
          NativeRustcVm.NoWrap.sub ho.2.1 (by omega)⟩
      exact ⟨by rw [h31]; omega, hr⟩
    obtain ⟨hsumv, hs4, hsv4⟩ := hpost4
    have hsl : slice st3.data st3.data.regs.X0 st3.data.regs.X1 = tail := by
      unfold slice
      rw [show st3.data.regs.X1.toNat = tail.toList.length by simp [h31, hsz], h30,
        NativeRustcVm.ewsOf_of_ewsAt ht3.tail]
    rw [hsl] at hsumv
    have ht4 := ht3.of_call hpre (by omega) (Nc := sumEStack) (by decide)
      (fun p hp ↦ hs4 p fun h ↦ h.elim (fun h' ↦ Nat.not_lt_zero _ h') hp) hsv4
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    subst hpc4
    exact some_b4 hp hbl hgr hmul hpre hr1 (hg3.of_saved hsv4) ht4
      (congrArg EW.c0 hsumv) (congrArg EW.c1 hsumv)

end

end NativeRustcVmArm.Sumcheck.RoundPoly
