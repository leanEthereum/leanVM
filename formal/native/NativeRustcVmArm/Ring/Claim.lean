module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Claim.Call

/-!
# `ring_claim_weight`'s contract

The prologue and `eq_eval_fn` (`b0`, `stepEntry`), `ring_weight` (`b1`, `stepWeight`), the
branch on its `Option<EW>` (`b2`, never taken: the tag is `1`), `EW::mul` (`b3`), the product
and the tag `1` stored and the epilogue (`b4`, `b5`).
-/

namespace NativeRustcVmArm.Ring.Claim

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Vm.RingClaimWeight NativeRustcVmArm.Whir NativeRustcVm.Ring

public section

variable {m0 : MachineData}

/-- **The end**: from a state of the frame and the block run to the return, the contract. -/
theorem post_of [Labels] (h : RingClaimWeightPre m0) {m st : MachineData} {S : SState}
    (hfr : CFr m0 m) (hm : Match (envR m0 m) S st) (hok : exitOk S 112 slots keep = true)
    (hout : outOnly S = true) {v : Option EW} (hv : OptEWAt st.dmem (oA m0) v)
    (hvv : v = some (StackWeight.eval (.ring (placementArg m0) (slice m0 m0.regs.X3 m0.regs.X4)
      (arr m0 m0.regs.X5 coeffCount)) (slice m0 m0.regs.X6 m0.regs.X7))) :
    retOf st = retOf m0 ∧ RingClaimWeightPost m0 st := by
  have hwf := envR_wf h hfr
  obtain ⟨hret, hS⟩ := hfr.exit hm hwf hok
  refine ⟨hret, hvv ▸ hv, ?_, hS⟩
  have h2 := outOnly_same hm hwf rfl hout
  intro q hq
  rw [h2 q fun h ↦ hq (.inl h)]
  exact hfr.same q fun h ↦ h.elim (fun h ↦ hq (.inr h)) id

theorem matchR [Labels] (h : RingClaimWeightPre m0) {m : MachineData} (hfr : CFr m0 m)
    (hx19 : m.regs.getXReg .X19 = m0.regs.X0) : Match (envR m0 m) retS m :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.1 (by decide) (by decide), rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval])
    ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [hx19]; simp [Sym.eval, oA], trivial⟩
    trivial trivial trivial

variable [Host] {k : Nat}

/-- **`ring_claim_weight`'s contract.** -/
theorem ringClaimWeight_spec (hp : Placed code k)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hrw : Spec (Labels.label NativeRustcVmArm.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.RingClaimWeight.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingClaimWeight.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingClaimWeight.entryOffset) NativeRustcVmArm.Vm.RingClaimWeight.entry_at]
  refine stepEntry hp h hee fun m1 hM1 ↦ stepWeight hp h hrw hM1 fun m2 hM ↦ ?_
  have hwf := envR_wf h hM.fr
  have hm := matchR h hM.fr hM.x19
  refine exec_then (hb b2_in_code (by simp [b2]) hp) run_b2 hwf hm fun st3 hm3 hpc3 ↦ ?_
  have hc : (SBool.cmp .eq .W64 (.load 0 8 8) (.lit 0)).eval (envR m0 m2) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64]
    rw [load_word (env := envR m0 m2) (r := 0) (off := 8) hM.w.1]
    rfl
  simp only [PcOk, hc, Bool.false_eq_true, ↓reduceIte] at hpc3
  rw [show k + NativeRustcVmArm.Vm.RingClaimWeight.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingClaimWeight.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingClaimWeight.b2_next]] at hpc3
  refine exec_at (hb b3_in_code (by simp [b3]) hp) run_b3 hwf hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
  have hfr4 : CFr m0 st4.data :=
    hM.fr.ofBlock hm hm4 hwf rfl rfl rfl fun r hr ↦ by
      simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
  have hw := NativeRustcVm.ewAt_iff.mp hM.w.2
  have hw0 : NativeRustcVm.WordAt m2.dmem (fb m0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8)
      (wOf m0).c0 := hw.1
  have hw1 : NativeRustcVm.WordAt m2.dmem
      (fb m0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8) (wOf m0).c1 := hw.2
  rw [NativeRustcVm.addr_add_add] at hw0
  rw [NativeRustcVm.addr_add_add, NativeRustcVm.addr_add_add] at hw1
  have e0 : st4.data.regs.X0 = (eqOf m0).c0 :=
    Column.reg_of hm4 (r := .X0) (v := .reg .X20) rfl (by simp [Sym.eval, hM.x20])
  have e1 : st4.data.regs.X1 = (eqOf m0).c1 :=
    Column.reg_of hm4 (r := .X1) (v := .reg .X21) rfl (by simp [Sym.eval, hM.x21])
  have e2 : st4.data.regs.X2 = (wOf m0).c0 :=
    Column.reg_of hm4 (r := .X2) (v := .load 0 16 8) rfl
      (by simp only [Sym.eval]; exact load_word (env := envR m0 m2) (r := 0) (off := 16) hw0)
  have e3 : st4.data.regs.X3 = (wOf m0).c1 :=
    Column.reg_of hm4 (r := .X3) (v := .load 0 24 8) rfl
      (by simp only [Sym.eval]; exact load_word (env := envR m0 m2) (r := 0) (off := 24) hw1)
  have hx19 : st4.data.regs.getXReg .X19 = m0.regs.X0 :=
    (Match.reg_eq hm hm4 (r := .X19) rfl rfl).trans hM.x19
  refine Fr.leafAt hfr4 (hN h) (N' := ewMulStack) (by decide) keep_cs slots_le
    (fun _ h ↦ h.elim) hmul hpc4 (hfr4.stackOk h.1 (by decide) (by decide))
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq ↦ .inl hq, hq.2.2.2⟩)
    fun m5 hfr5 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingClaimWeight.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingClaimWeight.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingClaimWeight.b3_next]]
  have hval : (⟨m5.regs.getXReg .X0, m5.regs.getXReg .X1⟩ : EW) = eqOf m0 * wOf m0 := by
    show (⟨m5.regs.X0, m5.regs.X1⟩ : EW) = _
    rw [hq.1, hq.2.1, e0, e1, e2, e3]
    rfl
  have hwf5 := envR_wf h hfr5
  have hm5 := matchR h hfr5 ((hcs .X19 rfl).trans hx19)
  refine exec_then (hb b4_in_code (by simp [b4]) hp) run_b4 hwf5 hm5 fun st6 hm6 hpc6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [show k + NativeRustcVmArm.Vm.RingClaimWeight.b4Offset + b4.length = k + NativeRustcVmArm.Vm.RingClaimWeight.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingClaimWeight.b4_next]] at hpc6
  refine exec_at (hb b5_in_code (by simp [b5]) hp) run_b5 hwf5 hpc6 hm6 fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨hret, hpost⟩ := post_of h hfr5 hm7 (by decide) (by decide)
    (outSome_at hm7 rfl (by decide)) (by rw [hval]; rfl)
  exact .done _ ⟨by simp only [PcOk] at hpc7; rw [hpc7, hret], hpost⟩

end

end NativeRustcVmArm.Ring.Claim
