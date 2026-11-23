module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Weight.Outer

/-!
# `ring_weight`: the coefficients' loop, `r'` empty

Every product is its coefficient: each turn (`ZerI`) loads it into X19, X25 (`b22`), squares the
powers (`sqLoop` over `b23`, `b24`) and adds it to the total (`b25`); after the last, the
epilogue. `b21` starts it.
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight
open NativeRustcVmArm.Arrays (calleeRegs regs_eq_of)

@[expose] public section

/-- **The coefficients' loop, turn `k`** (`r'` empty). -/
structure ZerI (m0 : MachineData) (k : Nat) (m : MachineData) : Prop where
  fr : WFr m0 m
  lt : k < 64
  x20 : m.regs.getXReg .X20 = m0.regs.X5
  x22 : (m.regs.getXReg .X22).toBitVec = slotA m0 (nR m0)
  x24 : (m.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (16 * k)
  tot : (⟨m.regs.getXReg .X21, m.regs.getXReg .X23⟩ : EW) = (A m0 k).1
  pow : PowP m0 m.dmem (A m0 k).2

end

public section

variable {m0 : MachineData}

theorem qL_nil (h0 : nQ m0 = 0) : qL m0 = #[] := by
  simp [slice, NativeRustcVm.ewsOf, h0]

variable [Host] {k : Nat}

/-- **A turn** (`b22` to `b25`). -/
theorem zerTurn (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {j : Nat} {m : MachineData}
    (hI : ZerI m0 j m) (hQ : nQ m0 = 0) (hR : 0 < nR m0) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b22Offset) ∧ ∃ j',
        ZerI m0 j' st.data ∧ 64 - j' < 64 - j) ∨
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) ∧ Done m0 st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b22Offset)⟩ := by
  have hj := hI.lt
  -- `b22`
  have hwf := coef_wf h hI.fr hj
  have hm := coef_match (m := m) (r := .X24) (k := j) (by rw [hI.x20, hI.x24])
  refine exec_then (hb b22_in_code (by simp [b22]) hp) run_b22 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  refine at_pc hpc1 ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b22Offset + b22.length = k + NativeRustcVmArm.Vm.RingWeight.b23Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b22_next]]
  have hfr1 : WFr m0 st1.data := hI.fr.ofBlock hm hm1 hwf rfl rfl rfl fun r hr ↦ by simp at hr
  have hce := coef_ew h hI.fr hj
  have k1 := regs_eq_of hm hm1 [.X20, .X21, .X22, .X23, .X24] (by decide)
  have hsI : SqI m0 .X26 (A m0 j).2 st1.data 0 st1.data := by
    refine ⟨hfr1, hR, ?_, fun _ _ _ ↦ rfl, fun _ h ↦ absurd h (by omega), fun l _ hl ↦ ?_⟩
    · refine reg_bv hm1 rfl ?_
      simp only [Sym.eval, add_bv]
      show m.regs.SP.toBitVec + _ = _
      rw [hI.fr.sp]
    · rw [hm1.dmem_eq hwf rfl]; exact hI.pow l hl
  have h22 : (st1.data.regs.getXReg .X22).toBitVec = slotA m0 (nR m0) := by
    rw [k1 .X22 (by simp)]; exact hI.x22
  refine (sqLoop h hmul rfl h22 (by decide) (hb b23_in_code (by simp [b23]) hp) run_b23
    (by decide) (show k + NativeRustcVmArm.Vm.RingWeight.b23Offset + b23.length = k + NativeRustcVmArm.Vm.RingWeight.b24Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b23_next]) (hb b24_in_code (by simp [b24]) hp)
    run_b24 (by decide) (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b23Offset) NativeRustcVmArm.Vm.RingWeight.label_20_at) hsI).bind fun st4 ⟨hpc4, hS⟩ ↦ at_pc hpc4 ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b24Offset + b24.length = k + NativeRustcVmArm.Vm.RingWeight.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b24_next]]
  -- `b25`
  refine exec_then (hb b25_in_code (by simp [b25]) hp) run_b25 (Env.wf_nil _) (match_nil _)
    fun st5 hm5 hpc5 ↦ ?_
  have hfr5 := regs_fr hS.fr hm5 rfl rfl
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq (Env.wf_nil _) rfl
  have hS' : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25],
      st4.data.regs.getXReg r = st1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hS.regs _ (by simp [calleeRegs]) (by simp)
  have k5 := regs_eq_of (match_nil _) hm5 [.X20, .X22] (by decide)
  have hc0 : st4.data.regs.getXReg .X19 = ((cL m0).getD j 0).c0 := by
    rw [hS' .X19 (by simp)]; exact reg_of hm1 rfl hce.1
  have hc1 : st4.data.regs.getXReg .X25 = ((cL m0).getD j 0).c1 := by
    rw [hS' .X25 (by simp)]; exact reg_of hm1 rfl hce.2
  have hA := A_succ (m0 := m0) hj
  have htot' : (⟨st5.data.regs.getXReg .X21, st5.data.regs.getXReg .X23⟩ : EW) = (A m0 (j + 1)).1 := by
    have x21 : st5.data.regs.getXReg .X21 =
        st4.data.regs.getXReg .X19 ^^^ st4.data.regs.getXReg .X21 :=
      reg_of hm5 rfl (eor_eval (a := st4.data.regs.getXReg .X19)
        (b := st4.data.regs.getXReg .X21) rfl rfl)
    have x23 : st5.data.regs.getXReg .X23 =
        st4.data.regs.getXReg .X25 ^^^ st4.data.regs.getXReg .X23 :=
      reg_of hm5 rfl (eor_eval (a := st4.data.regs.getXReg .X25)
        (b := st4.data.regs.getXReg .X23) rfl rfl)
    have e3 := congrArg EW.c0 hI.tot
    have e4 := congrArg EW.c1 hI.tot
    simp only at e3 e4
    rw [hA, x21, x23, hc0, hc1, hS' .X21 (by simp), hS' .X23 (by simp), k1 .X21 (by simp),
      k1 .X23 (by simp), e3, e4, tot_step]
    show _ = (A m0 j).1 + prodOf (A m0 j).2 (qL m0) ((cL m0).getD j 0)
    rw [qL_nil hQ, prodOf_nil]
  have hpow' : PowP m0 st5.data.dmem (A m0 (j + 1)).2 := fun l hl ↦ by
    rw [hd5, hA]
    show NativeRustcVm.EWAt _ _ (((A m0 j).2.map fun v ↦ v * v).getD l 0)
    rw [getD_map_sq (by rw [size_A]; exact hl)]
    exact hS.sq l hl
  have h24 : (st5.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (16 * (j + 1)) := by
    refine reg_bv hm5 rfl ?_
    simp only [Sym.eval, add_bv, Env.ofMachine_regs]
    rw [hS' .X24 (by simp), k1 .X24 (by simp), hI.x24]
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  simp only [PcOk] at hpc5
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc5
  have he : (SBool.not (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X24) (.lit 16)) (.lit 1024))).eval
      (Env.ofMachine st4.data []) = true ↔ j + 1 ≠ 64 := by
    have : (Sym.bin .add .W64 (.reg .X24) (.lit 16)).eval (Env.ofMachine st4.data []) =
        BitVec.ofNat 64 (16 * (j + 1)) := by
      rw [← h24]; exact (reg_bv hm5 rfl rfl).symm
    simp only [SBool.eval, CmpOp.apply, Sym.low_W64, Bool.not_eq_true', Bool.eq_false_iff, ne_eq]
    rw [this]
    simp only [Sym.eval]
    rw [eq_lit (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hreg : ∀ r ∈ [XReg.X20, .X22], st5.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [k5 _ (by simp), hS' _ (by simp), k1 _ (by simp)]
  by_cases hl : j + 1 = 64
  · refine .done _ (.inr ⟨(hc.2 (fun e ↦ he.mp e hl)).trans (show Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b25Offset + b25.length) =
      Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) from rfl), hfr5, ?_⟩)
    rw [htot', A_done, hl]
  · refine .done _ (.inl ⟨(hc.1 (he.mpr hl)).trans (hp.label (j := NativeRustcVmArm.Vm.RingWeight.b22Offset) NativeRustcVmArm.Vm.RingWeight.label_19_at), j + 1,
      ⟨hfr5, by omega, by rw [hreg .X20 (by simp)]; exact hI.x20,
        by rw [hreg .X22 (by simp)]; exact hI.x22, h24, htot', hpow'⟩, by omega⟩)

end

end NativeRustcVmArm.Ring.Weight
