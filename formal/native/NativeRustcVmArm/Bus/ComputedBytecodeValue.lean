module

public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmArm.Bus.ComputedBytecodeValue.Exec
public import NativeRustcVmArm.Bus.Common

/-!
# `computed_bytecode_value`

`b0` saves X30, X20, X19 in its 32-byte frame, keeps the value in X20, X19 and calls
`multilinear_eval_by` on the words and the point; `b1` compares the result with the value
(`cset`) and returns (`computedBytecodeValue_spec`).
-/

namespace NativeRustcVmArm.Bus.ComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ComputedBytecodeValue
open NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVmArm.Layout (infix_of)

public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) := [(0, .X30), (16, .X20), (24, .X19)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 32 := by decide

variable [Host] {k : Nat}

/-- **`computed_bytecode_value`'s contract.** -/
theorem computedBytecodeValue_spec (hp : Placed code k)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel) MleOfComputedBytecodeValuePre
      MleOfComputedBytecodeValuePost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost := by
  rintro m0 ⟨hS, hwr, hwo, hpt⟩
  have hN : computedBytecodeValueStack ≤ m0.regs.SP.toNat := hS.2.1
  have hNval : computedBytecodeValueStack = 32 + mleStack := rfl
  have hwf := Bus.wf_env0 hS (F := 32) (by rw [hNval]; omega)
  have hm : Match (Bus.env0 m0 32) entryS m0 :=
    Bus.match_entry hS (by rw [hNval]; omega) rfl
  rw [show Labels.label NativeRustcVmArm.Vm.ComputedBytecodeValue.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ComputedBytecodeValue.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.ComputedBytecodeValue.entryOffset) NativeRustcVmArm.Vm.ComputedBytecodeValue.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr : Fr m0 32 computedBytecodeValueStack slots keep (fun _ ↦ False) st.data :=
    Fr.ofPrologue hN (by rw [hNval]; omega) hm1 hwf rfl (by decide) slots_le
      (by decide) (by decide)
  have hreg : ∀ r v, (Bus.after b0 entryS).reg r = some v →
      (st.data.regs.getXReg r).toBitVec = v.eval (Bus.env0 m0 32) := fun r v h ↦
    hm1.regs r v (by rw [← Bus.after_eq run_b0]; exact h)
  have hx0 := hreg .X0 _ rfl
  have hx1 := hreg .X1 _ rfl
  have hx2 := hreg .X2 _ rfl
  have hx3 := hreg .X3 _ rfl
  have hx4 := hreg .X4 _ rfl
  have hx20 := hreg .X20 _ rfl
  have hx19 := hreg .X19 _ rfl
  have e0 : st.data.regs.X0 = m0.regs.X1 := UInt64.toBitVec_inj.mp hx0
  have e1 : st.data.regs.X1 = m0.regs.X0 := UInt64.toBitVec_inj.mp hx1
  have e2 : st.data.regs.X2 = m0.regs.X1 := UInt64.toBitVec_inj.mp hx2
  have e3 : st.data.regs.X3 = m0.regs.X2 := UInt64.toBitVec_inj.mp hx3
  have e4 : st.data.regs.X4 = m0.regs.X3 := UInt64.toBitVec_inj.mp hx4
  have e20 : st.data.regs.getXReg .X20 = m0.regs.X4 := UInt64.toBitVec_inj.mp hx20
  have e19 : st.data.regs.getXReg .X19 = m0.regs.X5 := UInt64.toBitVec_inj.mp hx19
  have hle : 32 + mleStack ≤ computedBytecodeValueStack := le_of_eq hNval.symm
  have hpre : MleOfComputedBytecodeValuePre st.data := by
    refine ⟨hfr.stackOk hS rfl hle, by rw [e0, e2], ?_, ?_, ?_⟩
    · rw [e1, e2]; exact Bus.Fr.readable hfr hwr
    · rw [e1, e2]; exact fun h ↦ Bus.Fr.offStack hfr hS (hwo h) hle
    · rw [e3, e4]
      exact ⟨Bus.Fr.readable hfr hpt.1, Bus.Fr.offStack hfr hS hpt.2 hle⟩
  refine Fr.leaf hfr hN hle keep_callee slots_le (fun _ h ↦ h.elim) hmle
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ hq'.elim
      (fun h ↦ (Bus.not_inRange_zero _ _ h).elim) .inl, hq.2.2⟩) hpc hpre
    fun m2 hfr2 hq2 hcs ↦ ?_
  -- After the call: `b1`.
  have hwf2 := Bus.wf_frame (F := 32) hS (by rw [hNval]; omega) hfr2.kept
  have hm2 : Match (Env.ofMachine m2 [(base m0 32, 32)]) retS m2 :=
    Bus.match_frame hS (by rw [hNval]; omega) rfl hfr2.sp
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2 rfl hm2 fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr2.exit hm3 hwf2 (by decide)
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  refine .done _ ⟨by simp only [PcOk] at hpc3; rw [hpc3, hret], ?_, ?_, hsaved⟩
  · -- The result.
    have hx0' := hm3.regs .X0 _ rfl
    have hres := hq2.1
    have hw : wordSliceE st.data st.data.regs.X1 st.data.regs.X2 =
        wordSliceE m0 m0.regs.X0 m0.regs.X1 := by
      unfold wordSliceE
      rw [e1, e2]
      by_cases h0 : m0.regs.X1.toNat = 0
      · simp only [h0, NativeRustcVm.wordsOf, List.range_zero, List.map_nil]
      · rw [Bus.Fr.wordsOf_eq hfr hS hwr.2 (hwo (by omega)) fun _ _ h ↦ h]
    have hs : slice st.data st.data.regs.X3 st.data.regs.X4 = slice m0 m0.regs.X2 m0.regs.X3 := by
      rw [e3, e4]; exact Bus.Fr.slice_eq hfr hS hpt fun _ _ h ↦ h
    rw [hw, hs] at hres
    have h20 : m2.regs.getXReg .X20 = m0.regs.X4 := (hcs .X20 rfl).trans e20
    have h19 : m2.regs.getXReg .X19 = m0.regs.X5 := (hcs .X19 rfl).trans e19
    apply UInt64.toBitVec_inj.mp
    show (st3.data.regs.getXReg .X0).toBitVec = _
    rw [hx0']
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs, h20, h19]
    rw [← hres]
    exact Bus.cset_ew (ewRet m2) (ewArg m0.regs.X4 m0.regs.X5)
  · intro p hp
    rw [hd3]
    exact Bus.Fr.changes hfr2 (fun _ h ↦ h.elim) p hp

end

end NativeRustcVmArm.Bus.ComputedBytecodeValue
