module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Field.EWMul.Exec
public import NativeRustcVmArm.Field.Leaf
public import NativeRustcVmArm.Field.LinSound
public import NativeRustcVmArm.Field.RustSym
public import NativeRustcVm.Field.EW

/-!
# `EW::mul` on AArch64

`ewMul_spec_rust`: rustc's `EW::mul`, placed anywhere in the program, returns `Field.ewMul` of its
arguments' limbs (`NativeRustcVm.Field.Rust`) in X0, X1, using its 592-byte frame only and keeping
the callee-saved registers. rustc interleaves and shares the three carry-less products and the two
reductions; each result is the transcription's by `Lin.check` (`ewMul_val`). `ewMul_spec`: the
model's product (`NativeRustcVm.Field.ewMul_eq`).
-/

namespace NativeRustcVmArm.Field.EWMul

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.EWMul

public section

/-- The Karatsuba product of the argument registers, as a symbolic value. -/
@[expose] def rustS : Sym × Sym := ewMulS (.reg .X0) (.reg .X1) (.reg .X2) (.reg .X3)

/-- The block's X0 is the product's limb 0, by `Lin.check`. -/
theorem check_x0 : (match exec b0 (frameS 592) with
    | some (S, _) => (S.reg .X0).map fun v ↦ Lin.check 32 v rustS.1
    | none => none) = some true := by
  decide +kernel

/-- The block's X1 is the product's limb 1, by `Lin.check`. -/
theorem check_x1 : (match exec b0 (frameS 592) with
    | some (S, _) => (S.reg .X1).map fun v ↦ Lin.check 32 v rustS.2
    | none => none) = some true := by
  decide +kernel

theorem reg_of_check {r : XReg} {b : Sym} [Labels] {env : Env} {m : MachineData} {S' : SState}
    {x : Exit} (hrun : exec b0 (frameS 592) = some (S', x)) (hm : Match env S' m)
    (hc : (match exec b0 (frameS 592) with
      | some (S, _) => (S.reg r).map fun v ↦ Lin.check 32 v b
      | none => none) = some true) :
    (m.regs.getXReg r).toBitVec = b.eval env := by
  rw [hrun] at hc
  obtain ⟨v, hv, hcv⟩ := Option.map_eq_some_iff.mp hc
  rw [hm.regs r v hv]
  exact Lin.eval_eq_of_check hcv env

/-- The block's results in X0 and X1. -/
theorem ewMul_val [Labels] {env : Env} {m : MachineData} {S' : SState} {x : Exit}
    (hrun : exec b0 (frameS 592) = some (S', x)) (hm : Match env S' m) :
    (m.regs.getXReg .X0).toBitVec =
        (NativeRustcVm.Field.ewMul (env.regs .X0) (env.regs .X1) (env.regs .X2) (env.regs .X3)).1 ∧
      (m.regs.getXReg .X1).toBitVec =
        (NativeRustcVm.Field.ewMul (env.regs .X0) (env.regs .X1) (env.regs .X2)
          (env.regs .X3)).2 := by
  have he := eval_ewMulS env (.reg .X0) (.reg .X1) (.reg .X2) (.reg .X3)
  exact ⟨(reg_of_check hrun hm check_x0).trans (congrArg Prod.fst he),
    (reg_of_check hrun hm check_x1).trans (congrArg Prod.snd he)⟩

/-- `EW::mul`'s postcondition against the transcription. -/
@[expose] def RustPost (m m' : MachineData) : Prop :=
  (m'.regs.X0.toBitVec = (NativeRustcVm.Field.ewMul m.regs.X0.toBitVec m.regs.X1.toBitVec
      m.regs.X2.toBitVec m.regs.X3.toBitVec).1 ∧
    m'.regs.X1.toBitVec = (NativeRustcVm.Field.ewMul m.regs.X0.toBitVec m.regs.X1.toBitVec
      m.regs.X2.toBitVec m.regs.X3.toBitVec).2) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m ewMulStack) ewMulStack) ∧ Saved m m'

/-- **`EW::mul` computes `Field.ewMul`.** -/
theorem ewMul_spec_rust [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre RustPost := by
  have hk : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.EWMul.b0Offset) :=
    b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
  have hl : Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.EWMul.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.EWMul.entryOffset) NativeRustcVmArm.Vm.EWMul.entry_at
  refine leaf_spec (Q := fun m m' ↦
    m'.regs.X0.toBitVec = (NativeRustcVm.Field.ewMul m.regs.X0.toBitVec m.regs.X1.toBitVec
      m.regs.X2.toBitVec m.regs.X3.toBitVec).1 ∧
    m'.regs.X1.toBitVec = (NativeRustcVm.Field.ewMul m.regs.X0.toBitVec m.regs.X1.toBitVec
      m.regs.X2.toBitVec m.regs.X3.toBitVec).2) hk hl (by decide) run_b0 ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro m m' _ hm'
    have h := ewMul_val run_b0 hm'
    simp only [Env.ofMachine_regs] at h
    exact h

/-- **`EW::mul` computes the model's product.** -/
theorem ewMul_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost := by
  intro m hpre
  refine Eventually.mono (ewMul_spec_rust hp m hpre) fun st ⟨hpc, ⟨h0, h1⟩, hso, hsv⟩ ↦
    ⟨hpc, ?_, ?_, hso, hsv⟩
  · rw [NativeRustcVm.Field.ewMul_eq] at h0
    simp only [UInt64.ofBitVec_toBitVec] at h0
    exact UInt64.toBitVec_inj.mp h0
  · rw [NativeRustcVm.Field.ewMul_eq] at h1
    simp only [UInt64.ofBitVec_toBitVec] at h1
    exact UInt64.toBitVec_inj.mp h1

end

end NativeRustcVmArm.Field.EWMul
