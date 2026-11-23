module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Field.Kmul.Exec
public import NativeRustcVmArm.Field.Leaf
public import NativeRustcVmArm.Field.Norm
public import NativeRustcVm.Field.Clmul

/-!
# `kmul` on AArch64

`kmul_spec_rust`: rustc's `kmul`, placed anywhere in the program, returns `Field.kmul a b`
(`NativeRustcVm.Field.Rust`, `field.rs` transcribed) of its arguments, using its 112-byte frame
only and keeping the callee-saved registers. Its one block's result is the transcription up to the
order of `xor`s, `or`s and products (`kmul_val`). `kmul_spec`: the model's product
(`NativeRustcVm.Field.kmul_toBitVec`).
-/

namespace NativeRustcVmArm.Field.Kmul

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kmul

public section

/-- The block's result in X0. -/
theorem kmul_val [Labels] {env : Env} {m : MachineData} {S' : SState} {x : Exit}
    (hrun : exec b0 (frameS 112) = some (S', x)) (hm : Match env S' m) :
    (m.regs.getXReg .X0).toBitVec = NativeRustcVm.Field.kmul (env.regs .X0) (env.regs .X1) := by
  rw [run_b0] at hrun
  cases hrun
  have h := hm.regs .X0 _ rfl
  field_ops at h
  rw [h]
  refine kmul_of ?_ ?_
  · simp only [NativeRustcVm.Field.clmulLow]
    ac_rfl
  · simp only [NativeRustcVm.Field.clmulLow]
    congr 1
    ac_rfl

/-- `kmul`'s postcondition against the transcription. -/
@[expose] def RustPost (m m' : MachineData) : Prop :=
  m'.regs.X0.toBitVec = NativeRustcVm.Field.kmul m.regs.X0.toBitVec m.regs.X1.toBitVec ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m kmulStack) kmulStack) ∧ Saved m m'

/-- **`kmul` computes `Field.kmul`.** -/
theorem kmul_spec_rust [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre RustPost := by
  have hk : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.Kmul.b0Offset) :=
    b0_in_code.trans hp.1 (by rw [b0]; exact List.cons_ne_nil _ _)
  have hl : Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Kmul.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.Kmul.entryOffset) NativeRustcVmArm.Vm.Kmul.entry_at
  refine leaf_spec (Q := fun m m' ↦ m'.regs.X0.toBitVec =
    NativeRustcVm.Field.kmul m.regs.X0.toBitVec m.regs.X1.toBitVec) hk hl (by decide) run_b0
    ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro m m' _ hm'
    have h := kmul_val run_b0 hm'
    rw [Env.ofMachine_regs, Env.ofMachine_regs] at h
    exact h

/-- **`kmul` computes the model's product.** -/
theorem kmul_spec [Host] {k : Nat} (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost := by
  intro m hpre
  refine Eventually.mono (kmul_spec_rust hp m hpre) fun st ⟨hpc, h0, hso, hsv⟩ ↦
    ⟨hpc, ?_, hso, hsv⟩
  rw [NativeRustcVm.Field.kmul_toBitVec] at h0
  exact UInt64.toBitVec_inj.mp h0

end

end NativeRustcVmArm.Field.Kmul
