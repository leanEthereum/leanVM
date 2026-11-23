module

public import NativeRustcVmArm.Code.Vm.BasisWEval.Names
public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmArm.Whir.BasisWEval.Tail

/-!
# `BasisW::eval`

The prologue saves the registers, calls `LayoutW::placement` on `QKECCAK` and takes the first
scale (`entry`); `ring_claim_weight` gives the ring-switched claim's weight (`ring_call`), times
the first scale (`first`); the column claims' loop adds each placed claim's `column_weight` times
its scale (`loop_run`); the out-of-domain claim's `eq_eval` times its scale ends the sum, stored
as `Some` at the output (`ood_scale`, `finish`). The sum is `BasisW.eval` (`eval_eq`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVm.Whir NativeRustcVmArm.Vm.BasisWEval

public section

variable [Host] {k : Nat}

/-- **`BasisW::eval`'s contract.** -/
theorem basisWEval_spec (hp : Placed code k)
    (hpl : ∀ L, Spec (label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hrcw : Spec (label NativeRustcVmArm.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost)
    (hcw : Spec (label NativeRustcVmArm.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (heq : Spec (label NativeRustcVmArm.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (ba : BasisAddrs) (b : BasisW) :
    Spec (label NativeRustcVmArm.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b) := by
  intro m0 hpre
  obtain ⟨v, h⟩ := in_of_pre hpre
  rw [show Labels.label NativeRustcVmArm.Vm.BasisWEval.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.BasisWEval.entryOffset) NativeRustcVmArm.Vm.BasisWEval.entry_at]
  have hend : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b19Offset) → End m0 ba b v st.data →
      Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ BasisWEvalPost b m0 s.data) st :=
    fun st hpc he ↦ ood_scale hp h hpc he fun st' hpc' ha ↦ finish hp h heq hmul hpc' ha
  exact entry hp h hpl fun st hpc ha ↦ ring_call hp h hrcw hpc ha fun st' hpc' hw hf hcs ↦
    first hp h hmul ha hpc' hw hf hcs
      (fun st'' hpc'' hl ↦ loop_run hp h hcw hmul hend rfl hpc'' hl) hend

end

end NativeRustcVmArm.Whir.BasisWEval
