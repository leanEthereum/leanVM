module

public import NativeRustcVmX64.Whir.BasisWEval.Tail
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names

/-!
# `BasisW::eval` on x86-64

The prologue pushes the callee-saved registers, keeps the output's address, the point and the
layout's address in the 160-byte frame and calls `LayoutW::placement` on `QKECCAK`, then takes
the first scale (`entry`); `ring_claim_weight`, its two stack arguments the point, gives the
ring-switched claim's weight (`ring_call`), times the first scale (`first`); the column claims'
loop adds each placed claim's `column_weight` (`Some`: at most 36 coordinates and a stack of log
at most 30 fit its 66 slots) times its scale (`loop_run`); the out-of-domain claim's `eq_eval`
times its scale ends the sum, stored as `Some` at the output (`ood_scale`, `finish`). The sum is
`BasisW.eval` (`In.eval_eq`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeVm.Model NativeRustcVm.Whir NativeRustcVmX64.Vm.BasisWEval

public section

variable [Host] {k : Nat}

/-- **`BasisW::eval`'s contract.** -/
theorem basisWEval_spec (hp : Placed code k)
    (hpl : ∀ L, Spec (Labels.label NativeRustcVmX64.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hrcw : Spec (Labels.label NativeRustcVmX64.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost)
    (hcw : Spec (Labels.label NativeRustcVmX64.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (ba : BasisAddrs) (b : BasisW) :
    Spec (Labels.label NativeRustcVmX64.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b) := by
  intro m0 hpre
  obtain ⟨v, h⟩ := in_of_pre hpre
  rw [show Labels.label NativeRustcVmX64.Vm.BasisWEval.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b0Offset) from hp.label NativeRustcVmX64.Vm.BasisWEval.entry_at]
  have hend : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BasisWEval.b21Offset) → End m0 ba b v st.data →
      Eventually (step1 Host.exe) (Goal m0 b) st :=
    fun st hpc he ↦ ood_scale hp h hpc he fun st' hpc' ha ↦ finish hp h heq hmul hpc' ha
  exact entry hp h hpl fun st hpc ha ↦ ring_call hp h hrcw hpc ha fun st' hpc' ha' ↦
    first hp h hmul hpc' ha' (fun st'' hpc'' hm ↦ loop_run hp h hcw hmul hend rfl hpc'' hm) hend

end

end NativeRustcVmX64.Whir.BasisWEval

/-- info: 'NativeRustcVmX64.Whir.BasisWEval.basisWEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.BasisWEval.basisWEval_spec
