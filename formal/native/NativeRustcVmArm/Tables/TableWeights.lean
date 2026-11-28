module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.TableWeights.Names
public import NativeRustcVmArm.Tables.TableWeights.Entry

/-!
# `table_weights` meets its contract

The entry (`entry_step`) into the loop (`loop_spec`) or, for an empty point, straight to the exit;
the exit (`exit_step`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym

public section

variable [Host] {k : Nat}

/-- **`table_weights` meets its contract.** -/
theorem table_weights_spec (hp : Placed Vm.TableWeights.code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost := by
  intro m0 hpre
  have hc := ctx_of hpre
  rw [lbl_entry hp]
  refine Eventually.bind (entry_step hp hc) fun ⟨d, pc⟩ h => ?_
  rcases h with ⟨hpc, hit⟩ | ⟨hpc, hfin⟩
  · simp only at hpc
    subst hpc
    exact Eventually.bind (loop_spec hp hc hmul hit) fun ⟨d', pc'⟩ ⟨hpc', hfin⟩ => by
      simp only at hpc'
      subst hpc'
      exact exit_step hp hc hfin
  · simp only at hpc
    subst hpc
    exact exit_step hp hc hfin

end

end NativeRustcVmArm.Tables.TableWeights
