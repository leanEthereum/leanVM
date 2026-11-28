module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.SlotWeights.Names
public import NativeRustcVmArm.KeccakGkr.SlotWeights.Zero
public import NativeRustcVmArm.KeccakGkr.SlotWeights.Tail

/-!
# `slot_weights` meets its contract

The prologue and `eq_kernel` (`prologue`), the rows zeroed (`zero_loop`), the first segment's
loop (`to_segA`, `segA_loop`), the second's when the count is `2` (`after_segA`, `segB_loop`), the
epilogue (`epilogue`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights

public section

variable [NativeRustcArm.Host] {k : Nat}

/-- **`slot_weights` meets its contract**, given `eq_kernel`'s and `EW::mul`'s. -/
theorem slotWeights_spec (hp : Placed code k)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (c : KeccakClaimW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c) := by
  intro m0 hpre
  have hl : Labels.label NativeRustcVmArm.Vm.SlotWeights.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.SlotWeights.entryOffset) NativeRustcVmArm.Vm.SlotWeights.entry_at
  rw [hl]
  refine (prologue hp hpre heq).bind fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine (zero_loop hp hpre hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine (to_segA hp hpre hpc2 hI2).bind fun s3 ⟨hpc3, hI3⟩ ↦ ?_
  refine (segA_loop hp hpre hmul hpc3 hI3).bind fun s4 ⟨hpc4, hI4⟩ ↦ ?_
  refine (after_segA hp hpre hpc4 hI4).bind fun s5 h5 ↦ ?_
  rcases h5 with ⟨hpc5, hE⟩ | ⟨hpc5, hc2, hI5⟩
  · exact epilogue hp hpre hpc5 hE
  · refine (segB_loop hp hpre hmul hpc5 hI5).bind fun s6 ⟨hpc6, hb6, hx6, hr6⟩ ↦ ?_
    refine epilogue hp hpre hpc6 ⟨hb6, hx6, ?_⟩
    rw [show 1600 * (m0.regs.X4.toNat + m0.regs.X5.toNat) = 3200 by
      have := hI5.first0
      omega]
    exact hr6

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
