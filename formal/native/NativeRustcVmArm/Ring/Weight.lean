module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Weight.Start
public import NativeRustcVmArm.Ring.Weight.Sum

/-!
# `ring_weight`'s contract

The prologue (`b0`) zeroes the 36 powers and branches on `|r|`: with `r` empty the result is the
coefficients' sum (`b2` to `b4`); else `r` is copied into the powers (`b5` to `b10`) and each of
the 64 coefficients' products is added to the total, the powers squared after it, with `r'` not
empty (`b11` to `b20`) or empty (`b21` to `b25`); the epilogue (`b26`) stores `some` total.
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

public section

variable [Host] {k : Nat}

/-- **`ring_weight`'s contract.** -/
theorem ringWeight_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.entryOffset) NativeRustcVmArm.Vm.RingWeight.entry_at]
  have toExit : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) ∧ Done m0 st.data →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingWeightPost m0 st.data) st :=
    fun st ⟨hpc, hD⟩ ↦ at_pc hpc (stepExit hp h hD)
  have loops : ∀ m, Copied m0 m → 0 < nR m0 →
      Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingWeightPost m0 st.data)
        ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset)⟩ :=
    fun m hC hR ↦ (stepLoops hp h hmul hC hR).bind toExit
  refine stepEntry hp h fun st hB hpc ↦ ?_
  by_cases h1 : nR m0 = 1
  · rw [ite_eq_left h1] at hpc
    refine at_pc hpc ?_
    have := stepCopy hp h hB (by omega) fun m hC ↦ loops m hC (by omega)
    rwa [ite_eq_left h1] at this
  · rw [ite_eq_right h1] at hpc
    refine at_pc hpc (stepB1 hp hB fun st2 hB2 hpc2 ↦ ?_)
    by_cases h0 : nR m0 = 0
    · rw [ite_eq_left h0] at hpc2
      exact at_pc hpc2 (stepSum hp h hB2 h0 fun m hD ↦ stepExit hp h hD)
    · rw [ite_eq_right h0] at hpc2
      refine at_pc hpc2 ?_
      have := stepCopy hp h hB2 (by omega) fun m hC ↦ loops m hC (by omega)
      rwa [ite_eq_right h1] at this

end

end NativeRustcVmArm.Ring.Weight
