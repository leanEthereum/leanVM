module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry2
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExitNone
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.ExitSome
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Fold
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names

/-!
# `keccak_open` meets its x86-64 contract

The prologue calls the plain sumcheck. Failure returns tag zero; success computes the slot
weights, folds all six rounds in place, writes the value and tag, and restores the System V
callee-saved registers and return stack pointer. The proof assumes only the four callees'
contracts, not a fold or execution oracle.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen

public section

/-- The complete machine-code contract, given the four callee contracts. -/
theorem keccakOpen_spec [Host] {k : Nat} (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hsw : ∀ c, Spec (Labels.label NativeRustcVmX64.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s)) :
    ∀ a s c, Spec (Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c) := by
  intro a s c m0 hpre
  have h := preOk hpre
  rw [show Labels.label NativeRustcVmX64.Vm.KeccakOpen.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakOpen.b0Offset) from hp.label NativeRustcVmX64.Vm.KeccakOpen.entry_at]
  refine (sc_run hp h hsc).bind fun st ⟨hpc, hs⟩ ↦ ?_
  cases hr : scRun s m0 with
  | none => exact none_exit hp h hpc hs hr
  | some r =>
    obtain ⟨⟨sl, v⟩, s1⟩ := r
    obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size (reg m0 .rdx).toNat c
      (openFirst m0).toNat (openCount m0).toNat
    refine (sw_run hp h hsw hpc hs hr).bind fun st ⟨hpc, hs⟩ ↦ ?_
    refine (fold_start hp h hpc hs).bind fun st ⟨hpc, hm, hk, hrows⟩ ↦ ?_
    refine (fold_run hp hmul hmemcpy h rfl hsz hrow hpc hm hk hrows).bind
      fun st ⟨hpc, hm, hrows⟩ ↦ ?_
    exact some_exit hp h hr hpc hm hrows

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
