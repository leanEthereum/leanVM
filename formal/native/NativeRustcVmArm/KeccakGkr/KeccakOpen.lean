module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.SlotWeights.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Entry2
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.ExitSome
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Fold

/-!
# `keccak_open` meets its contract

The prologue and the plain sumcheck (`sc_run`); on `None` the return with tag `0`
(`none_exit`); else `slot_weights` into the rows (`sw_run`), the fold's start (`fold_start`), the
six rounds of the in-place fold (`fold_run`), the value written and the return with tag `1`
(`some_exit`) (`keccakOpen_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

public section

/-- **`keccak_open` meets its contract**, given `EW::mul`'s, `memcpy`'s, `slot_weights`'s and
the plain sumcheck's. -/
theorem keccakOpen_spec [NativeRustcArm.Host] {k : Nat} (hp : Placed code k)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hsw : ∀ c, Spec (label NativeRustcVmArm.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c))
    (hsc : ∀ a s, Spec (label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s)) :
    ∀ a s c, Spec (label NativeRustcVmArm.Vm.KeccakOpen.entryLabel) (KeccakOpenPre a s c) (KeccakOpenPost a s c) := by
  intro a s c m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.KeccakOpen.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.KeccakOpen.entryOffset) NativeRustcVmArm.Vm.KeccakOpen.entry_at]
  refine (sc_run hp h hsc).bind fun st ⟨hpc, hsc1⟩ ↦ ?_
  cases hr : scRun s m0 with
  | none => exact none_exit hp h hpc hsc1 hr
  | some r =>
    obtain ⟨⟨sl, v⟩, s1⟩ := r
    obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size m0.regs.X2.toNat c
      m0.regs.X6.toNat m0.regs.X7.toNat
    exact (sw_run hp h hsw hpc hsc1 hr).bind fun st ⟨hpc, hs⟩ ↦
      (fold_start hp h hpc hs).bind fun st ⟨hpc, hf⟩ ↦
      (fold_run hp hmul hmemcpy (c := ⟨a, s1, sl, v⟩) (ok_of h) hsz hrow hpc hf.mid hf.x29
        hf.x27 hf.x28 hf.x22 hf.x23 hf.x25 hf.x26 hf.rw).bind fun st ⟨hpc, hmid, hrw⟩ ↦
      some_exit hp h hr hpc hmid hrw

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
