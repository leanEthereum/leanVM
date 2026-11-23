module

public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Code.Vm.WhirLevels.Names
public import NativeRustcVmArm.Whir.WhirLevels.Entry

/-!
# `whir_levels` on AArch64

**`whirLevels_spec`**: X0 becomes `whirLevels logN laneFolds b 0 levels`'s `Some`/`None`, the
`TState` its next state, given `fold_rounds`', `next_level`'s and `final_level`'s contracts.
rustc unrolled the loop over the levels (a ladder has `3` to `6`): the prologue keeps the arguments
in X19 to X28 (`Regs`); each level runs its fold rounds (`fold_stage`), computes `μ` (`w_stage`),
then either jumps to `final_level` after the epilogue (a tail call whose contract ends the
function, `final_stage`) or calls `next_level` (`next_stage`) and goes on to the next level; a
`None` returns `0` (`exit_none`). Model: `whirLevels_single`, `whirLevels_cons_cons`.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.WhirLevels

public section

variable [Host] {k : Nat}

/-- **`whir_levels`' contract.** -/
theorem whirLevels_spec (hp : Placed code k)
    (hfr : ∀ a s w, Spec (label NativeRustcVmArm.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w) (FoldRoundsPost a s w))
    (hnl : ∀ a s level w rounds, Spec (label NativeRustcVmArm.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (hfl : ∀ a s level ba b w rounds, Spec (label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (a : DecArea) (s : TState) (levels : List LeanVM.Parameters.Whir.Level) (ba : BasisAddrs)
    (b : BasisW) (claim : EW) :
    Spec (label NativeRustcVmArm.Vm.WhirLevels.entryLabel) (WhirLevelsPre a s levels ba b claim)
      (WhirLevelsPost a s levels b claim) := by
  intro m0 h
  obtain ⟨rate, c⟩ := Ctx.of_pre h
  rw [show Labels.label NativeRustcVmArm.Vm.WhirLevels.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.WhirLevels.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.WhirLevels.entryOffset) NativeRustcVmArm.Vm.WhirLevels.entry_at]
  exact entry hp ⟨hfr, hnl, hfl⟩ c

end

end NativeRustcVmArm.Whir.WhirLevels
