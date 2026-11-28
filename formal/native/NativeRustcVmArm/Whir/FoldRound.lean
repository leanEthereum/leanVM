module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.FoldRound.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Whir.FoldRound.Fin2

/-!
# `fold_round`'s contract

The prologue, four `read_scalar`s and the grind (`reads`, `None` returned where one fails), the two
squeezes (`squeezes`), the six products (`muls`), the folded claim, the push of `α` and the round
written (`tail`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {k : Nat}

/-- **`fold_round`'s contract.** -/
theorem foldRound_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (a : DecArea) (s : TState)
    (w : WhirStateW) :
    Spec (Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.FoldRound.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRound.entryOffset) NativeRustcVmArm.Vm.FoldRound.entry_at]
  exact reads hp h (hrs a) (hgr a) fun st s5 u0 v c0 c1 hpc hb ↦
    squeezes hp h hsq hpc hb fun st' hpc' hb' ↦
      muls hp h hmul hpc' hb' fun st'' hpc'' hb'' ↦ tail hp h hpc'' hb''

end

end NativeRustcVmArm.Whir.FoldRound
