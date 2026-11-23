module

public import NativeRustcVmX64.Whir.FoldRound.Tail
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.FoldRound.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names

/-!
# `fold_round` on x86-64

**`foldRound_spec`**: rustc's `fold_round`, placed anywhere in the program, meets
`FoldRoundPre`/`FoldRoundPost` given `read_scalar`'s, `grind`'s, `squeeze`'s and `EW::mul`'s
contracts. Four `read_scalar` calls into the frame, each tag tested (`None` returns the tag `0`,
`none20`), the grind (`reads`); the two squeezes and the six products (`s1` to `s8_mul`); the
folded claim written, `α` pushed, `α`, `β` written to the output with the tag `1` (`tail`). The
state, the challenges and the transcript's state are `foldRound`'s (`NativeRustcVm.Whir.Fold`).
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound

public section

variable [Host] {k : Nat}

/-- **`fold_round` meets its contract.** -/
theorem foldRound_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) (a : DecArea) (s : TState)
    (w : WhirStateW) :
    Spec (Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel) (FoldRoundPre a s w) (FoldRoundPost a s w) := by
  intro m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.FoldRound.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FoldRound.b0Offset) from hp.label NativeRustcVmX64.Vm.FoldRound.entry_at]
  exact reads hp h (hrs a) (hgr a) fun _ _ _ _ _ _ hpc hA ↦
    s1 hp h hsq hpc hA fun _ hpc hP h15 h13 hax hdx ↦
    s2 hp h hsq hpc hP h15 h13 hax hdx fun _ hpc hP h15 _ hax hdx ↦
    s3 hp h hmul hpc hP h15 hax hdx fun _ hpc hP h15 h13 hax hdx ↦
    s4 hp h hmul hpc hP h15 h13 hax hdx fun _ hpc hP h15 hax hdx ↦
    s5_mul hp h hmul hpc hP h15 hax hdx fun _ hpc hP hax hdx ↦
    s6_mul hp h hmul hpc hP hax hdx fun _ hpc hP hax hdx ↦
    s7_mul hp h hmul hpc hP hax hdx fun _ hpc hP h15 h13 hax hdx ↦
    s8_mul hp h hmul hpc hP h15 h13 hax hdx fun _ hpc hP h15 h13 hax hdx ↦
    tail hp h hpc hP h15 h13 hax hdx

end

end NativeRustcVmX64.Whir.FoldRound
