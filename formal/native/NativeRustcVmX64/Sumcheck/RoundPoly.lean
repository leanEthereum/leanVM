module

public import NativeRustcVmX64.Sumcheck.RoundPoly.Entry
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `TState::sumcheck_round_poly` on x86-64

**`roundPoly_spec`**: in equality mode (`some_entry`) or plain mode (`none_entry`), the round
polynomial `sumcheckRoundPoly count claim eq` at the message, the `TState` the next state, AL its
`Option<()>` (`RoundPolyPost`).
-/

namespace NativeRustcVmX64.Sumcheck.RoundPoly

open NativeRustcX64 NativeRustcVmX64.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`sumcheck_round_poly`'s contract.** -/
theorem roundPoly_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (a : DecArea) (s : TState) (e : Option EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.b0Offset) from hp.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entry_at]
  cases e with
  | none => exact none_entry hp hrs hrss hsum hbl hgr hpre
  | some ev => exact some_entry hp hrss hsum hbl hgr hmul hpre

end

end NativeRustcVmX64.Sumcheck.RoundPoly
