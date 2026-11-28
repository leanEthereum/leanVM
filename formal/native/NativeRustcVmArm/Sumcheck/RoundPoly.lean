module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Sumcheck.RoundPoly.Entry

/-!
# `TState::sumcheck_round_poly`

**`roundPoly_spec`**: in equality mode (`some_entry`) or plain mode (`none_entry`), the round
polynomial `sumcheckRoundPoly count claim eq` at the message, the `TState` the next state
(`RoundPolyPost`).
-/

namespace NativeRustcVmArm.Sumcheck.RoundPoly

open NativeRustcArm NativeRustcVmArm.Vm.TStateSumcheckRoundPoly
open NativeVm.Model NativeRustcVm.Transcript

public section

variable [Host] {k : Nat}

/-- **`sumcheck_round_poly`'s contract.** -/
theorem roundPoly_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hsum : Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (a : DecArea) (s : TState) (e : Option EW) :
    Spec (Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryOffset) NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entry_at]
  cases e with
  | none => exact none_entry hp hrs hrss hsum hbl hgr hpre
  | some ev => exact some_entry hp hrss hsum hbl hgr hmul hpre

end

end NativeRustcVmArm.Sumcheck.RoundPoly
