module

public import NativeRustcVmArm.Code.Vm.BasisWEval.Names
public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.GluedEval.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.SampleQueries.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Whir.FinalLevel.Glued
public import NativeRustcVmArm.Whir.FinalLevel.Rows
public import NativeRustcVmArm.Whir.FinalLevel.Sum

/-!
# `final_level` on AArch64

**`finalLevel_spec`**: X0 becomes `finalLevelM`'s `Some`/`None`, the `TState` at X0 its next state,
given its callees' contracts. The prologue reads the folded lane (`entry`); `grind` and
`sample_queries` (`queries`); `query_openings` and `each_row` (`rows`); `sumcheck_plain` (`sum`);
the point (`point`); the rotated point and `BasisW::eval` (`rotate`); the glued claims
(`glued`); `multilinear_eval`, the product and the end check (`finish`). Each `None` returns `0`.
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmArm.Vm.FinalLevel

public section

variable [Host] {k : Nat}

/-- **`final_level`'s contract.** -/
theorem finalLevel_spec (hp : Placed code k)
    (hrsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrow : ∀ rows op, Spec (Labels.label NativeRustcVmArm.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hbw : ∀ ba b, Spec (Labels.label NativeRustcVmArm.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b))
    (hge : ∀ g, Spec (Labels.label NativeRustcVmArm.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost) :
    ∀ a s level ba b w rounds, Spec (label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds) := by
  intro a s level ba b w rounds m0 h
  have c := Ctx.of_pre h
  rw [show Labels.label NativeRustcVmArm.Vm.FinalLevel.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.FinalLevel.entryOffset) NativeRustcVmArm.Vm.FinalLevel.entry_at]
  exact entry hp c hrsc fun _ _ _ hpc hb h22 h24 h26 h23 h25 hsz hfd hts hrun ↦
    queries hp c hgr hsq hpc ⟨hb, h22, h24, h23, hsz, hfd⟩ h26 h25 hts hrun
      fun _ _ _ hpc hl h26 h29 hq hts hrun ↦
    rows hp c hqo hrow hpc hl h26 h29 hq hts hrun fun _ _ hpc hl hts hrun ↦
    sum hp c hsc hpc hl hts hrun fun _ _ _ _ hpc hc htn htl hcl hts hrun ↦
    point hp c hext hpc hc htn htl hcl hts fun _ hpc hc h22 h23 h24 htl hbuf hts ↦
    rotate hp c hext hbw hpc hc h22 h23 h24 htl hbuf hts
      fun _ hpc hc h22 h29 h23 h24 htl hpt hopt hts ↦
    glued hp c hge hmul hpc hc htn h22 h29 h23 h24 htl hpt hopt hts fun _ hpc hB h21 h23 ↦
    finish hp c hmul hmle hpc hB.fr hB.x19 hB.x20 h21 h23 hB.size hB.fold htn hB.tl hB.cl hB.ts
      hrun

end

end NativeRustcVmArm.Whir.FinalLevel
