module

public import NativeRustcVmX64.Whir.FinalLevel.End
public import NativeRustcVmX64.Code.Vm.BasisWEval.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Code.Vm.GluedEval.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.SampleQueries.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names

/-!
# `final_level` on x86-64

The callee contracts compose the transcript, row checks, sumcheck, rotated basis evaluation,
glued claims and final equality check, preserving the full return and memory contract.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

variable [Host] {k : Nat}

/-- `final_level`'s contract, using its callees' contracts. -/
theorem finalLevel_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SampleQueries.entryLabel) (SampleQueriesPre a s)
      (SampleQueriesPost a s))
    (hqo : ∀ a s Q, Spec (Labels.label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
      (QueryOpeningsPost a s Q))
    (hrow : ∀ rows op, Spec (Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.entryLabel) (EachRowFinalPre rows op)
      (EachRowFinalPost rows))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hbw : ∀ ba b, Spec (Labels.label NativeRustcVmX64.Vm.BasisWEval.entryLabel) (BasisWEvalPre ba b) (BasisWEvalPost b))
    (hge : ∀ g, Spec (Labels.label NativeRustcVmX64.Vm.GluedEval.entryLabel) (GluedEvalPre g) (GluedEvalPost g))
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost) :
    ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmX64.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds) := by
  intro a s level ba b w rounds m0 hpre
  have c := Ctx.of_pre hpre
  rw [show Labels.label NativeRustcVmX64.Vm.FinalLevel.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b0Offset) from hp.label NativeRustcVmX64.Vm.FinalLevel.entry_at]
  refine entry hp c hrs fun st1 folded s1 hpc1 hl1 hbx1 hbp1 hts1 hr1 ↦ ?_
  refine queries hp c hgr hsq hpc1 hl1 hbx1 hbp1 hts1 hr1
    fun st2 qs s3 hpc2 hl2 hbp2 hq2 hts2 hr2 ↦ ?_
  refine openings hp c hqo hpc2 hl2 hbp2 hq2 hts2 hr2
    fun st3 rows s4 hpc3 hl3 hbp3 hbx3 hq3 hrows3 hop3 hopBounds3 hts3 hr3 ↦ ?_
  refine check hp c hrow hpc3 hl3 hbp3 hbx3 hq3 hrows3 hop3 hopBounds3 hts3 hr3
    fun st4 hpc4 hl4 hts4 hr4 ↦ ?_
  refine sum hp c hsc hpc4 hl4 hts4 hr4
    fun st5 tail claim s5 hpc5 hc5 hbx5 h48 h56 htn htail5 hcl5 hts5 hr5 ↦ ?_
  refine point hp c hext hpc5 hc5 hbx5 h48 h56 htn htail5 hcl5 hts5
    fun st6 hpc6 hc6 hbx6 h12 h15 h13 h56 hpt hrot htail6 hts6 ↦ ?_
  refine rotate hp c hbw hpc6 hc6 hbx6 h12 h15 h13 h56 hpt hrot htail6 htn hts6
    fun st7 hpc7 hc7 hbx7 h12 h15 h48 hpt hb72 htail7 hts7 ↦ ?_
  refine glued hp c hge hmul hpc7 hc7 hbx7 h12 h15 h48 hpt hb72 htail7 htn hts7
    fun st8 hpc8 hgb ↦ ?_
  exact finish hp c hmul hmle hpc8 htn hgb hr5

end

end NativeRustcVmX64.Whir.Levels.FL

/--
info: 'NativeRustcVmX64.Whir.Levels.FL.finalLevel_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Whir.Levels.FL.finalLevel_spec
