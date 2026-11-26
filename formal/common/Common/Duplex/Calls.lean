module

public import Common.Duplex.Main
public import Common.Defs

@[expose] public section

/-!
# The simulator's queries of the challenges

Each step of the duplex lemma's simulator (`simImpl`) makes at most one query of the challenges
`G`, and only for a call of `F` (`isWeightBound_simImpl`): with `gCalls` counting the queries of
`G`, the simulated adversary queries `G` at most as often as the real one calls `F`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP)
open scoped ENNReal

namespace Common.SeedDuplex

variable {Msg Dg Root Z : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq Root] [SampleableType Dg] [SampleableType Z]
  [Fintype Z] [Fintype Root] [Nonempty Z]

section Weights

variable {St W Cp : Type} [DecidableEq St] [DecidableEq Cp] [SampleableType St]
  [SampleableType W] [Fintype St] [Fintype W]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

/-- Queries of the challenges `G`, one each. -/
def gCalls : (unifSpec + GSpec Msg Dg Root Z n).Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

/-- **Each step of the simulator makes at most one query of `G`**, and only for a call of `F`. -/
theorem isWeightBound_simImpl (t : (Rom2 Msg Dg St).Domain) (s : SimSt Dg St Root n) :
    QueryCostAtMost ((simImpl D hP gaP t).run s) (gCalls (Msg := Msg) (Dg := Dg) (Root := Root)
      (Z := Z) (n := n)) (fCalls (Msg := Msg) (Dg := Dg) (St := St) t) := by
  have hu : ∀ {β : Type} (p : ProbComp β),
      QueryCostAtMost (liftM p : OracleComp (unifSpec + GSpec Msg Dg Root Z n) β) gCalls 0 :=
    fun p ↦ isWeightBound_liftM_probComp gCalls (fun _ ↦ rfl) p
  rcases t with k | m | x
  · simp only [simImpl, StateT.run_monadLift, monadLift_self]
    exact (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [simImpl, StateT.run_mk]
    exact ((isWeightBound_query gCalls (.inr (.inl m))).bind fun _ ↦
      isWeightBound_pure _ _ 0)
  · simp only [simImpl, StateT.run_mk]
    split
    · trivial
    · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
      unfold freshAns
      split
      · split
        · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)
        · exact ((isWeightBound_query gCalls (.inr (.inr _))).bind fun _ ↦
            (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0)
      · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)

end Weights

end Common.SeedDuplex
