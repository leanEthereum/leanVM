import XmssSecurity.Proof.CappedJointExactLoss

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningExactFirstLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  ((WinningOutcomeBadEventOccurs execution.2.1.1 execution.1 .encoding ∧
      ¬WinningCachedSelectionOccurs execution) ∨
    GlobalWinningChainValueRevealed execution.2.1.1 execution.1 ∨
    WinningTopGuessOccurs execution.2.1.1 execution.1)

def HasExactFirstLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs x] ≤
    (q + firstLaneSlack : Nat) /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem capped_winning_implies_exactFirstLane_or_secondLane
    (adversary : Adversary)
    (execution : CappedEncodingTraceExecution)
    (hmem : execution ∈ support
      (cappedDetailedGameWithEncodingTrace adversary))
    (hwin : execution.1.won = true) :
    WinningExactFirstLaneBadEventOccurs execution ∨
      WinningSecondLaneBadEventOccurs execution := by
  by_cases hcachedSelection : WinningCachedSelectionOccurs execution
  · exact Or.inr (Or.inl hcachedSelection)
  · rcases capped_winning_implies_cachedSelection_or_digestBad
        adversary execution hmem hwin with hcachedSelection' | hdigest
    · exact (hcachedSelection hcachedSelection').elim
    · rcases hdigest with hencoding | hchain | hstructural | htop
      · exact Or.inl (Or.inl ⟨hencoding.1, hcachedSelection⟩)
      · exact Or.inl (Or.inr (Or.inl hchain))
      · exact Or.inr (Or.inr hstructural)
      · exact Or.inl (Or.inr (Or.inr htop))

theorem capped_forgeAdvantage_le_exactFirstLane_add_secondLane
    (adversary : Adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs x] +
      Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningSecondLaneBadEventOccurs x] := by
  calc
    forgeAdvantage Concrete.scheme adversary =
        Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[execution.1.won = true] := by
      rw [forgeAdvantage_eq_detailedGameWithCache,
        ← cappedDetailedGameWithEncodingTrace_cache_projection, prEvent_map]

    _ ≤ Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningExactFirstLaneBadEventOccurs execution ∨
            WinningSecondLaneBadEventOccurs execution] := by
      apply prEvent_mono_of_support
      intro execution hmem hwin
      exact capped_winning_implies_exactFirstLane_or_secondLane
        adversary execution hmem hwin
    _ ≤ _ := prEvent_or_le _ _ _

theorem capped_forgeAdvantage_le_of_exactTwoLaneBounds
    (q : Nat) (adversary : Adversary)
    (hfirst : HasExactFirstLaneBound q adversary)
    (hsecond : HasSecondLaneBound q adversary) :
    forgeAdvantage Concrete.scheme adversary ≤
      ((2 * q + lowerOrderSlack : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) :=
  (capped_forgeAdvantage_le_exactFirstLane_add_secondLane adversary).trans
    ((add_le_add hfirst hsecond).trans (capped_two_lane_loss_budget q))

def HasExactFirstLaneBounds : Prop :=
  ∀ (q : Nat) (adversary : Adversary),
    HasAfterKeygenHashQueryBound Concrete.scheme adversary q →
      HasExactFirstLaneBound q adversary

theorem concreteScheme_afterKeygenSecurity_of_exactFirstLaneBounds
    (hfirst : HasExactFirstLaneBounds) :
    HasAfterKeygenSecurity Concrete.scheme := by
  intro q hq adversary hbound
  exact capped_forgeAdvantage_le_of_exactTwoLaneBounds q adversary (hfirst q adversary hbound)
    (hasSecondLaneBound_of_hashQueryBound q adversary hbound hq)

end XmssSecurity
