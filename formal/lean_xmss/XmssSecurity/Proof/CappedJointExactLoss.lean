import XmssSecurity.Proof.CachedSelectionBound
import XmssSecurity.Proof.CappedUnifiedExpectedDigest
import XmssSecurity.Proof.LossDecomposition

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningCachedSelectionOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr[WinningSecondLaneBadEventOccurs |
      cappedDetailedGameWithEncodingTrace adversary] ≤
    q /
      ((2 ^ digestBits : Nat) : ENNReal)

theorem hasSecondLaneBound_of_hashQueryBound
    (q : Nat) (adversary : Adversary)
    (hbound : HasAfterKeygenHashQueryBound Concrete.scheme adversary q) (hq : q < 2 ^ 127) :
    HasSecondLaneBound q adversary := by
  let encoding := CappedEncodingMonitor.expectedPostKeygenEncodingQueries adversary
  let structural := expectedPostKeygenStructuralQueries adversary
  have hstructural :
      Pr[fun execution : CappedEncodingTraceExecution =>
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      structural / ((2 ^ digestBits : Nat) : ENNReal) := by
    change Pr[fun execution : CappedEncodingTraceExecution =>
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
        cappedDetailedGameWithEncodingTrace adversary] ≤
      expectedPostKeygenStructuralQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal)
    calc
      _ = Pr[fun execution : GameOutcome × QueryCache HashSpec =>
            WinningStructuralCollisionOccurs execution.2 execution.1 |
          detailedGameWithCache Concrete.scheme adversary] := by
        rw [← cappedDetailedGameWithEncodingTrace_cache_projection,
          probEvent_map]
        rfl
      _ ≤ _ :=
        winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries
          adversary
  unfold HasSecondLaneBound WinningSecondLaneBadEventOccurs
  calc
    Pr[fun execution : CappedEncodingTraceExecution =>
        WinningCachedSelectionOccurs execution ∨
          WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
      cappedDetailedGameWithEncodingTrace adversary] ≤
      Pr[WinningCachedSelectionOccurs |
          cappedDetailedGameWithEncodingTrace adversary] +
        Pr[fun execution : CappedEncodingTraceExecution =>
            WinningStructuralCollisionOccurs execution.2.1.1 execution.1 |
          cappedDetailedGameWithEncodingTrace adversary] :=
      probEvent_or_le _ _ _
    _ ≤ encoding / ((2 ^ digestBits : Nat) : ENNReal) +
        structural / ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add
        (capped_cachedSelection_probability_le_expectedDigest q adversary hbound hq)
        hstructural
    _ = (encoding + structural) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      simp only [div_eq_mul_inv, add_mul]
    _ ≤ q /
        ((2 ^ digestBits : Nat) : ENNReal) := by
      gcongr
      exact postKeygenEncoding_add_structural_expected_le q adversary hbound

/-- Lane 1's constant, the verification's queries and the encoding monitor's. -/
def firstLaneSlack : Nat := 2 ^ 19

theorem capped_two_lane_loss_budget (q : Nat) :
    ((q + firstLaneSlack : Nat) : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) +
        (q : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) ≤
      ((2 * q + lowerOrderSlack : Nat) : ENNReal) / ((2 ^ 128 : Nat) : ENNReal) := by
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div _ (by norm_num [digestBits])
  exact_mod_cast (show q + firstLaneSlack + q ≤ 2 * q + lowerOrderSlack by
    simp only [firstLaneSlack, lowerOrderSlack]; omega)

end XmssSecurity
