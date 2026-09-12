import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheMessageWeight
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMessageWeight_of_no_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after)
    (hnoNew : ∀ input output, before input = none → MessageHashInput parameter input → after input = some output →
      ¬ Admissible (truncateMessageDigest output)) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  have hzero : cacheMessageWeight parameter (fun input source => if before input = none then weight input source else 0) after = 0 := by
    unfold cacheMessageWeight
    apply ENNReal.tsum_eq_zero.mpr
    intro input
    unfold cacheMessageEntryWeight
    cases houtput : after input with
    | none => rfl
    | some output =>
        simp only
        by_cases hgood : MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output)
        · rw [if_pos hgood]
          by_cases hfresh : before input = none
          · exact (hnoNew input output hfresh hgood.1 houtput hgood.2).elim
          · simp only [hfresh, if_false]
        · simp only [hgood, if_false]
  rw [hzero, add_zero]

theorem cacheMessageWeight_of_single_new (parameter : PublicParameter) (weight : HashInput → FewTimeView → ENNReal)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hmessage : MessageHashInput parameter input) (hafter : after input = some output)
    (hadmissible : Admissible (truncateMessageDigest output))
    (hunique : ∀ other answer, before other = none → MessageHashInput parameter other → after other = some answer →
      Admissible (truncateMessageDigest answer) → other = input) :
    cacheMessageWeight parameter weight after = cacheMessageWeight parameter weight before + weight input (hashOutputFewTimeView output) := by
  rw [cacheMessageWeight_of_le parameter weight before after hcache]
  congr 1
  unfold cacheMessageWeight
  rw [tsum_eq_single input]
  · simp only [cacheMessageEntryWeight, hafter, hmessage, hadmissible, and_self, if_true, hfresh]
  · intro other hne
    unfold cacheMessageEntryWeight
    cases hanswer : after other with
    | none => rfl
    | some answer =>
        simp only
        by_cases hgood : MessageHashInput parameter other ∧ Admissible (truncateMessageDigest answer)
        · rw [if_pos hgood]
          by_cases hbefore : before other = none
          · exact (hne (hunique other answer hbefore hgood.1 hanswer hgood.2)).elim
          · simp only [hbefore, if_false]
        · simp only [hgood, if_false]

end SphincsSecurity.Concrete
