import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedSigningViews
import SphincsSecurity.Proof.Fts.NormalizedTargetMatches

/-! ## TargetAssignmentReuse -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem targetTreeMatchCount_log (log : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view (log.get slot)) target tree =
      (log.map (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0)).sum := by
  rw [targetTreeMatchCount, ← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map log
    (fun entry => if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0))

theorem targetTreeMatchCount_log_append (log suffix : List α) (view : α → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view ((log ++ suffix).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        targetTreeMatchCount (fun slot => view (suffix.get slot)) target tree := by
  simp only [targetTreeMatchCount_log, List.map_append, List.sum_append]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetLogMatch (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (tree : FtsTree) : ENNReal :=
  (Fintype.card FtsLeaf : ENNReal) *
    (targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log) target tree : ENNReal)

noncomputable def normalizedTargetLogProduct (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  ∏ tree ∈ required, normalizedTargetLogMatch key cache log payload target tree

theorem targetTreeMatchCount_log_append_singleton (log : List α) (entry : α) (view : α → Option FewTimeView)
    (target : FewTimeView) (tree : FtsTree) :
    targetTreeMatchCount (fun slot => view ((log ++ [entry]).get slot)) target tree =
      targetTreeMatchCount (fun slot => view (log.get slot)) target tree +
        if ∃ source, view entry = some source ∧ source.1 = target.1 ∧ source.2 tree = target.2 tree then 1 else 0 := by
  simp only [targetTreeMatchCount_log_append, targetTreeMatchCount_log, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem normalizedSourceSubsetMatch_singleton (target source : FewTimeView) (tree : FtsTree) :
    normalizedSourceSubsetMatch target source {tree} = (Fintype.card FtsLeaf : ENNReal) * (sourceTreeMatch target source tree : ENNReal) := by
  simp only [normalizedSourceSubsetMatch, Finset.card_singleton, pow_one, sourceSubsetMatch, Finset.prod_singleton]

theorem eligibleSigningViews_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (hcache : before ≤ after)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    eligibleSigningViews (messageAnswers key.parameter after) key.root payload log =
      eligibleSigningViews (messageAnswers key.parameter before) key.root payload log := by
  funext slot
  exact eligibleSigningView?_cache_stable key.parameter key.root before after hcache payload (log.get slot)
    (hsigned _ (List.get_mem _ _))

theorem normalizedTargetLogMatch_le_of_eligibleView (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target source : FewTimeView) (tree : FtsTree)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hentry : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none ∨
      eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = some source) :
    normalizedTargetLogMatch key after (log ++ [entry]) payload target tree ≤
      normalizedTargetLogMatch key before log payload target tree + normalizedSourceSubsetMatch target source {tree} := by
  have hstable := eligibleSigningViews_cache_stable key before after log payload hcache hsigned
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  rw [hstable] at hstep
  rw [normalizedTargetLogMatch, hstep, Nat.cast_add, mul_add, normalizedSourceSubsetMatch_singleton]
  apply add_le_add le_rfl
  apply mul_le_mul' le_rfl
  apply Nat.cast_le.mpr
  rcases hentry with hnone | hsome
  · simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, Nat.zero_le]
  · simp only [hsome, Option.some.injEq, exists_eq_left', sourceTreeMatch, le_refl]

end SphincsSecurity.Concrete
