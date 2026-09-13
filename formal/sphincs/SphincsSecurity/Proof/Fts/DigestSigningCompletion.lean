import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestSelectionWeight
import SphincsSecurity.Proof.Fts.SelectedDigestCache
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAfterDigest signWithView

def DigestCompletionPreservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec) : Prop :=
  DigestCompletionConsistent loop result ∧ messageAnswers key.parameter result.2 = messageAnswers key.parameter loop.2

theorem digestCompletion_successful_cached_output (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result)
    (signature : Signature) (hs : result.1.1 = some signature) :
    ∃ output, result.2 (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message signature.randomness)) = some output ∧
      Admissible (truncateMessageDigest output) ∧ result.1.2 = some (hashOutputFewTimeView output) := by
  obtain ⟨index, leaves, hselected⟩ := hcompletion.1.2 signature hs
  have hloop' : (some (signature.randomness, index, leaves), loop.2) ∈ support
      ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before) := by
    have heq : loop = (some (signature.randomness, index, leaves), loop.2) := Prod.ext hselected rfl
    rwa [← heq]
  obtain ⟨output, hcached, hadmissible, hview⟩ := signDigestLoop_selected_cached_output
    digestAttemptLimit key message before loop.2 signature.randomness index leaves hloop'
  refine ⟨output, ?_, hadmissible, ?_⟩
  · exact (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).trans hcached
  · simp only [hcompletion.1.1, selectedLoopView?, hselected, Option.map_some, ← hview]

noncomputable def originalDigestCompletion (key : SecretKey) (loop : DigestLoopRecord) :
    ProbComp ((Option Signature × Option FewTimeView) × QueryCache HashSpec) :=
  match loop.1 with
  | none => pure ((none, none), loop.2)
  | some (randomness, index, leaves) =>
      (fun result => ((result.1, some (selectedFewTimeView index leaves)), result.2)) <$>
        (simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2

theorem signWithView_run_eq_digestCompletion (key : SecretKey) (message : Message) (before : QueryCache HashSpec) :
    (simulateQ romImpl (signWithView key message)).run before =
      (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= originalDigestCompletion key := by
  rw [signWithView, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro loop
  cases hl : loop.1 with
  | none => simp only [originalDigestCompletion, hl, simulateQ_pure, StateT.run_pure]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        simulateQ_romImpl_liftM, map_eq_bind_pure_comp]
      rfl

theorem originalDigestCompletion_preservesMessages (key : SecretKey) (loop : DigestLoopRecord)
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hr : result ∈ support (originalDigestCompletion key loop)) :
    DigestCompletionPreservesMessages key loop result := by
  cases hl : loop.1 with
  | none =>
      have heq : result = ((none, none), loop.2) := by
        simpa only [originalDigestCompletion, hl, support_pure, Set.mem_singleton_iff] using hr
      subst result
      simp only [DigestCompletionPreservesMessages, DigestCompletionConsistent, selectedLoopView?, hl,
        Option.map_none, reduceCtorEq, false_implies, implies_true, and_self]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      simp only [originalDigestCompletion, hl, support_map] at hr
      obtain ⟨⟨signature, after⟩, hfinish, rfl⟩ := hr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [selectedLoopView?, hl, Option.map_some]
      · intro successful hs
        have hfinish' : (some successful, after) ∈ support
            ((simulateQ (randomOracle : QueryImpl HashSpec _) (signAfterDigest key randomness index leaves)).run loop.2) := by
          rwa [← hs]
        have hrandomness := signAfterDigest_support_some_randomness key randomness index leaves loop.2 after successful hfinish'
        exact ⟨index, leaves, by simpa only [hrandomness] using hl⟩
      · funext payload
        exact signAfterDigest_message_cache_eq key randomness index leaves loop.2 after signature hfinish payload

end SphincsSecurity.Concrete
