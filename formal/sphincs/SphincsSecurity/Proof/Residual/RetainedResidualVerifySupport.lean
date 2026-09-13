import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeVerifierSource
import SphincsSecurity.Proof.Residual.RetainedResidualSuccessTransfer
import SphincsSecurity.Proof.Residual.RetainedResidualVerify

/-! ## RetainedResidualWorld -/

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open InterleavedResidual (Routing)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem fixedSourceRun_bind {A B : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) A)
    (next : A → OracleComp (OracleWorld + SigningSpec) B) (memory : Memory) :
    fixedSourceRun context (computation >>= next) memory =
      (fixedSourceRun context computation memory >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun value => fixedSourceRun context (next value) result.2)) := by
  simp only [fixedSourceRun, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨value, after⟩
  cases value <;> rfl

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (liftHashSource)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem fixedHashStep_cache {inputs : Finset HashInput} (context : Context inputs) (input : HashInput)
    (memory : Memory) (answer : HashOutput)
    (hlive : (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing
      context.actual context.oracle input memory).1 = some answer) :
    (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing
      context.actual context.oracle input memory).2.external.cache =
      Function.update memory.external.cache input (some (context.oracle input)) := by
  rw [fixedHashStep_external]
  unfold fixedHashStep ResidualByteFrontend.fixedStep ResidualByteFrontend.fixedAnswer ResidualByteFrontend.checkedResult at hlive
  unfold ResidualByteFrontend.fixedStep ResidualByteFrontend.fixedAnswer
  split
  · rename_i hbad
    simp only [if_pos hbad, Option.bind_none, reduceCtorEq] at hlive
  · rfl

theorem fixedSourceRun_hash_success {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp HashSpec Result) (memory : Memory) (value : Result) (after : Memory)
    (hresult : fixedSourceRun context (liftHashSource computation) memory (some value, after) ≠ 0) :
    value = evalWithAnswerFn context.oracle computation ∧ CachedRun after.external.cache context.oracle computation ∧
      ∀ input, memory.external.cache input ≠ none → after.external.cache input ≠ none := by
  induction computation using OracleComp.inductionOn generalizing memory value after with
  | pure value =>
      simp only [liftHashSource, simulateQ_pure, fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff,
        not_not, Prod.mk.injEq, Option.some.injEq] at hresult
      obtain ⟨rfl, rfl⟩ := hresult
      exact ⟨rfl, CachedRun.pure _ _ _, fun _ h => h⟩
  | query_bind input next ih =>
      rw [FtsProbeSimulation.liftHashSource_query_bind, fixedSourceRun_query_bind] at hresult
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query,
        fixedByteImpl, pure_bind] at hresult
      generalize hstep : fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing
        context.actual context.oracle input memory = step at hresult
      rcases step with ⟨answer, middle⟩
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq, Option.some_ne_none,
            false_and, not_not] at hresult
      | some answer =>
          have hanswer : answer = context.oracle input := by
            rcases fixedHashStep_answer context input memory with hstop | hlive
            · rw [hstep] at hstop
              cases hstop
            · rw [hstep] at hlive
              exact Option.some.inj hlive
          subst answer
          have hcache : middle.external.cache = Function.update memory.external.cache input (some (context.oracle input)) := by
            have h := fixedHashStep_cache context input memory (context.oracle input) (by rw [hstep])
            simpa only [hstep] using h
          obtain ⟨hvalue, hcached, hpreserves⟩ := ih (context.oracle input) middle value after hresult
          refine ⟨hvalue, ?_, ?_⟩
          · intro other hother
            rw [queriedInputs_query_bind, List.mem_cons] at hother
            rcases hother with rfl | hother
            · apply hpreserves
              rw [hcache, Function.update_self]
              simp only [ne_eq, reduceCtorEq, not_false_eq_true]
            · exact hcached _ hother
          · intro other hother
            apply hpreserves
            rw [hcache]
            by_cases heq : other = input
            · rw [heq, Function.update_self]
              simp only [ne_eq, reduceCtorEq, not_false_eq_true]
            · rwa [Function.update_of_ne heq]

theorem fixedSourceRun_verify_honest {inputs : Finset HashInput} (context : Context inputs)
    (memory : Memory) (hcompatible : Compatible context memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (message : Message) (signature : Signature) (after : Memory)
    (hresult : fixedSourceRun context
      (FtsProbeSimulation.liftOracleWorldLeft (scheme.verify ⟨context.key.root, context.key.parameter⟩ message signature))
        memory (some true, after) ≠ 0) :
    ∃ digest, evalWithAnswerFn context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) = digest ∧
      CachedRun after.external.cache context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) ∧
      Admissible digest ∧ FullyHonestOpening context.oracle after.external.cache context.key (digestIndex digest) (digestLeaves digest) signature ∧
      ∀ tree, after.routing.disclosed (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) := by
  have hcompatible' := fixedSourceRun_compatible context _ memory hcompatible true after hresult
  rw [FtsProbeSimulation.liftOracleWorldLeft_scheme_verify] at hresult
  obtain ⟨hvalue, hcached, _⟩ := fixedSourceRun_hash_success context _ memory true after hresult
  exact hcompatible'.verify_honest hdummy hroot message signature hvalue.symm hcached

theorem fixedSourceRun_rest_honest {inputs : Finset HashInput} (context : Context inputs)
    (memory : Memory) (hcompatible : Compatible context memory)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (adversary : Adversary) (forgery : Forgery) (after : Memory)
    (hresult : fixedSourceRun context
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
        memory (some (forgery, true), after) ≠ 0) :
    ∃ digest, evalWithAnswerFn context.oracle (messageDigest context.key.parameter context.key.root forgery.message forgery.signature.randomness) = digest ∧
      CachedRun after.external.cache context.oracle
        (messageDigest context.key.parameter context.key.root forgery.message forgery.signature.randomness) ∧
      Admissible digest ∧ FullyHonestOpening context.oracle after.external.cache context.key (digestIndex digest) (digestLeaves digest) forgery.signature ∧
      ∀ tree, after.routing.disclosed (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) := by
  rw [FtsProbeSimulation.unloggedRetainedRestComputation, fixedSourceRun_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨⟨candidate, middle⟩, hmiddle, hresult⟩ := hresult
  cases candidate with
  | none =>
      simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq,
        Option.some_ne_none, false_and, not_not] at hresult
  | some candidate =>
      have hcompatible' := fixedSourceRun_compatible context _ memory hcompatible candidate middle hmiddle
      simp only [Option.elim_some] at hresult
      rw [fixedSourceRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨checked, finalMemory⟩, hchecked, hresult⟩ := hresult
      cases checked with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq,
            Option.some_ne_none, false_and, not_not] at hresult
      | some checked =>
          simp only [Option.elim_some, fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff,
            not_not, Prod.mk.injEq, Option.some.injEq] at hresult
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hresult
          exact fixedSourceRun_verify_honest context middle hcompatible' hdummy hroot _ _ _ hchecked

end SphincsSecurity.Concrete.RetainedResidual
