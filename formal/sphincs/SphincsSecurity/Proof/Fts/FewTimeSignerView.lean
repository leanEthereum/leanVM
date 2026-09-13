import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeUniform
import SphincsSecurity.Proof.Scheme.NoMessage
/-!
# Signer digest views

This proof-only signer exposes the few-time view selected by the digest loop alongside the ordinary
signature result. Forgetting the extra component recovers the concrete signer exactly.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def selectedFewTimeView (index : Index) (leaves : IndexGroup → FtsLeaf) : FewTimeView :=
  (index, fun tree => leaves (ftsIndexOf tree))

noncomputable def signWithView (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature × Option FewTimeView) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest secretKey randomness index leaves)
      pure (signature, some (selectedFewTimeView index leaves))

theorem signWithView_fst (secretKey : SecretKey) (message : Message) :
    Prod.fst <$> signWithView secretKey message = sign secretKey message := by
  rw [sign_eq_digestLoop_afterDigest]
  simp only [signWithView, map_eq_bind_pure_comp, bind_assoc]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => simp
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      simp

theorem simulateQ_signWithView_fst_run (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
        (simulateQ romImpl (signWithView secretKey message)).run cache =
      (simulateQ romImpl (sign secretKey message)).run cache := by
  calc
    _ = (simulateQ romImpl (Prod.fst <$> signWithView secretKey message)).run cache := by
      rw [simulateQ_map, StateT.run_map]
    _ = _ := by rw [signWithView_fst]

set_option linter.constructorNameAsVariable false in
theorem signWithView_support_some
    (secretKey : SecretKey) (message : Message)
    (initialCache finalCache : QueryCache HashSpec)
    (signature : Signature) (view : Option FewTimeView)
    (hmem : ((some signature, view), finalCache) ∈ support
      ((simulateQ romImpl (signWithView secretKey message)).run initialCache)) :
    ∃ (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
        (loopCache : QueryCache HashSpec),
      (some (randomness, index, leaves), loopCache) ∈ support
          ((simulateQ romImpl
            (signDigestLoop digestAttemptLimit secretKey message)).run initialCache)
        ∧ (some signature, finalCache) ∈ support
          ((simulateQ (randomOracle : QueryImpl HashSpec
            (StateT (QueryCache HashSpec) ProbComp))
            (signAfterDigest secretKey randomness index leaves)).run loopCache)
        ∧ view = some (selectedFewTimeView index leaves) := by
  rw [signWithView, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨loopResult, loopCache⟩, hloop, hfinish⟩ := hmem
  cases loopResult with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at hfinish
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfinish
      obtain ⟨⟨signatureResult, signatureCache⟩, hsignature, hpure⟩ := hfinish
      have hpureEq : ((some signature, view), finalCache) =
          ((signatureResult, some (selectedFewTimeView index leaves)), signatureCache) := by
        simpa only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] using hpure
      have hresult : some signature = signatureResult :=
        congrArg (fun result => result.1.1) hpureEq
      have hview : view = some (selectedFewTimeView index leaves) :=
        congrArg (fun result => result.1.2) hpureEq
      have hcache : finalCache = signatureCache := congrArg Prod.snd hpureEq
      rw [← hresult, ← hcache] at hsignature
      refine ⟨randomness, index, leaves, loopCache, hloop, ?_, hview⟩
      simpa only [simulateQ_romImpl_liftM] using hsignature

end SphincsSecurity.Concrete
