import SphincsSecurity.Proof.Reference.FixedHashBoundary
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop signAfterDigest boundaryEval
set_option backward.isDefEq.respectTransparency false

theorem fixedBoundaryRun_bind_nonzero {A B : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (first : OracleComp OracleWorld A) (next : A → OracleComp OracleWorld B) (result : B × SigningBoundaryTrace)
    (hresult : 𝒟[fixedBoundaryRun parameter oracle (first >>= next)] result ≠ 0) :
    ∃ before after, 𝒟[fixedBoundaryRun parameter oracle first] before ≠ 0 ∧
      𝒟[fixedBoundaryRun parameter oracle (next before.1)] after ≠ 0 ∧ result = (after.1, before.2 * after.2) := by
  rw [fixedBoundaryRun_bind, evalDist_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨before, hbefore, hresult⟩ := hresult
  rw [evalDist_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨after, hafter, hresult⟩ := hresult
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  exact ⟨before, after, hbefore, hafter, hresult⟩

private theorem fixedBoundaryRun_lift_hash_return {A B : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec A) (finish : A → B) :
    fixedBoundaryRun parameter oracle ((liftM computation : OracleComp OracleWorld A) >>= fun value => pure (finish value)) =
      pure (finish (evalWithAnswerFn oracle computation), (boundaryEval parameter oracle computation).2) := by
  rw [fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash, pure_bind, fixedBoundaryRun_pure, map_pure, mul_one, boundaryEval_fst]

theorem boundaryEval_signAttempt (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (message : Message) (randomness : Randomness) :
    boundaryEval key.parameter oracle (signAttempt key message randomness) =
      (signAttemptResultOfOutput (oracle (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness))),
        FreeMonoid.of (some (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness),
          oracle (tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness))))) := by
  have hquery (input : HashInput) :
      evalWithAnswerFn oracle (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = oracle input := rfl
  by_cases h : Admissible (truncateMessageDigest (oracle (tweakableHashInput key.parameter .message
    (messageDigestPayload key.root message randomness))))
  all_goals simp [signAttempt, messageDigest, oracleHash, boundaryEval_bind, boundaryEval_hash_query,
    hquery, boundaryEval_pure, signAttemptResultOfOutput, signingBoundaryTrace,
    FtsProbeSimulation.MessageHashInput, h]

private theorem signDigestLoop_succ (key : SecretKey) (message : Message) (attempts : Nat) :
    signDigestLoop (attempts + 1) key message = (do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM (signAttempt key message randomness : OracleComp HashSpec _)
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts key message) := by
  rw [signDigestLoop]
  apply bind_congr
  intro randomness
  apply bind_congr
  intro attempt
  cases attempt with
  | none => rfl
  | some selected => rcases selected with ⟨index, leaves⟩; rfl

private noncomputable def finishSelected (key : SecretKey) :
    Option (Randomness × Index × (IndexGroup → FtsLeaf)) → OracleComp OracleWorld (Option Signature × Option FewTimeView)
  | none => pure (none, none)
  | some (randomness, index, leaves) => do
      let signature ← liftM (signAfterDigest key randomness index leaves)
      pure (signature, some (selectedFewTimeView index leaves))

private theorem signWithView_bind (key : SecretKey) (message : Message) :
    signWithView key message = signDigestLoop digestAttemptLimit key message >>= finishSelected key := by
  rw [signWithView]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some selected => rcases selected with ⟨randomness, index, leaves⟩; rfl

theorem fixedBoundaryRun_digest_selected (key : SecretKey) (oracle : QueryImpl HashSpec Id) (message : Message)
    (attempts : Nat) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (trace : SigningBoundaryTrace)
    (hresult : 𝒟[fixedBoundaryRun key.parameter oracle (signDigestLoop attempts key message)]
      (some (randomness, index, leaves), trace) ≠ 0) :
    let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message randomness)
    signAttemptResultOfOutput (oracle input) = some (index, leaves) ∧ (input, oracle input) ∈ trace.messageCalls := by
  induction attempts generalizing randomness index leaves trace with
  | zero =>
      simp only [signDigestLoop, fixedBoundaryRun_pure, evalDist_pure, ne_eq,
        SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq, Option.some_ne_none, false_and, not_not] at hresult
  | succ attempts ih =>
      rw [signDigestLoop_succ] at hresult
      obtain ⟨⟨sampled, sampledTrace⟩, ⟨result, restTrace⟩, _, hrest, heq⟩ :=
        fixedBoundaryRun_bind_nonzero key.parameter oracle _ _ _ hresult
      obtain ⟨⟨attempt, attemptTrace⟩, ⟨finished, finishTrace⟩, hattempt, hfinish, heq'⟩ :=
        fixedBoundaryRun_bind_nonzero key.parameter oracle _ _ _ hrest
      have htrace : trace = sampledTrace * (attemptTrace * finishTrace) :=
        (Prod.mk.inj heq).2.trans (congrArg (sampledTrace * ·) (Prod.mk.inj heq').2)
      have hvalue : some (randomness, index, leaves) = finished :=
        (Prod.mk.inj heq).1.trans (Prod.mk.inj heq').1
      cases attempt with
      | none =>
          rw [← hvalue] at hfinish
          obtain ⟨hselected, hmem⟩ := ih randomness index leaves finishTrace hfinish
          refine ⟨hselected, ?_⟩
          rw [htrace, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
          exact Or.inr (by rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append]; exact Or.inr hmem)
      | some selected =>
          rcases selected with ⟨selectedIndex, selectedLeaves⟩
          have hfinish' : (finished, finishTrace) = (some (sampled, selectedIndex, selectedLeaves), 1) := by
            simpa only [fixedBoundaryRun_pure, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hfinish
          have hselected : (some (selectedIndex, selectedLeaves), attemptTrace) =
              boundaryEval key.parameter oracle (signAttempt key message sampled) := by
            simpa only [fixedBoundaryRun_lift_hash, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hattempt
          rw [boundaryEval_signAttempt] at hselected
          have hmem : (tweakableHashInput key.parameter .message (messageDigestPayload key.root message sampled),
              oracle (tweakableHashInput key.parameter .message (messageDigestPayload key.root message sampled))) ∈ trace.messageCalls := by
            rw [htrace, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
            refine Or.inr ?_
            rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append]
            refine Or.inl ?_
            rw [(Prod.mk.inj hselected).2]
            exact List.mem_singleton_self _
          have hvalues : (randomness, index, leaves) = (sampled, selectedIndex, selectedLeaves) :=
            Option.some.inj (hvalue.trans (Prod.mk.inj hfinish').1)
          dsimp only
          rw [(Prod.mk.inj hvalues).1, (Prod.mk.inj (Prod.mk.inj hvalues).2).1,
            (Prod.mk.inj (Prod.mk.inj hvalues).2).2]
          exact ⟨(Prod.mk.inj hselected).1.symm, hmem⟩

private theorem finish_none_support (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (result : (Option Signature × Option FewTimeView) × SigningBoundaryTrace)
    (h : 𝒟[fixedBoundaryRun key.parameter oracle (finishSelected key none)] result ≠ 0) : result = ((none, none), 1) := by
  simpa only [finishSelected, fixedBoundaryRun_pure, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using h

private theorem finish_some_support (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (result : (Option Signature × Option FewTimeView) × SigningBoundaryTrace)
    (h : 𝒟[fixedBoundaryRun key.parameter oracle (finishSelected key (some (randomness, index, leaves)))] result ≠ 0) :
    result = ((evalWithAnswerFn oracle (signAfterDigest key randomness index leaves), some (selectedFewTimeView index leaves)),
      (boundaryEval key.parameter oracle (signAfterDigest key randomness index leaves)).2) := by
  simpa only [finishSelected, fixedBoundaryRun_lift_hash_return, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using h

private theorem finish_success (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (selected : Option (Randomness × Index × (IndexGroup → FtsLeaf)))
    (signature : Signature) (view : Option FewTimeView) (trace : SigningBoundaryTrace)
    (h : 𝒟[fixedBoundaryRun key.parameter oracle (finishSelected key selected)] ((some signature, view), trace) ≠ 0) :
    ∃ randomness index leaves, selected = some (randomness, index, leaves) ∧
      evalWithAnswerFn oracle (signAfterDigest key randomness index leaves) = some signature ∧
      view = some (selectedFewTimeView index leaves) := by
  cases selected with
  | none =>
      have heq := finish_none_support key oracle _ h
      have hnone : some signature = none := (Prod.mk.inj (Prod.mk.inj heq).1).1
      cases hnone
  | some selected =>
      rcases selected with ⟨randomness, index, leaves⟩
      have heq := finish_some_support key oracle randomness index leaves _ h
      exact ⟨randomness, index, leaves, rfl, (Prod.mk.inj (Prod.mk.inj heq).1).1.symm,
        (Prod.mk.inj (Prod.mk.inj heq).1).2⟩

private theorem fixedBoundaryRun_signing_selected (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (loop : OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf))))
    (signature : Signature) (view : Option FewTimeView) (trace : SigningBoundaryTrace)
    (hresult : 𝒟[fixedBoundaryRun key.parameter oracle (loop >>= finishSelected key)] ((some signature, view), trace) ≠ 0) :
    ∃ randomness index leaves loopTrace tailTrace,
      𝒟[fixedBoundaryRun key.parameter oracle loop]
        (some (randomness, index, leaves), loopTrace) ≠ 0 ∧
      evalWithAnswerFn oracle (signAfterDigest key randomness index leaves) = some signature ∧
      view = some (selectedFewTimeView index leaves) ∧ trace = loopTrace * tailTrace := by
  obtain ⟨⟨selected, loopTrace⟩, ⟨result, tailTrace⟩, hloop, htail, heq⟩ :=
    fixedBoundaryRun_bind_nonzero key.parameter oracle loop (finishSelected key) _ hresult
  have hreturn : (some signature, view) = result := (Prod.mk.inj heq).1
  rw [← hreturn] at htail
  obtain ⟨randomness, index, leaves, hselected, hsign, hview⟩ := finish_success key oracle selected signature view tailTrace htail
  rw [hselected] at hloop
  exact ⟨randomness, index, leaves, loopTrace, tailTrace, hloop, hsign, hview, (Prod.mk.inj heq).2⟩

theorem fixedBoundaryRun_signing_origin (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (message : Message) (signature : Signature) (view : Option FewTimeView) (trace : SigningBoundaryTrace)
    (hresult : 𝒟[fixedBoundaryRun key.parameter oracle (signWithView key message)] ((some signature, view), trace) ≠ 0) :
    let input := tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness)
    let digest := truncateMessageDigest (oracle input)
    view = some (hashOutputFewTimeView (oracle input)) ∧ Admissible digest ∧
      evalWithAnswerFn oracle (signAfterDigest key signature.randomness (digestIndex digest) (digestLeaves digest)) = some signature ∧
      (input, oracle input) ∈ trace.messageCalls := by
  rw [signWithView_bind] at hresult
  obtain ⟨randomness, index, leaves, loopTrace, tailTrace, hloop, hsign, hview, htrace⟩ :=
    fixedBoundaryRun_signing_selected key oracle (signDigestLoop digestAttemptLimit key message) signature view trace hresult
  have hrandomness := signAfterDigest_some_randomness oracle key randomness index leaves signature hsign
  obtain ⟨hselected, hmem⟩ := fixedBoundaryRun_digest_selected key oracle message digestAttemptLimit randomness index leaves loopTrace hloop
  dsimp only
  rw [hrandomness]
  dsimp only [signAttemptResultOfOutput] at hselected
  split at hselected
  next hadmissible =>
    have hcoords := Prod.mk.inj (Option.some.inj hselected)
    refine ⟨?_, hadmissible, ?_, ?_⟩
    · change view = some (selectedFewTimeView _ _)
      rw [hcoords.1, hcoords.2]
      exact hview
    · rw [hcoords.1, hcoords.2]
      exact hsign
    · rw [htrace, SigningBoundaryTrace.messageCalls_mul, List.mem_append]
      exact Or.inl hmem
  next hadmissible => cases hselected

end SphincsSecurity.Concrete.RetainedResidual
