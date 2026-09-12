import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeFresh
/-!
# Completing an optional fresh signer target

A signer may produce no fresh selected digest. Completing that absent selection with an independent
uniform view keeps the result uniform. This is the optional-candidate form needed by the target
monitor.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

def freshSelectedLoopView?
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : Option FewTimeView :=
  match result.1 with
  | none => none
  | some (randomness, index, leaves) =>
      if referenceCache (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) = none then
        some (selectedFewTimeView index leaves)
      else none

noncomputable def completeFreshSelectedLoopView
    (referenceCache : QueryCache HashSpec) (secretKey : SecretKey) (message : Message)
    (result : Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) : ProbComp FewTimeView :=
  match freshSelectedLoopView? referenceCache secretKey message result with
  | some view => pure view
  | none => $ᵗ FewTimeView

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
theorem probEvent_completeFreshSelectedLoopView_le_uniform
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (referenceCache workingCache : QueryCache HashSpec) (P : FewTimeView → Prop)
    (hinvariant : OnlyRejectedNewMessageEntries referenceCache workingCache secretKey message) :
    Pr[P | (simulateQ romImpl (signDigestLoop attempts secretKey message)).run workingCache >>=
      completeFreshSelectedLoopView referenceCache secretKey message] ≤
      Pr[P | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
  induction attempts generalizing workingCache with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, pure_bind, completeFreshSelectedLoopView,
        freshSelectedLoopView?]
      exact le_rfl
  | succ attempts ih =>
      rw [signDigestLoop_run_succ_eq]
      rw [bind_assoc]
      refine probEvent_bind_le_of_forall_le fun randomness _hrandomness => ?_
      let input := tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)
      by_cases hreference : referenceCache input = none
      · by_cases hworking : workingCache input = none
        · let continuation := signDigestLoopContinuation attempts secretKey message randomness
          have hcoordinates := evalDist_signAttempt_fresh_bind_coordinates
            secretKey message randomness workingCache (by simpa only [input] using hworking)
            continuation
          change Pr[P |
              ((simulateQ randomOracle
                (signAttempt secretKey message randomness :
                  OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run
                workingCache >>= continuation) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message] ≤ _
          have hcoordinates' :
              𝒟[((simulateQ randomOracle
                  (signAttempt secretKey message randomness :
                    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run
                    workingCache >>= continuation) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] =
                𝒟[(do
                  let coordinates ← $ᵗ HashOutputCoordinates
                  let output := hashOutputCoordinatesEquiv.symm coordinates
                  continuation (signAttemptResultOfOutput output,
                    workingCache.cacheQuery input output)) >>=
                    completeFreshSelectedLoopView referenceCache secretKey message] := by
            rw [evalDist_bind, hcoordinates, ← evalDist_bind]
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hcoordinates']
          rw [bind_assoc]
          have hreorder := evalDist_uniformHashOutputCoordinates_bind_reordered
            (fun coordinates =>
              let output := hashOutputCoordinatesEquiv.symm coordinates
              continuation (signAttemptResultOfOutput output,
                workingCache.cacheQuery input output) >>=
                  completeFreshSelectedLoopView referenceCache secretKey message)
          rw [probEvent_congr' (fun _ _ => Iff.rfl) hreorder]
          refine probEvent_bind_le_of_forall_le fun rest _hrest => ?_
          by_cases hadmissible : rest.1 = 0
          · refine (probEvent_bind_le_probEvent (p := P) (q := P) ?_).trans le_rfl
            intro view _hview hnotP
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hsuccessful : signAttemptResultOfOutput output ≠ none := by
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff]
              exact hadmissible
            obtain ⟨indexLeaves, hindexLeaves⟩ := Option.ne_none_iff_exists'.mp hsuccessful
            rcases indexLeaves with ⟨index, leaves⟩
            have hviewEq : selectedFewTimeView index leaves = view :=
              signAttemptResultOfOutput_coordinates_view coordinates index leaves
                (by simpa only [output] using hindexLeaves)
            dsimp only
            rw [show signAttemptResultOfOutput
                (hashOutputCoordinatesEquiv.symm ((view, rest.1), rest.2)) =
                some (index, leaves) by
              simpa only [coordinates, output] using hindexLeaves]
            simp only [continuation, signDigestLoopContinuation, pure_bind]
            rw [completeFreshSelectedLoopView, freshSelectedLoopView?]
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) = none := by
              simpa only [input] using hreference
            simp [hreference', hviewEq, hnotP]
          · refine probEvent_bind_le_of_forall_le fun view _hview => ?_
            let coordinates : HashOutputCoordinates := ((view, rest.1), rest.2)
            let output := hashOutputCoordinatesEquiv.symm coordinates
            have hrejected : signAttemptResultOfOutput output = none := by
              apply Option.eq_none_iff_forall_not_mem.mpr
              intro selected hselected
              have hne : signAttemptResultOfOutput output ≠ none := by
                rw [hselected]
                simp
              rw [signAttemptResultOfOutput_coordinates_ne_none_iff] at hne
              exact hadmissible hne
            have hinvariant' := onlyRejectedNewMessageEntries_cacheRejected
              referenceCache workingCache secretKey message randomness output hinvariant
              hrejected
            simpa only [coordinates, output, continuation, hrejected,
              signDigestLoopContinuation] using
              ih (workingCache.cacheQuery input output) hinvariant'
        · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hworking
          have hrejected := hinvariant randomness output
            (by simpa only [input] using hreference) (by simpa only [input] using houtput)
          rw [bind_assoc]
          refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
          have hle : workingCache ≤ attemptResult.2 :=
            simulateQ_romImpl_cache_le
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) :
                  OracleComp OracleWorld (Option (Index × (IndexGroup → FtsLeaf))))
              workingCache attemptResult (by
                rw [simulateQ_romImpl_liftM]
                exact hattempt)
          have hattemptResult : attemptResult.1 = none :=
            (signAttempt_result_of_cached secretKey message randomness workingCache
              attemptResult.2 attemptResult.1 output
              (hle (by simpa only [input] using houtput)) hattempt).trans hrejected
          have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
            referenceCache workingCache attemptResult.2 secretKey message randomness
            hinvariant (by
              have heq : attemptResult = (none, attemptResult.2) :=
                Prod.ext hattemptResult rfl
              rw [← heq]
              exact hattempt)
          simpa only [hattemptResult, signDigestLoopContinuation] using
            ih attemptResult.2 hinvariant'
      · rw [bind_assoc]
        refine probEvent_bind_le_of_forall_le fun attemptResult hattempt => ?_
        cases hattemptResult : attemptResult.1 with
        | none =>
            have hinvariant' := onlyRejectedNewMessageEntries_of_failed_attempt
              referenceCache workingCache attemptResult.2 secretKey message randomness
              hinvariant (by
                have heq : attemptResult = (none, attemptResult.2) :=
                  Prod.ext hattemptResult rfl
                rw [← heq]
                exact hattempt)
            simpa only [hattemptResult, signDigestLoopContinuation] using
              ih attemptResult.2 hinvariant'
        | some selected =>
            rcases selected with ⟨index, leaves⟩
            have hreference' : referenceCache
                (tweakableHashInput secretKey.parameter .message
                  (messageDigestPayload secretKey.root message randomness)) ≠ none := by
              simpa only [input] using hreference
            simp only [signDigestLoopContinuation, hattemptResult, pure_bind, completeFreshSelectedLoopView,
              freshSelectedLoopView?, if_neg hreference']
            exact le_rfl

end SphincsSecurity.Concrete
