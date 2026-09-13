import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeSampling
namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem signingTraceComputation_bind
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) :
    signingTraceComputation (computation >>= next) = (do
      let left ← signingTraceComputation computation
      let right ← signingTraceComputation (next left.1)
      pure (right.1, left.2 ++ right.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [signingTraceComputation]
  | query_bind input tail ih =>
      simp only [bind_assoc, signingTraceComputation_query_bind, map_eq_bind_pure_comp]
      apply bind_congr
      intro reply
      rw [ih reply]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro left
      apply bind_congr
      intro right
      simp only [List.append_assoc, Function.comp_apply]

theorem signingTraceComputation_liftOracleWorldLeft
    (computation : OracleComp OracleWorld α) :
    signingTraceComputation (liftOracleWorldLeft computation) =
      (fun value => (value, [])) <$> liftOracleWorldLeft computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      have hlift : liftOracleWorldLeft (OracleSpec.query input >>= next) =
          ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl input)) :
            OracleComp (OracleWorld + SigningSpec) _) >>= fun reply => liftOracleWorldLeft (next reply)) := by
        letI directLift : MonadLift (OracleQuery OracleWorld) (OracleQuery (OracleWorld + SigningSpec)) :=
          (OracleQuery.subSpec_add_left (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
        unfold liftOracleWorldLeft
        rw [liftM_bind]
        rfl
      rw [hlift, signingTraceComputation_query_bind, map_bind]
      apply bind_congr
      intro reply
      rw [ih reply]
      simp only [Functor.map_map, signingLogFragment, List.nil_append]

noncomputable def unloggedRetainedRestComputation (adversary : Adversary) (publicKey : PublicKey) :
    OracleComp (OracleWorld + SigningSpec) (Forgery × Bool) := do
  let forgery ← adversary.main publicKey
  let verified ← liftOracleWorldLeft (scheme.verify publicKey forgery.message forgery.signature)
  pure (forgery, verified)

def arrangeRetainedTrace (result : (Forgery × Bool) × QueryLog SigningSpec) : RetainedRestResult :=
  ((result.1.1, result.2), result.1.2)

theorem retainedGameRestComputation_eq_signingTrace
    (adversary : Adversary) (publicKey : PublicKey) :
    retainedGameRestComputation adversary publicKey =
      arrangeRetainedTrace <$> signingTraceComputation (unloggedRetainedRestComputation adversary publicKey) := by
  simp only [retainedGameRestComputation, unloggedRetainedRestComputation, signingTraceComputation_bind, map_bind]
  apply bind_congr
  intro result
  simp only [signingTraceComputation_liftOracleWorldLeft]
  simp [signingTraceComputation, arrangeRetainedTrace]

end SphincsSecurity.Concrete.FtsProbeSimulation
