import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeAdversary

/-! ## FtsProbeStablePrefixQueries -/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def liftHashSource (computation : OracleComp HashSpec α) : OracleComp (OracleWorld + SigningSpec) α :=
  simulateQ (fun input => (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
    OracleComp (OracleWorld + SigningSpec) HashOutput)) computation

theorem liftHashSource_query_bind (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    liftHashSource ((liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput) >>= next) =
      ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl (.inr input))) :
        OracleComp (OracleWorld + SigningSpec) HashOutput) >>= fun output => liftHashSource (next output)) := by
  rw [liftHashSource, simulateQ_bind, simulateQ_spec_query]
  rfl

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem liftOracleWorldLeft_query_bind
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    liftOracleWorldLeft (OracleSpec.query input >>= next) =
      ((liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (.inl input)) :
        OracleComp (OracleWorld + SigningSpec) _) >>= fun reply => liftOracleWorldLeft (next reply)) := by
  letI directLift : MonadLift (OracleQuery OracleWorld) (OracleQuery (OracleWorld + SigningSpec)) :=
    (OracleQuery.subSpec_add_left (spec₁ := OracleWorld) (spec₂ := SigningSpec)).toMonadLift
  unfold liftOracleWorldLeft
  rw [liftM_bind]
  rfl

theorem liftHashSource_eq_liftOracleWorldLeft (computation : OracleComp HashSpec α) :
    liftHashSource computation = liftOracleWorldLeft (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      have hworld : (liftM ((liftM (OracleSpec.query (spec := HashSpec) input) : OracleComp HashSpec HashOutput) >>= next) :
          OracleComp OracleWorld α) =
          ((liftM (OracleSpec.query (spec := OracleWorld) (.inr input)) : OracleComp OracleWorld HashOutput) >>=
            fun reply => liftM (next reply)) := by
        letI directLift : MonadLift (OracleQuery HashSpec) (OracleQuery OracleWorld) :=
          (OracleQuery.subSpec_add_right (spec₁ := unifSpec) (spec₂ := HashSpec)).toMonadLift
        rw [liftM_bind]
        rfl
      rw [liftHashSource_query_bind, hworld, liftOracleWorldLeft_query_bind]
      exact bind_congr ih

theorem liftOracleWorldLeft_scheme_verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    liftOracleWorldLeft (scheme.verify publicKey message signature) =
      liftHashSource (verify (m := OracleComp HashSpec) publicKey message signature) := by
  rw [liftHashSource_eq_liftOracleWorldLeft]
  rfl

end SphincsSecurity.Concrete.FtsProbeSimulation
