import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteCorrespondence
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

noncomputable def translate (inputs : Finset HashInput) : QueryImpl OracleWorld (OracleComp (World inputs))
  | .inl input => liftM ((World inputs).query (.inl (.random input)))
  | .inr input => if hin : input ∈ inputs then hashQuery ⟨input, hin⟩ else pure (0 : HashOutput)

noncomputable def byteRun {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp OracleWorld Result) (state : State inputs) : SPMF (Option Result × State inputs) :=
  AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
    actual seed (simulateQ (translate inputs) computation) state

theorem observedRun_bind {A B : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (World inputs) A) (next : A → OracleComp (World inputs) B) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
      actual seed (computation >>= next) state =
        (AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
          actual seed computation state >>= fun result =>
            result.1.elim (pure (none, result.2)) (fun answer =>
              AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions)
                actual seed (next answer) result.2)) := by
  simp only [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_bind,
    OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (fun continuation =>
    (simulateQ (AdaptiveResidualLabels.observedImpl
      (environment parameter inputs words disclosed known actions) actual seed) computation).run.run state >>= continuation)
  funext result
  rcases result with ⟨answer, state⟩
  cases answer <;> rfl

theorem byteRun_pure {Result : Type} (actual : Labels) (seed : inputs → HashOutput) (value : Result) (state : State inputs) :
    byteRun parameter inputs words disclosed known actions actual seed (pure value) state =
      pure (some value, state) := by
  simp only [byteRun, simulateQ_pure, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure]

end SphincsSecurity.Concrete.ResidualByteFrontend
