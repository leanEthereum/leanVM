import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteRun
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def checkedResult {Memory : Type} (reject : HashInput → HashOutput → Prop) (input : HashInput)
    (result : Option HashOutput × Memory) : Option HashOutput × Memory :=
  (result.1.bind (fun answer => if reject input answer then none else some answer), result.2)

noncomputable def checkedHashQuery {inputs : Finset HashInput} (reject : HashInput → HashOutput → Prop)
    (input : inputs) : OracleComp (World inputs) HashOutput := do
  let answer ← hashQuery input
  if reject input.val answer then liftM ((World inputs).query (.inl .stop)) else pure answer

noncomputable def checkedTranslate (inputs : Finset HashInput) (reject : HashInput → HashOutput → Prop) :
    QueryImpl OracleWorld (OracleComp (World inputs))
  | .inl input => liftM ((World inputs).query (.inl (.random input)))
  | .inr input => if hin : input ∈ inputs then checkedHashQuery reject ⟨input, hin⟩ else pure (0 : HashOutput)

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem observedRun_stop (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (liftM ((World inputs).query (.inl .stop)) : OracleComp (World inputs) HashOutput) state = pure (none, state) := by
  simp only [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
    AdaptiveResidualLabels.observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind]

theorem observedRun_checkedHashQuery (reject : HashInput → HashOutput → Prop) (actual : Labels)
    (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (checkedHashQuery reject input) state =
        pure (checkedResult reject input.val (hashQueryResult parameter inputs words disclosed known actions actual seed input state)) := by
  rw [checkedHashQuery, observedRun_bind, observedRun_hashQuery, pure_bind]
  generalize hresult : hashQueryResult parameter inputs words disclosed known actions actual seed input state = result
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => rfl
  | some answer =>
      dsimp only [Option.elim_some, checkedResult, Option.bind_some]
      by_cases hreject : reject input.val answer
      · simp only [if_pos hreject, observedRun_stop]
      · simp only [if_neg hreject, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure]

end SphincsSecurity.Concrete.ResidualByteFrontend
