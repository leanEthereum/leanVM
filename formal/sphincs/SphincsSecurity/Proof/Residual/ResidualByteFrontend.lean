import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.AdaptiveResidualLabels
import SphincsSecurity.Proof.Hypertree.CanonicalProbeCache
import SphincsSecurity.Proof.Residual.ResidualByteAction
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

inductive Control (inputs : Finset HashInput) where
  | prepare (input : inputs)
  | random (input : unifSpec.Domain)
  | account (cost : Nat)
  | stop

abbrev ControlSpec (inputs : Finset HashInput) : OracleSpec (Control inputs)
  | .prepare _ => Action inputs
  | .random input => unifSpec.Range input
  | .account _ => Unit
  | .stop => HashOutput

abbrev World (inputs : Finset HashInput) := AdaptiveResidualLabels.World (ControlSpec inputs) CanonicalCoordinate inputs
abbrev State (inputs : Finset HashInput) := AdaptiveResidualLabels.State CanonicalCoordinate inputs ExternalMemory

noncomputable def execute {inputs : Finset HashInput} : Action inputs → OracleComp (World inputs) HashOutput
  | .known answer => pure answer
  | .read input => liftM ((World inputs).query (.inr (.read input)))
  | .probe input test => liftM ((World inputs).query (.inr (.probe input test)))

noncomputable def hashQuery {inputs : Finset HashInput} (input : inputs) : OracleComp (World inputs) HashOutput := do
  let action ← liftM ((World inputs).query (.inl (.prepare input)))
  execute action

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

noncomputable def prepare (input : inputs) (memory : ExternalMemory) : Action inputs × ExternalMemory :=
  let paid := charge parameter words disclosed known input.val memory
  match memory.cache input.val with
  | some answer => (.known answer, paid)
  | none =>
      let action := actions input
      match action with
      | .known answer => (action, storeReply paid input.val answer)
      | _ => (action, paid)

noncomputable def environment : AdaptiveResidualLabels.Environment (ControlSpec inputs) CanonicalCoordinate inputs ExternalMemory where
  auxiliary state input := match input with
    | .prepare input =>
        let prepared := prepare parameter inputs words disclosed known actions input state.memory
        PMF.pure (some prepared.1, prepared.2)
    | .random input => (PMF.uniformOfFintype (unifSpec.Range input)).map (fun answer => (some answer, state.memory))
    | .account cost => PMF.pure (some (), { state.memory with hashCalls := state.memory.hashCalls + cost })
    | .stop => PMF.pure (none, state.memory)
  rowAnswer memory input answer := storeReply memory input.val answer
  probeAnswer memory input _ answer := storeReply memory input.val answer
  probeStop memory _ _ := memory
  disclosure memory _ _ := memory

omit parameter words disclosed known actions in
def RowsCovered (state : State inputs) : Prop :=
  ∀ input answer, state.rows input = some answer → state.memory.cache input.val = some answer

omit parameter words disclosed known actions in
theorem rowsCovered_fresh (state : State inputs) (hcovered : RowsCovered inputs state) (input : inputs)
    (hfresh : state.memory.cache input.val = none) : state.rows input = none := by
  cases hrow : state.rows input with
  | none => rfl
  | some answer =>
      have h := hcovered input answer hrow
      rw [hfresh] at h
      cases h

theorem prepare_cached (input : inputs) (memory : ExternalMemory) (answer : HashOutput)
    (hcache : memory.cache input.val = some answer) :
    prepare parameter inputs words disclosed known actions input memory =
      (.known answer, charge parameter words disclosed known input.val memory) := by
  simp only [prepare, hcache]

theorem prepare_hashCalls (input : inputs) (memory : ExternalMemory) :
    (prepare parameter inputs words disclosed known actions input memory).2.hashCalls = memory.hashCalls + 1 := by
  unfold prepare
  cases memory.cache input.val with
  | some answer => rfl
  | none => cases actions input <;> rfl

theorem observedRun_prepare_bind {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (next : Action inputs → OracleComp (World inputs) Result) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (liftM ((World inputs).query (.inl (.prepare input))) >>= next) state =
        let prepared := prepare parameter inputs words disclosed known actions input state.memory
        AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
          (next prepared.1) { state with memory := prepared.2 } := by
  rw [AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_query_bind]
  simp only [AdaptiveResidualLabels.observedImpl, environment, OptionT.run_mk, StateT.run_mk,
    SPMF.lift_pure, pure_bind, Option.elim_some, AdaptiveResidualLabels.observedRun]

end SphincsSecurity.Concrete.ResidualByteFrontend
