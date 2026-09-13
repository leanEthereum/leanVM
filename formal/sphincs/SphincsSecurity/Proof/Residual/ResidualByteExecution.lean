import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualByteFrontend
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

noncomputable def executeResult (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) :
    Action inputs → Option HashOutput × State inputs
  | .known answer => (some answer, state)
  | .read input => (some (seed input), AdaptiveResidualLabels.readState
      (environment parameter inputs words disclosed known actions) state input (seed input))
  | .probe input test =>
      match state.rows input with
      | some answer => (some answer, AdaptiveResidualLabels.readState
          (environment parameter inputs words disclosed known actions) state input answer)
      | none => if test.keep actual (seed input) then
          (some (seed input), AdaptiveResidualLabels.probeState
            (environment parameter inputs words disclosed known actions) state input test (seed input))
        else (none, AdaptiveResidualLabels.stoppedState
          (environment parameter inputs words disclosed known actions) state input test)

theorem observedRun_execute (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) (action : Action inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (execute action) state = pure (executeResult parameter inputs words disclosed known actions actual seed state action) := by
  cases action with
  | known answer =>
      simp only [execute, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith_pure, executeResult]
  | read input =>
      simp only [execute, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
        AdaptiveResidualLabels.observedImpl, OptionT.run_mk, StateT.run_mk, executeResult]
  | probe input test =>
      simp only [execute, AdaptiveResidualLabels.observedRun, AdaptiveResidualLabels.runWith, simulateQ_spec_query,
        AdaptiveResidualLabels.observedImpl, OptionT.run_mk, StateT.run_mk, executeResult]
      dsimp only [OracleSpec.Range, World, AdaptiveResidualLabels.World, OracleSpec.add_apply_inr,
        AdaptiveResidualLabels.ResidualSpec]
      cases hrow : state.rows input with
      | none => by_cases hkeep : test.keep actual (seed input) <;> simp only [hkeep, if_true, if_false]
      | some answer => rfl

noncomputable def hashQueryResult (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    Option HashOutput × State inputs :=
  let prepared := prepare parameter inputs words disclosed known actions input state.memory
  executeResult parameter inputs words disclosed known actions actual seed { state with memory := prepared.2 } prepared.1

theorem observedRun_hashQuery (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    AdaptiveResidualLabels.observedRun (environment parameter inputs words disclosed known actions) actual seed
      (hashQuery input) state = pure (hashQueryResult parameter inputs words disclosed known actions actual seed input state) := by
  rw [hashQuery, observedRun_prepare_bind, observedRun_execute]
  rfl

omit parameter words disclosed known actions in
noncomputable def delivered (input : inputs) (memory : ExternalMemory) (answer : Option HashOutput) : ExternalMemory :=
  answer.elim memory (fun answer => storeReply memory input.val answer)

noncomputable def publicCachedReply (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (memory : ExternalMemory) :
    Option HashOutput :=
  (memory.cache input.val).elim
    (ResidualByteAction.eval actual seed (actions input)) some

theorem hashQueryResult_project (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs)
    (hcovered : RowsCovered inputs state) (hlocal : Local input (actions input)) :
    let result := hashQueryResult parameter inputs words disclosed known actions actual seed input state
    let answer := publicCachedReply inputs actions actual seed input state.memory
    (result.1, result.2.memory) = (answer, delivered inputs input
      (charge parameter words disclosed known input.val state.memory) answer) := by
  dsimp only
  cases hcache : state.memory.cache input.val with
  | some answer =>
      simp only [hashQueryResult, prepare, hcache, executeResult, publicCachedReply, Option.elim_some, delivered]
      congr 1
      unfold storeReply charge
      simp only [← hcache, Function.update_eq_self]
  | none =>
      have hrow := rowsCovered_fresh inputs state hcovered input hcache
      simp only [hashQueryResult, prepare, hcache, publicCachedReply, Option.elim_none]
      cases haction : actions input with
      | known answer => rfl
      | read row =>
          have heq : row = input := by simpa only [haction, Local] using hlocal
          subst row
          rfl
      | probe row test =>
          have heq : row = input := by simpa only [haction, Local] using hlocal
          subst row
          simp only [executeResult, hrow, ResidualByteAction.eval]
          split <;> rfl

theorem hashQueryResult_hashCalls (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    (hashQueryResult parameter inputs words disclosed known actions actual seed input state).2.memory.hashCalls =
      state.memory.hashCalls + 1 := by
  have h := prepare_hashCalls parameter inputs words disclosed known actions input state.memory
  unfold hashQueryResult
  generalize hprepared : prepare parameter inputs words disclosed known actions input state.memory = prepared at *
  rcases prepared with ⟨action, memory⟩
  cases action with
  | known answer => exact h
  | read input => exact h
  | probe input test =>
      dsimp only [executeResult]
      cases hrow : state.rows input with
      | none =>
          dsimp only
          split <;> exact h
      | some answer =>
          dsimp only
          exact h

omit parameter words disclosed known actions in
theorem rowsCovered_store (state : State inputs) (hcovered : RowsCovered inputs state)
    (candidates : CanonicalCoordinate → Finset Digest) (input : inputs) (answer : HashOutput) :
    RowsCovered inputs ⟨candidates, Function.update state.rows input (some answer), storeReply state.memory input.val answer⟩ := by
  intro other output hrow
  dsimp only at hrow
  by_cases heq : other = input
  · subst other
    simp only [Function.update_self, Option.some.injEq] at hrow
    subst output
    exact Function.update_self ..
  · have hval : other.val ≠ input.val := fun h => heq (Subtype.ext h)
    rw [Function.update_of_ne heq] at hrow
    exact (Function.update_of_ne hval _ _).trans (hcovered other output hrow)

omit parameter words disclosed known actions in
theorem rowsCovered_store_public (state : State inputs) (hcovered : RowsCovered inputs state)
    (input : inputs) (hfresh : state.rows input = none) (answer : HashOutput) :
    RowsCovered inputs { state with memory := storeReply state.memory input.val answer } := by
  intro other output hrow
  by_cases heq : other = input
  · subst other
    rw [hfresh] at hrow
    cases hrow
  · have hval : other.val ≠ input.val := fun h => heq (Subtype.ext h)
    exact (Function.update_of_ne hval _ _).trans (hcovered other output hrow)

theorem prepare_rowsCovered (state : State inputs) (hcovered : RowsCovered inputs state) (input : inputs) :
    RowsCovered inputs { state with memory :=
      (prepare parameter inputs words disclosed known actions input state.memory).2 } := by
  unfold prepare
  cases hcache : state.memory.cache input.val with
  | some answer => exact hcovered
  | none =>
      have hrow := rowsCovered_fresh inputs state hcovered input hcache
      cases actions input with
      | known answer =>
          exact rowsCovered_store_public inputs
            { state with memory := charge parameter words disclosed known input.val state.memory } hcovered input hrow answer
      | read _ => exact hcovered
      | probe _ _ => exact hcovered

theorem executeResult_rowsCovered (actual : Labels) (seed : inputs → HashOutput) (state : State inputs)
    (hcovered : RowsCovered inputs state) (action : Action inputs) :
    RowsCovered inputs
      (executeResult parameter inputs words disclosed known actions actual seed state action).2 := by
  cases action with
  | known answer => exact hcovered
  | read input => exact rowsCovered_store inputs state hcovered state.candidates input (seed input)
  | probe input test =>
      simp only [executeResult]
      cases hrow : state.rows input with
      | some answer => exact rowsCovered_store inputs state hcovered state.candidates input answer
      | none =>
          dsimp only
          split
          · exact rowsCovered_store inputs state hcovered (test.restrict state.candidates (seed input)) input (seed input)
          · exact hcovered

theorem hashQueryResult_rowsCovered (actual : Labels) (seed : inputs → HashOutput) (state : State inputs)
    (hcovered : RowsCovered inputs state) (input : inputs) :
    RowsCovered inputs
      (hashQueryResult parameter inputs words disclosed known actions actual seed input state).2 :=
  executeResult_rowsCovered parameter inputs words disclosed known actions actual seed _
    (prepare_rowsCovered parameter inputs words disclosed known actions state hcovered input) _

end SphincsSecurity.Concrete.ResidualByteFrontend
