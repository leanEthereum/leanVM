import SphincsSecurity.Proof.Forced.SecretGuessObservation
import SphincsSecurity.Proof.Reference.ReferenceAuxiliarySigning
import SphincsSecurity.Proof.Base.UniformTableProducts
namespace SphincsSecurity.Concrete.FtsGuessSigning

open _root_.OracleComp OracleSpec SecretGuessObservation CanonicalProbeRouting UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition

abbrev Coordinate := Index × FtsTree × FtsLeaf

def secretTable : (Index → FtsTree → FtsLeaf → Digest) ≃ (Coordinate → Digest) where
  toFun secrets coordinate := secrets coordinate.1 coordinate.2.1 coordinate.2.2
  invFun table index tree leaf := table (index, tree, leaf)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sampleFtsSecrets_table : secretTable <$> 𝒟[sampleFtsSecrets] =
    complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) := by
  rw [sampleFtsSecrets, evalDist_uniformSample, complete_of_nonempty _ (fun _ => Finset.univ_nonempty), uniformTable_univ]
  have h := congrArg (fun law : PMF (Coordinate → Digest) => 𝒟[law])
    (PMF.uniformOfFintype_map_of_bijective secretTable secretTable.bijective)
  simpa only [← PMF.monad_map_eq_map, evalDist_map] using h

variable {AuxIndex Memory : Type} {auxSpec : OracleSpec AuxIndex}

def completeRecord (record : PublicSigningRecord) :
    OracleComp (World auxSpec Coordinate Digest) ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) :=
  match record.1.1, record.1.2 with
  | some plan, some view => do
      let secrets ← sequenceFin fun tree => disclosure (view.1, tree, view.2 tree)
      pure ((some (plan.finish secrets), some view), record.2)
  | _, _ => pure ((none, record.1.2), record.2)

def completedState (environment : Environment auxSpec Coordinate Digest Memory) (labels : Coordinate → Digest)
    (record : PublicSigningRecord) (state : State Coordinate Digest Memory) : State Coordinate Digest Memory :=
  match record.1.1, record.1.2 with
  | some _, some view => disclosureSequenceState environment labels (fun tree => (view.1, tree, view.2 tree)) state
  | _, _ => state

theorem completedState_counts (environment : Environment auxSpec Coordinate Digest Memory) (labels : Coordinate → Digest)
    (record : PublicSigningRecord) (state : State Coordinate Digest Memory) :
    ((completedState environment labels record state).guesses,
      (completedState environment labels record state).probes) = (state.guesses, state.probes) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan with
  | none => rfl
  | some plan =>
      cases view with
      | none => rfl
      | some view => exact disclosureSequenceState_counts environment labels (fun tree : FtsTree => (view.1, tree, view.2 tree)) state

theorem fixedRun_completeRecord (environment : Environment auxSpec Coordinate Digest Memory) (labels : Coordinate → Digest)
    (record : PublicSigningRecord) (state : State Coordinate Digest Memory) :
    fixedRun environment labels (completeRecord record) state =
      pure (completePublicSigningRecord (fun index tree leaf => labels (index, tree, leaf)) record,
        completedState environment labels record state) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan <;> cases view <;> simp only [completeRecord, completePublicSigningRecord, completedState,
    Option.map_none, Option.map_some]
  all_goals first
    | exact runWith_pure (fixedImpl environment labels) _ _
    | rw [fixedRun_disclosureSequence_bind]; exact runWith_pure (fixedImpl environment labels) _ _

noncomputable def nativeRun (environment : Environment auxSpec Coordinate Digest Memory) (labels : Coordinate → Digest)
    (state : State Coordinate Digest Memory) (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    SPMF (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest Memory) :=
  𝒟[publicSigningRecord parameter root outside known words selections message] >>= fun record =>
    fixedRun environment labels (completeRecord record) state

noncomputable def lazySigningRun (environment : Environment auxSpec Coordinate Digest Memory)
    (state : State Coordinate Digest Memory) (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    SPMF (((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest Memory) :=
  𝒟[publicSigningRecord parameter root outside known words selections message] >>= fun record =>
    lazyRun environment (completeRecord record) state

theorem nativeRun_erasure (environment : Environment auxSpec Coordinate Digest Memory) (labels : Coordinate → Digest)
    (state : State Coordinate Digest Memory) (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    Prod.fst <$> nativeRun environment labels state parameter root outside known words selections message =
      𝒟[completePublicSigningRecord (fun index tree leaf => labels (index, tree, leaf)) <$>
        publicSigningRecord parameter root outside known words selections message] := by
  simp only [nativeRun, fixedRun_completeRecord, map_eq_bind_pure_comp, evalDist_bind, evalDist_pure,
    bind_assoc, pure_bind, Function.comp_def]

theorem nativeRun_original (environment : Environment auxSpec Coordinate Digest Memory)
    (state : State Coordinate Digest Memory) (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    Prod.fst <$> nativeRun environment (fun coordinate => key.ftsSecret coordinate.1 coordinate.2.1 coordinate.2.2) state
        key.parameter key.root
        (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding known auxiliary.rows auxiliary.seed))
        known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message =
      𝒟[fixedBoundaryRun key.parameter
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        (signWithView key message)] := by
  rw [nativeRun_erasure,
    fixedBoundaryRun_signWithView_auxiliary_public key inputs hencoding labels auxiliary hauxiliary dummy disclosed known hagrees message]

theorem signingRun_erasure (environment : Environment auxSpec Coordinate Digest Memory)
    (state : State Coordinate Digest Memory) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (parameter : PublicParameter) (root : Digest) (outside : QueryImpl HashSpec Id)
    (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily) (message : Message) :
    (complete state.allowed >>= fun labels => nativeRun environment labels state parameter root outside known words selections message) =
      lazySigningRun environment state parameter root outside known words selections message := by
  simp only [nativeRun, lazySigningRun]
  rw [RetainedObservation.bind_comm]
  exact congrArg (𝒟[publicSigningRecord parameter root outside known words selections message] >>= ·)
    (funext fun record => run_erasure environment (completeRecord record) state ha)

end SphincsSecurity.Concrete.FtsGuessSigning
