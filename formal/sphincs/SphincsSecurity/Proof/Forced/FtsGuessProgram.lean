import SphincsSecurity.Proof.Forced.FtsGuessHash
import SphincsSecurity.Proof.Reference.ReferenceForgerySource
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun frontierRoot maskOtsPrefixes boundaryEval

noncomputable def signingProgram (message : Message) :
    OracleComp World ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let record ← liftM (World.query (.inl (.inr message)))
  FtsGuessSigning.completeRecord record

theorem fixed_completeRecord (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest)
    (record : PublicSigningRecord) :
    simulateQ (fixedAnswers auxiliary secrets) (FtsGuessSigning.completeRecord record) =
      pure (completePublicSigningRecord (FtsGuessSigning.secretTable.symm secrets) record) := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan <;> cases view <;>
    simp only [FtsGuessSigning.completeRecord, completePublicSigningRecord, Option.map_none, Option.map_some,
      simulateQ_pure, simulateQ_bind, fixedAnswers, SecretGuessObservation.fixedAnswers_disclosureSequence, pure_bind]
  rfl

theorem fixed_signingProgram (auxiliary : QueryImpl Auxiliary ProbComp) (secrets : Coordinate → Digest)
    (message : Message) :
    simulateQ (fixedAnswers auxiliary secrets) (signingProgram message) =
      completePublicSigningRecord (FtsGuessSigning.secretTable.symm secrets) <$> auxiliary (.inr message) := by
  simp only [signingProgram, simulateQ_bind, simulateQ_spec_query, fixed_completeRecord,
    fixedAnswers, SecretGuessObservation.fixedAnswers, bind_pure_comp]

abbrev Traced (m : Type → Type) := WriterT SigningBoundaryTrace (WriterT Trace m)

noncomputable def adversaryImpl (parameter : PublicParameter) (labels : CanonicalGraphLabels) :
    QueryImpl (OracleWorld + SigningSpec) (Traced (OracleComp World))
  | .inl input => WriterT.mk (WriterT.mk ((fun answer =>
      ((answer, signingBoundaryTrace parameter input answer), hashObservationTrace input answer)) <$>
        worldProgram parameter labels input))
  | .inr message => WriterT.mk (WriterT.mk ((fun record => ((record.1.1, record.2), 1)) <$> signingProgram message))

noncomputable def adversaryRun {Result : Type} (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp World (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) :=
  ((simulateQ (adversaryImpl parameter labels) (OtsPrefix.logged computation)).run).run

noncomputable def nativeImpl (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (signer : Message → ProbComp (Option Signature × SigningBoundaryTrace)) :
    QueryImpl (OracleWorld + SigningSpec) (Traced ProbComp)
  | .inl input => WriterT.mk (WriterT.mk ((fun answer =>
      ((answer, signingBoundaryTrace parameter input answer), hashObservationTrace input answer)) <$> fixedHashWorld f input))
  | .inr message => WriterT.mk (WriterT.mk ((fun record => (record, 1)) <$> signer message))

private theorem simulateQ_two_writers {ι₁ ι₂ Result ω₁ ω₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m] [Monoid ω₁] [Monoid ω₂]
    (first : QueryImpl spec₁ (WriterT ω₁ (WriterT ω₂ (OracleComp spec₂)))) (second : QueryImpl spec₂ m)
    (combined : QueryImpl spec₁ (WriterT ω₁ (WriterT ω₂ m)))
    (hquery : ∀ input, simulateQ second ((first input).run).run = ((combined input).run).run)
    (computation : OracleComp spec₁ Result) :
    simulateQ second ((simulateQ first computation).run).run = ((simulateQ combined computation).run).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, WriterT.run_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        simulateQ_map, hquery]
      apply bind_congr
      rintro ⟨⟨answer, first⟩, second⟩
      rw [ih]

theorem fixed_adversaryImpl (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) ((adversaryImpl parameter labels input).run).run =
      ((nativeImpl parameter (programmedHash parameter otsSecret ftsSecret labels residual)
        (fun message => (Prod.map Prod.fst id) <$>
          (completePublicSigningRecord ftsSecret <$> signer message)) input).run).run := by
  cases input with
  | inl input =>
      simp only [adversaryImpl, nativeImpl, WriterT.run_mk, simulateQ_map]
      rw [FtsGuessHash.fixed_worldProgram parameter otsSecret ftsSecret labels residual signer input]
  | inr message =>
      simp only [adversaryImpl, nativeImpl, WriterT.run_mk, simulateQ_map, fixed_signingProgram, auxiliaryAnswers,
        Functor.map_map]
      rfl

theorem fixed_adversaryRun {Result : Type} (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) (adversaryRun parameter labels computation) =
      ((simulateQ (nativeImpl parameter (programmedHash parameter otsSecret ftsSecret labels residual)
        (fun message => (Prod.map Prod.fst id) <$>
          (completePublicSigningRecord ftsSecret <$> signer message))) (OtsPrefix.logged computation)).run).run :=
  simulateQ_two_writers _ _ _ (fixed_adversaryImpl parameter otsSecret ftsSecret labels residual signer) _

private theorem fixedTrace_query (f : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    fixedTrace f (liftM (OracleWorld.query input)) =
      (fun answer => (answer, hashObservationTrace input answer)) <$> fixedHashWorld f input := by
  simp [fixedTrace, QueryPause.traced, QueryImpl.withTrace_apply]

private theorem fixedTrace_lift_prob {Result : Type} (f : QueryImpl HashSpec Id) (computation : ProbComp Result) :
    fixedTrace f (liftM computation) = (fun answer => (answer, (1 : Trace))) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, fixedTrace_pure, map_pure]
  | query_bind input next ih =>
      rw [liftM_bind, fixedTrace_bind]
      change (fixedTrace f (liftM (OracleWorld.query (.inl input))) >>= _) = _
      rw [fixedTrace_query]
      simp only [hashObservationTrace, fixedHashWorld, ih, Functor.map_map, map_bind]
      rw [map_eq_bind_pure_comp, bind_assoc]
      simp only [Function.comp_def, pure_bind, one_mul]
      rfl

private theorem fixedTrace_writer {Result : Type}
    (f : QueryImpl HashSpec Id)
    (first : QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp OracleWorld)))
    (second : QueryImpl (OracleWorld + SigningSpec) (Traced ProbComp))
    (hquery : ∀ input, fixedTrace f (first input).run = ((second input).run).run)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    fixedTrace f (simulateQ first computation).run = ((simulateQ second computation).run).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, WriterT.run_pure, fixedTrace_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        fixedTrace_bind, fixedTrace_map, hquery]
      apply bind_congr
      rintro ⟨⟨answer, first⟩, second⟩
      simp only [ih, Functor.map_map]

noncomputable def sourceImpl (parameter : PublicParameter)
    (signer : Message → ProbComp (Option Signature × SigningBoundaryTrace)) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp OracleWorld))
  | .inl input => (QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk (liftM (signer message))

private theorem native_sourceQuery (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (signer : Message → ProbComp (Option Signature × SigningBoundaryTrace)) (input : (OracleWorld + SigningSpec).Domain) :
    fixedTrace f (sourceImpl parameter signer input).run = ((nativeImpl parameter f signer input).run).run := by
  cases input with
  | inl input =>
      have h : (sourceImpl parameter signer (.inl input)).run =
          (fun answer => (answer, signingBoundaryTrace parameter input answer)) <$> liftM (OracleWorld.query input) := by
        simp [sourceImpl, QueryImpl.withTrace_apply]
      rw [h, fixedTrace_map, fixedTrace_query]
      simp only [nativeImpl, WriterT.run_mk, Functor.map_map]
      rfl
  | inr message => exact fixedTrace_lift_prob f (signer message)

theorem native_adversaryRun {Result : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    fixedTrace f (CausalFrontierProgram.adversaryRun parameter root f ftsSecret words frontier computation) =
      ((simulateQ (nativeImpl parameter f
        (frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier))
        (OtsPrefix.logged computation)).run).run :=
  fixedTrace_writer f (sourceImpl parameter
    (frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier)) _
    (native_sourceQuery parameter f _) (OtsPrefix.logged computation)

noncomputable def verifyProgram (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (forgery : Forgery) : OracleComp World ((Bool × SigningBoundaryTrace) × Trace) :=
  simulateQ (worldProgram parameter labels) (QueryPause.traced hashObservationTrace
    (boundaryComputation parameter (liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature : OracleComp HashSpec Bool))))

theorem fixed_verifyProgram (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (signer : QueryImpl SigningRecordSpec ProbComp) (forgery : Forgery) :
    simulateQ (fixedAnswers (auxiliaryAnswers parameter otsSecret labels residual signer)
      (FtsGuessSigning.secretTable ftsSecret)) (verifyProgram parameter root labels forgery) =
      pure (boundaryEval parameter (programmedHash parameter otsSecret ftsSecret labels residual)
        (verify ⟨root, parameter⟩ forgery.message forgery.signature),
        answerTrace (programmedHash parameter otsSecret ftsSecret labels residual)
          (verify ⟨root, parameter⟩ forgery.message forgery.signature)) := by
  rw [verifyProgram, fixed_world_translate]
  exact fixedTrace_boundary_hash parameter _ _

noncomputable def completedRun (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (adversary : Adversary) : OracleComp World (AdversaryTrace × (Bool × SigningBoundaryTrace) × Trace) := do
  let before ← adversaryRun parameter labels (adversary.main ⟨root, parameter⟩)
  let checked ← verifyProgram parameter root labels before.1.1.1
  pure (before, checked)

end SphincsSecurity.Concrete.FtsGuessHash
