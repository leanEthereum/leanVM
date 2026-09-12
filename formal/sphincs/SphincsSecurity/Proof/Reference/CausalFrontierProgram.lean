import SphincsSecurity.Proof.Ots.OtsPrefixSimulation
namespace SphincsSecurity.Concrete.CausalFrontierProgram

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

noncomputable def adversaryImpl (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp OracleWorld))
  | .inl input => (QueryImpl.id' OracleWorld).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk (liftM
      (frontierSigningRun parameter root (maskOtsPrefixes parameter words external) ftsSecret words frontier message))

theorem adversaryImpl_signing (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    adversaryImpl parameter root external ftsSecret words frontier (.inr message) =
      WriterT.mk (liftM (frontierSigningRun parameter root (maskOtsPrefixes parameter words external)
        ftsSecret words frontier message) : OracleComp OracleWorld _) := rfl

noncomputable def adversaryRun {Result : Type} (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp OracleWorld ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  (simulateQ (adversaryImpl parameter root external ftsSecret words frontier) (OtsPrefix.logged computation)).run

noncomputable def gameRest (parameter : PublicParameter) (root : Digest)
    (external : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    OracleComp OracleWorld (Bool × SigningBoundaryTrace) := do
  let result ← adversaryRun parameter root external ftsSecret words frontier (adversary.main ⟨root, parameter⟩)
  let checked ← boundaryComputation parameter (liftM
    (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature : OracleComp HashSpec Bool))
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)

noncomputable def game (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : OracleComp OracleWorld (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ 1212415 * result.2)) <$>
    gameRest parameter (frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier)
      external ftsSecret words frontier adversary

theorem worldImpl_lift_prob (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : ProbComp Result) :
    simulateQ (segment.worldImpl high outside) (liftM computation) =
      (liftM computation : OracleComp segment.World Result) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl

theorem prefix_boundary (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : OracleComp OracleWorld Result) :
    simulateQ (segment.worldImpl high outside) (boundaryComputation segment.parameter computation) =
      segment.boundary high outside computation := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply]

theorem prefix_adversaryImpl (segment : OtsPrefix) (root : Digest) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ (segment.worldImpl high outside)
        (adversaryImpl segment.parameter root outside ftsSecret words frontier input).run =
      (segment.adversaryImpl root high outside ftsSecret words frontier input).run := by
  cases input with
  | inl input => simp [adversaryImpl, OtsPrefix.adversaryImpl, QueryImpl.withTrace_apply]
  | inr message =>
      rw [adversaryImpl_signing, OtsPrefix.adversaryImpl_signing, WriterT.run_mk, WriterT.run_mk,
        worldImpl_lift_prob]

theorem prefix_adversaryRun (segment : OtsPrefix) (root : Digest) (high : segment.Query → OtsPrefix.High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (segment.worldImpl high outside)
        (adversaryRun segment.parameter root outside ftsSecret words frontier computation) =
      segment.adversaryRun root high outside ftsSecret words frontier computation :=
  simulateQ_writer_compose _ _ _ (prefix_adversaryImpl segment root high outside ftsSecret words frontier) _

theorem prefix_game (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) :
    simulateQ (segment.worldImpl high outside) (game segment.parameter outside ftsSecret words frontier adversary) =
      segment.game high outside ftsSecret words frontier adversary := by
  simp only [game, simulateQ_map, gameRest, simulateQ_bind, prefix_adversaryRun, prefix_boundary, simulateQ_pure,
    OtsPrefix.game, OtsPrefix.gameRest]

theorem fixed_game (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (fixedHashWorld external) (game parameter external ftsSecret words frontier adversary) =
      frontierGame parameter external ftsSecret words frontier adversary := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let segment : OtsPrefix := ⟨parameter, topLayer, rootTree, 0, chain, words topLayer rootTree 0 chain⟩
  have h := prefix_game segment (segment.highs external) external ftsSecret words frontier adversary
  apply_fun simulateQ (segment.fixedImpl (segment.lows external)) at h
  rw [segment.fixedImpl_game_original external ftsSecret words (by rfl) frontier adversary] at h
  rw [← QueryImpl.simulateQ_compose] at h
  have himpl : (segment.fixedImpl (segment.lows external)).compose
      (segment.worldImpl (segment.highs external) external) = fixedHashWorld external := by
    funext input
    rw [QueryImpl.apply_compose, segment.fixedImpl_worldImpl, segment.answer_original]
  simpa only [himpl] using h

theorem fixed_adversaryRun {Result : Type} (parameter : PublicParameter) (root : Digest) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (fixedHashWorld external) (adversaryRun parameter root external ftsSecret words frontier computation) =
      frontierAdversaryRun parameter root external ftsSecret words frontier computation := by
  let chain : ChainIndex := ⟨0, by decide⟩
  let segment : OtsPrefix := ⟨parameter, topLayer, rootTree, 0, chain, words topLayer rootTree 0 chain⟩
  have h := prefix_adversaryRun segment root (segment.highs external) external ftsSecret words frontier computation
  apply_fun simulateQ (segment.fixedImpl (segment.lows external)) at h
  rw [segment.fixedImpl_adversaryRun _ root _ external ftsSecret words (by rfl) frontier computation,
    segment.answer_original, causalFrontierAdversaryRun_eq] at h
  rw [← QueryImpl.simulateQ_compose] at h
  have himpl : (segment.fixedImpl (segment.lows external)).compose
      (segment.worldImpl (segment.highs external) external) = fixedHashWorld external := by
    funext input
    rw [QueryImpl.apply_compose, segment.fixedImpl_worldImpl, segment.answer_original]
  simpa only [himpl] using h

end SphincsSecurity.Concrete.CausalFrontierProgram
