import SphincsSecurity.Proof.Ots.OtsPrefixOracle
import SphincsSecurity.Proof.Reference.CausalFrontierGame
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

abbrev World (segment : OtsPrefix) := unifSpec + PartialChainEndpoint.PrefixSpec segment.digit.val Digest

noncomputable def fixedImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest) :
    QueryImpl segment.World ProbComp :=
  QueryImpl.id' unifSpec + (fun (query : segment.Query) => pure (tables query.1 query.2) :
    QueryImpl (PartialChainEndpoint.PrefixSpec segment.digit.val Digest) ProbComp)

noncomputable def hashImpl (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) : QueryImpl HashSpec (OracleComp segment.World) :=
  fun bytes => match segment.parse bytes with
    | none => pure (outside bytes)
    | some query => (combine · (high query)) <$> liftM (segment.World.query (.inr query))

noncomputable def worldImpl (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld (OracleComp segment.World)
  | .inl input => liftM (segment.World.query (.inl input))
  | .inr bytes => segment.hashImpl high outside bytes

theorem hashImpl_queryBound (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    (segment.hashImpl high outside bytes).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 1 := by
  cases hparse : segment.parse bytes with
  | none => simp only [hashImpl, hparse, isQueryBoundP_pure]
  | some query =>
      simp only [hashImpl, hparse, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      exact fun _ => Nat.zero_lt_one

theorem lift_prob_queryBound (segment : OtsPrefix) {Result : Type} (computation : ProbComp Result) :
    (liftM computation : OracleComp segment.World Result).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, isQueryBoundP_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change ((liftM (segment.World.query (.inl input)) >>= fun answer => liftM (next answer)) :
        OracleComp segment.World Result).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0
      simp only [isQueryBoundP_query_bind_iff, PartialChainEndpoint.IsPrefixQuery, not_false_eq_true,
        true_or, ↓reduceIte, true_and]
      exact ih

theorem fixedImpl_lift_prob (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Result : Type} (computation : ProbComp Result) :
    simulateQ (segment.fixedImpl tables) (liftM computation) = computation := by
  rw [fixedImpl, QueryImpl.simulateQ_add_liftM_left, simulateQ_id']

private theorem fixedImpl_lift_prob_congr (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Parameter Result : Type} (work : Parameter → ProbComp Result) (first second : Parameter) (h : first = second) :
    simulateQ (segment.fixedImpl tables) (liftM (work first)) = work second :=
  (segment.fixedImpl_lift_prob tables (work first)).trans (congrArg work h)

theorem fixedImpl_hashImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    simulateQ (segment.fixedImpl tables) (segment.hashImpl high outside bytes) =
      pure (segment.answer tables high outside bytes) := by
  cases hparse : segment.parse bytes with
  | none => simp only [hashImpl, answer, hparse, simulateQ_pure]
  | some query =>
      simp only [hashImpl, answer, hparse, simulateQ_map, simulateQ_spec_query]
      rfl

theorem fixedImpl_worldImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    simulateQ (segment.fixedImpl tables) (segment.worldImpl high outside input) =
      fixedHashWorld (segment.answer tables high outside) input := by
  cases input with
  | inl input => rw [worldImpl, simulateQ_spec_query]; rfl
  | inr bytes => exact segment.fixedImpl_hashImpl tables high outside bytes

noncomputable def boundary (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) {Result : Type} (computation : OracleComp OracleWorld Result) :
    OracleComp segment.World (Result × SigningBoundaryTrace) :=
  (simulateQ ((segment.worldImpl high outside).withTrace (signingBoundaryTrace segment.parameter)) computation).run

theorem fixedImpl_boundary (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id) {Result : Type}
    (computation : OracleComp OracleWorld Result) :
    simulateQ (segment.fixedImpl tables) (segment.boundary high outside computation) =
      fixedBoundaryRun segment.parameter (segment.answer tables high outside) computation := by
  apply simulateQ_writer_compose
  intro input
  simp [QueryImpl.withTrace_apply, segment.fixedImpl_worldImpl tables high outside input]

noncomputable def adversaryImpl (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace (OracleComp segment.World))
  | .inl input => (segment.worldImpl high outside).withTrace (signingBoundaryTrace segment.parameter) input
  | .inr message => WriterT.mk (liftM
      (frontierSigningRun segment.parameter root (maskOtsPrefixes segment.parameter words outside)
        ftsSecret words frontier message))

theorem adversaryImpl_signing (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    segment.adversaryImpl root high outside ftsSecret words frontier (.inr message) =
      WriterT.mk (liftM (frontierSigningRun segment.parameter root (maskOtsPrefixes segment.parameter words outside)
        ftsSecret words frontier message) : OracleComp segment.World _) := rfl

private theorem causalFrontierAdversaryImpl_signing (parameter : PublicParameter) (root : Digest)
    (oracle : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (message : Message) :
    causalFrontierAdversaryImpl parameter root oracle ftsSecret words frontier (.inr message) =
      WriterT.mk (frontierSigningRun parameter root (maskOtsPrefixes parameter words oracle) ftsSecret words frontier message) := rfl

theorem fixedImpl_adversaryImpl (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ (segment.fixedImpl tables)
        (segment.adversaryImpl root high outside ftsSecret words frontier input).run =
      (causalFrontierAdversaryImpl segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier input).run := by
  cases input with
  | inl input =>
      simp [adversaryImpl, causalFrontierAdversaryImpl, QueryImpl.withTrace_apply,
        segment.fixedImpl_worldImpl tables high outside input]
  | inr message =>
      rw [adversaryImpl_signing, causalFrontierAdversaryImpl_signing, WriterT.run_mk, WriterT.run_mk]
      exact fixedImpl_lift_prob_congr segment tables
        (fun oracle => frontierSigningRun segment.parameter root oracle ftsSecret words frontier message) _ _
        (segment.mask_answer words hword tables high outside).symm

noncomputable def logged {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp (OracleWorld + SigningSpec) (Result × QueryLog SigningSpec) :=
  (simulateQ ((QueryImpl.id' (OracleWorld + SigningSpec)).withTraceAppend signingLogFragment) computation).run

noncomputable def adversaryRun (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    OracleComp segment.World ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  (simulateQ (segment.adversaryImpl root high outside ftsSecret words frontier) (logged computation)).run

theorem fixedImpl_adversaryRun (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (segment.fixedImpl tables) (segment.adversaryRun root high outside ftsSecret words frontier computation) =
      causalFrontierAdversaryRun segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier computation := by
  rw [adversaryRun, simulateQ_writer_compose _ _ _
    (segment.fixedImpl_adversaryImpl tables root high outside ftsSecret words hword frontier)]
  unfold logged causalFrontierAdversaryRun
  congr 1
  apply simulateQ_writerAppend_compose
  intro input
  simp [QueryImpl.withTraceAppend_apply]

noncomputable def gameRest (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    OracleComp segment.World (Bool × SigningBoundaryTrace) := do
  let result ← segment.adversaryRun root high outside ftsSecret words frontier (adversary.main ⟨root, segment.parameter⟩)
  let checked ← segment.boundary high outside (liftM
    (verify ⟨root, segment.parameter⟩ result.1.1.message result.1.1.signature : OracleComp HashSpec Bool))
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)

theorem fixedImpl_gameRest (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (root : Digest) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (segment.gameRest root high outside ftsSecret words frontier adversary) =
      causalFrontierGameRest segment.parameter root (segment.answer tables high outside)
        ftsSecret words frontier adversary := by
  simp only [gameRest, simulateQ_bind, segment.fixedImpl_adversaryRun tables root high outside ftsSecret words hword frontier]
  unfold causalFrontierGameRest
  apply bind_congr
  intro result
  rw [fixedImpl_boundary, fixedBoundaryRun_lift_hash, pure_bind, simulateQ_pure]

noncomputable def game (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : OracleComp segment.World (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ 1212415 * result.2)) <$>
    segment.gameRest (frontierRoot segment.parameter (maskOtsPrefixes segment.parameter words outside) words frontier)
      high outside ftsSecret words frontier adversary

theorem fixedImpl_game (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl tables) (segment.game high outside ftsSecret words frontier adversary) =
      frontierGame segment.parameter (segment.answer tables high outside) ftsSecret words frontier adversary := by
  rw [game, simulateQ_map, fixedImpl_gameRest segment tables _ high outside ftsSecret words hword frontier,
    ← causalFrontierGame_eq, causalFrontierGame, segment.mask_answer words hword tables high outside]

theorem fixedImpl_game_original (segment : OtsPrefix) (oracle : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (hword : segment.digit.val ≤ (words segment.lay segment.tree segment.leaf segment.chainIdx).val)
    (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (segment.fixedImpl (segment.lows oracle))
        (segment.game (segment.highs oracle) oracle ftsSecret words frontier adversary) =
      frontierGame segment.parameter oracle ftsSecret words frontier adversary := by
  rw [fixedImpl_game segment _ _ _ ftsSecret words hword frontier adversary, answer_original]

end SphincsSecurity.Concrete.OtsPrefix
