import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalSigningFrontier
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk referenceEncodingSearch signDigestLoop

noncomputable def fixedHashWorld (f : QueryImpl HashSpec Id) : QueryImpl OracleWorld ProbComp
  | .inl input => liftM (unifSpec.query input)
  | .inr input => pure (f input)

noncomputable def fixedBoundaryRun {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) : ProbComp (α × SigningBoundaryTrace) :=
  (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter)) computation).run

theorem fixedBoundaryRun_pure {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (value : α) :
    fixedBoundaryRun parameter f (pure value) = pure (value, 1) := rfl

theorem fixedBoundaryRun_bind {α β : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) :
    fixedBoundaryRun parameter f (first >>= next) =
      fixedBoundaryRun parameter f first >>= fun result =>
        (fun final => (final.1, result.2 * final.2)) <$> fixedBoundaryRun parameter f (next result.1) := by
  simp only [fixedBoundaryRun, simulateQ_bind, WriterT.run_bind]

theorem fixedBoundaryRun_map {α β : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (g : α → β) :
    fixedBoundaryRun parameter f (g <$> computation) =
      (Prod.map g id) <$> fixedBoundaryRun parameter f computation := by
  simp only [fixedBoundaryRun, simulateQ_map, WriterT.run_map]
  rfl

theorem fixedBoundaryRun_forget {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    Prod.fst <$> fixedBoundaryRun parameter f computation = simulateQ (fixedHashWorld f) computation :=
  QueryImpl.fst_map_run_withTrace (fixedHashWorld f) (signingBoundaryTrace parameter) computation

theorem fixedBoundaryRun_lift_hash {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    fixedBoundaryRun parameter f (liftM computation) = pure (boundaryEval parameter f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [liftM_pure, fixedBoundaryRun_pure, boundaryEval_pure]
  | query_bind input next ih =>
      rw [liftM_bind, fixedBoundaryRun_bind, boundaryEval_bind, boundaryEval_hash_query]
      have hquery : fixedBoundaryRun parameter f
          (liftM (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput)) =
          pure (f input, signingBoundaryTrace parameter (.inr input) (f input)) := by
        change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
          (liftM (OracleWorld.query (.inr input)))).run = _
        rw [simulateQ_spec_query]
        rfl
      rw [hquery, pure_bind, ih, map_pure]
      rfl

def publicSignAttempt (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest parameter root message randomness
  if Admissible digest then pure (some (digestIndex digest, digestLeaves digest)) else pure none

noncomputable def publicDigestLoop (parameter : PublicParameter) (root : Digest) (message : Message) :
    Nat → OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0 => pure none
  | attempts + 1 => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM (publicSignAttempt parameter root message randomness)
      match attempt with
      | none => publicDigestLoop parameter root message attempts
      | some (index, leaves) => pure (some (randomness, index, leaves))

theorem publicDigestLoop_eq (key : SecretKey) (message : Message) (attempts : Nat) :
    publicDigestLoop key.parameter key.root message attempts = signDigestLoop attempts key message := by
  induction attempts with
  | zero => rw [publicDigestLoop, signDigestLoop]
  | succ attempts ih =>
      rw [publicDigestLoop, signDigestLoop]
      apply bind_congr
      intro randomness
      have hattempt : publicSignAttempt key.parameter key.root message randomness =
          (signAttempt key message randomness : OracleComp HashSpec _) := rfl
      rw [hattempt]
      apply bind_congr
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected => rfl

noncomputable def frontierSigningRecord (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (message : Message) :
    ProbComp ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) := do
  let selected ← fixedBoundaryRun parameter f (publicDigestLoop parameter root message digestAttemptLimit)
  match selected.1 with
  | none => pure ((none, none), selected.2)
  | some (randomness, index, leaves) =>
      let result := frontierSignAfterDigest parameter f ftsSecret words frontier randomness index leaves
      pure ((result.1, some (selectedFewTimeView index leaves)), selected.2 * (FreeMonoid.of none) ^ result.2)

theorem fixedBoundaryRun_signWithView_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (message : Message) :
    fixedBoundaryRun key.parameter f (signWithView key message) =
      frontierSigningRecord key.parameter key.root f key.ftsSecret words frontier message := by
  rw [signWithView, fixedBoundaryRun_bind, frontierSigningRecord, publicDigestLoop_eq]
  apply bind_congr
  rintro ⟨selected, trace⟩
  cases selected with
  | none => simp only [fixedBoundaryRun_pure, map_pure, mul_one]
  | some selected =>
      obtain ⟨randomness, index, leaves⟩ := selected
      rw [fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash,
        boundaryEval_signAfterDigest_frontier key f words frontier hfrontier randomness index leaves (hwords index)]
      simp only [pure_bind, fixedBoundaryRun_pure, map_pure, mul_one]

theorem fixedBoundaryRun_signWithView_canonical (key : SecretKey) (f : QueryImpl HashSpec Id)
    (dummy : OtsReferenceWords) (message : Message) :
    fixedBoundaryRun key.parameter f (signWithView key message) =
      frontierSigningRecord key.parameter key.root f key.ftsSecret (canonicalReferenceWords key f dummy)
        (canonicalFrontierValues key f (canonicalReferenceWords key f dummy)) message :=
  fixedBoundaryRun_signWithView_frontier key f _ _ (isSigningFrontier_canonical key f _)
    (frontierReferenceWord_canonical key f dummy) message

noncomputable def frontierSigningRun (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (message : Message) : ProbComp (Option Signature × SigningBoundaryTrace) :=
  (Prod.map Prod.fst id) <$> frontierSigningRecord parameter root f ftsSecret words frontier message

theorem fixedBoundaryRun_sign_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (message : Message) :
    fixedBoundaryRun key.parameter f (sign key message) =
      frontierSigningRun key.parameter key.root f key.ftsSecret words frontier message := by
  rw [← signWithView_fst, fixedBoundaryRun_map, fixedBoundaryRun_signWithView_frontier key f words frontier hfrontier hwords]
  rfl

end SphincsSecurity.Concrete
