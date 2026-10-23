import Sphincs.StatementDet
import Sphincs.BridgeAssembly

/-! Internalizing long adversarial hash inputs for the deterministic-randomizer game, and its
fixed-function form. `Seeded.sign` only makes short queries (its randomizer derivation is 88
bytes), so the argument of `BridgeInternalize` applies verbatim with `signingOracleDet`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Det

open Completeness SeedCoupling Short Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem randomizerHashInput_length (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) :
    (randomizerHashInput parameter seed message).length = 96 := by
  simp [randomizerHashInput, fieldBytes_length, bytesLE_length]

theorem randomizerHashInput_short (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) :
    IsShort (randomizerHashInput parameter seed message) := by
  simp only [IsShort, bound, randomizerHashInput_length]
  omega

theorem Only.deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) :
    Only (Sphincs.deriveRandomizer parameter seed message : OracleComp HashSpec Randomness) := by
  unfold Sphincs.deriveRandomizer
  exact Only.bind (Only.query (randomizerHashInput_short _ _ _)) (fun _ => Only.pure' _)

variable [Params]

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit Randomized.finishSign
  Sphincs.Seeded.signAttempt

theorem Only.seededLoop (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    ∀ attempts randomness, Only (Sphincs.Seeded.signDigestLoop sk message attempts randomness :
      OracleComp HashSpec (Option (Randomness × Index)))
  | 0, _ => Only.pure' _
  | attempts + 1, randomness => by
      rw [Sphincs.Seeded.signDigestLoop]
      refine Only.bind (Short.Seeded.Only.signAttempt _ _ _) (fun result => ?_)
      cases result with
      | none => exact Only.seededLoop sk message attempts (randomness + 1)
      | some _ => exact Only.pure' _

/-- The deterministic signer is the randomizer derivation, the scan, and the common assembly. -/
theorem seededSign_eq (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    (Sphincs.Seeded.sign sk message : OracleComp HashSpec (Option Signature)) = (do
      let base ← Sphincs.deriveRandomizer sk.parameter sk.seed message
      let some (randomness, _) ← Sphincs.Seeded.signDigestLoop sk message digestAttemptLimit base
        | return none
      Randomized.finishSign sk message randomness) := by
  unfold Sphincs.Seeded.sign Randomized.finishSign
  rfl

theorem Only.seededSign (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    Only (Sphincs.Seeded.sign sk message : OracleComp HashSpec (Option Signature)) := by
  rw [seededSign_eq]
  refine Only.bind (Only.deriveRandomizer _ _ _) (fun base => ?_)
  refine Only.bind (Only.seededLoop sk message _ _) (fun result => ?_)
  rcases result with _ | ⟨randomness, _⟩
  · exact Only.pure' _
  · exact Short.Only.finishSign _ _ _

theorem OnlyW.seededSign (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    OnlyW (liftM (Sphincs.Seeded.sign sk message : OracleComp HashSpec (Option Signature)) :
      OracleComp OracleWorld (Option Signature)) :=
  OnlyW.liftHash (Only.seededSign sk message)

/-! ### The Block relation for the deterministic signing oracle -/

noncomputable def gameImplDet (sk : Sphincs.Seeded.SecretKey) :
    QueryImpl AdvSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
    signingOracleDet sk

noncomputable def leftProgD (sk : Sphincs.Seeded.SecretKey) {β : Type}
    (M : OracleComp AdvSpec β) : OracleComp OracleWorld (β × QueryLog SigningSpec) :=
  (simulateQ (gameImplDet sk) M).run

noncomputable def rightProgD (sk : Sphincs.Seeded.SecretKey) {β : Type}
    (M : OracleComp AdvSpec β) (long : QueryCache HashSpec) :
    OracleComp OracleWorld ((β × QueryCache HashSpec) × QueryLog SigningSpec) :=
  (simulateQ (gameImplDet sk) ((simulateQ internalImpl M).run long)).run

theorem leftProgD_bind (sk : Sphincs.Seeded.SecretKey) {β γ : Type} (M : OracleComp AdvSpec β)
    (k : β → OracleComp AdvSpec γ) :
    leftProgD sk (M >>= k) = leftProgD sk M >>= fun first =>
      (fun second => (second.1, first.2 ++ second.2)) <$> leftProgD sk (k first.1) := by
  simp only [leftProgD, simulateQ_bind, WriterT.run_bind]

theorem rightProgD_bind (sk : Sphincs.Seeded.SecretKey) {β γ : Type} (M : OracleComp AdvSpec β)
    (k : β → OracleComp AdvSpec γ) (long : QueryCache HashSpec) :
    rightProgD sk (M >>= k) long = rightProgD sk M long >>= fun first =>
      (fun second => (second.1, first.2 ++ second.2)) <$> rightProgD sk (k first.1.1) first.1.2 := by
  simp only [rightProgD, simulateQ_bind, StateT.run_bind, WriterT.run_bind]

def BlockD (sk : Sphincs.Seeded.SecretKey) {β : Type} (M : OracleComp AdvSpec β) : Prop :=
  ∀ short long, (leftView <$> leftRun (leftProgD sk M) (merge short long)) =ᵈ (rightView <$> rightRun (rightProgD sk M long) short)

theorem BlockD.bind {sk : Sphincs.Seeded.SecretKey} {β γ : Type} {M : OracleComp AdvSpec β}
    {k : β → OracleComp AdvSpec γ} (hM : BlockD sk M) (hk : ∀ value, BlockD sk (k value)) :
    BlockD sk (M >>= k) := by
  intro short long
  rw [leftProgD_bind, rightProgD_bind, leftRun_bind, rightRun_bind, map_bind, map_bind]
  let combine : (β × QueryLog SigningSpec) × Nat × QueryCache HashSpec →
      (γ × QueryLog SigningSpec) × Nat × QueryCache HashSpec →
      (γ × QueryLog SigningSpec) × Nat × QueryCache HashSpec :=
    fun first second => ((second.1.1, first.1.2 ++ second.1.2), first.2.1 + second.2.1, second.2.2)
  refine evalDist_bind_rel _ _ leftView rightView (hM short long) _ _
    (fun first => combine first <$> (leftView <$> leftRun (leftProgD sk (k first.1.1)) first.2.2))
    (fun first => ?_) (fun first => ?_)
  · simp only [leftRun_map, Functor.map_map]
    rfl
  · simp only [rightRun_map, Functor.map_map]
    exact evalDist_map_rel _ _ rightView leftView (hk first.1.1.1.1 first.2 first.1.1.1.2).symm
      (combine (rightView first)) _ _ (fun _ => rfl) (fun _ => rfl)

theorem BlockD.pure' (sk : Sphincs.Seeded.SecretKey) {β : Type} (value : β) :
    BlockD sk (pure value : OracleComp AdvSpec β) := by
  intro short long
  simp only [leftProgD, rightProgD, simulateQ_pure, StateT.run_pure, WriterT.run_pure, leftRun,
    rightRun, countShort, countHashQueries, SphincsBase.QueryCap.counted_pure,
    StateT.run_pure, map_pure]
  rfl

theorem rightProgD_forward (sk : Sphincs.Seeded.SecretKey) (input : AdvSpec.Domain)
    (hforward : internalImpl input = forward input) (long : QueryCache HashSpec) :
    rightProgD sk (liftM (AdvSpec.query input)) long =
      (fun result => ((result.1, long), result.2)) <$> leftProgD sk (liftM (AdvSpec.query input)) := by
  simp only [rightProgD, leftProgD, simulateQ_spec_query, hforward]
  change (simulateQ (gameImplDet sk) ((fun answer => (answer, long)) <$>
      (liftM (AdvSpec.query input) : OracleComp AdvSpec _))).run = _
  rw [simulateQ_map, simulateQ_spec_query, WriterT.run_map]

theorem BlockD.forward (sk : Sphincs.Seeded.SecretKey) (input : AdvSpec.Domain)
    (hforward : internalImpl input = forward input)
    (honly : OnlyW (gameImplDet sk input).run) :
    BlockD sk (liftM (AdvSpec.query input)) := by
  intro short long
  rw [rightProgD_forward sk input hforward long, rightRun_map, Functor.map_map]
  have hleft : leftProgD sk (liftM (AdvSpec.query input)) = (gameImplDet sk input).run := by
    simp only [leftProgD, simulateQ_spec_query]
  rw [hleft, leftRun_short _ honly short long, Functor.map_map]
  rfl

theorem BlockD.draw (sk : Sphincs.Seeded.SecretKey) (draw : unifSpec.Domain) :
    BlockD sk (liftM (AdvSpec.query (.inl (.inl draw)))) :=
  BlockD.forward sk _ rfl (by
    change OnlyW (liftM (liftM (OracleWorld.query (.inl draw)) : OracleComp OracleWorld _) :
      WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run
    exact OnlyW.writerLift (OnlyW.queryDraw draw))

theorem BlockD.short (sk : Sphincs.Seeded.SecretKey) {input : HashInput} (h : IsShort input) :
    BlockD sk (liftM (AdvSpec.query (.inl (.inr input)))) :=
  BlockD.forward sk _ (by simp only [internalImpl, h, ↓reduceIte]) (by
    change OnlyW (liftM (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _) :
      WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run
    exact OnlyW.writerLift (OnlyW.queryShort h))

theorem OnlyW.signingDet (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    OnlyW (signingOracleDet sk message).run := by
  simp only [Det.signingOracleDet, QueryImpl.run_withLogging_apply]
  exact OnlyW.bind (OnlyW.seededSign sk message) (fun _ => OnlyW.pure' _)

theorem BlockD.signing (sk : Sphincs.Seeded.SecretKey) (message : Message) :
    BlockD sk (liftM (AdvSpec.query (.inr message))) :=
  BlockD.forward sk _ rfl (by
    change OnlyW (signingOracleDet sk message).run
    exact OnlyW.signingDet sk message)

theorem gameImplDet_liftWorld (sk : Sphincs.Seeded.SecretKey) {α : Type}
    (x : OracleComp OracleWorld α) :
    (simulateQ (gameImplDet sk) (liftWorld x)).run = (fun value => (value, ∅)) <$> x := by
  rw [liftWorld, ← QueryImpl.simulateQ_compose]
  have himpl : (gameImplDet sk ∘ₛ liftWorldImpl) =
      QueryImpl.ofLift OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) := by
    funext t
    change simulateQ (gameImplDet sk) (liftM (AdvSpec.query (Sum.inl t))) = _
    rw [simulateQ_spec_query]
    rfl
  rw [himpl, run_simulateQ_ofLift_writer]

theorem BlockD.long (sk : Sphincs.Seeded.SecretKey) {input : HashInput} (h : ¬IsShort input) :
    BlockD sk (liftM (AdvSpec.query (.inl (.inr input)))) := by
  intro short long
  have hleft : leftProgD sk (liftM (AdvSpec.query (.inl (.inr input)))) =
      (fun answer => (answer, ∅)) <$>
        (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _) := by
    simp only [leftProgD, simulateQ_spec_query]
    change (liftM (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _) :
      WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run = _
    rw [WriterT.run_liftM]
  have hlookup : merge short long input = long input := by simp [merge, h]
  rw [hleft, leftRun_map]
  have hint : simulateQ internalImpl (liftM (AdvSpec.query (.inl (.inr input))) : OracleComp AdvSpec _) =
      privateRead input := by
    rw [simulateQ_spec_query]
    simp only [internalImpl, h, ↓reduceIte]
  unfold rightProgD
  rw [hint]
  cases hc : long input with
  | some answer =>
      have hread : (privateRead input).run long = pure (answer, long) := by
        simp only [StateT.run, privateRead, hc]
      rw [hread]
      simp only [leftRun, countShort, rightRun, countHashQueries, simulateQ_pure, WriterT.run_pure,
        SphincsBase.QueryCap.counted_pure, StateT.run_pure, map_pure]
      rw [PreparedScheme.counted_query, simulateQ_map, simulateQ_spec_query, StateT.run_map]
      change _ <$> (_ <$> (_ <$> (randomOracle (spec := HashSpec) input).run (merge short long))) =ᵈ _
      rw [QueryImpl.withCaching_run_some _ (hlookup.trans hc)]
      simp [leftView, rightView, ShortQuery, h]
  | none =>
      have hread : (privateRead input).run long =
          (fun answer => (answer, long.cacheQuery input answer)) <$>
            liftWorld (liftM ($ᵗ HashOutput : ProbComp HashOutput) : OracleComp OracleWorld HashOutput) := by
        simp only [StateT.run, privateRead, hc]
      rw [hread, simulateQ_map, WriterT.run_map, gameImplDet_liftWorld, Functor.map_map, rightRun_map,
        rightRun_map, rightRun_liftProb, Functor.map_map, Functor.map_map, leftRun_longQuery h,
        QueryImpl.withCaching_run_none _ (hlookup.trans hc)]
      simp only [Functor.map_map]
      have hsample : (uniformSampleImpl (spec := HashSpec) input : ProbComp HashOutput) =ᵈ ($ᵗ HashOutput : ProbComp HashOutput) := by
        exact EvalDistEq.rfl
      refine evalDist_map_congr_of_evalDist_eq _ _ hsample _ _ (fun answer => ?_)
      simp only [leftView, rightView, merge_cacheQuery_long short long h]

theorem BlockD.query (sk : Sphincs.Seeded.SecretKey) (input : AdvSpec.Domain) :
    BlockD sk (liftM (AdvSpec.query input)) := by
  rcases input with (draw | bytes) | message
  · exact BlockD.draw sk draw
  · by_cases h : IsShort bytes
    · exact BlockD.short sk h
    · exact BlockD.long sk h
  · exact BlockD.signing sk message

theorem blockD_all (sk : Sphincs.Seeded.SecretKey) {β : Type} (M : OracleComp AdvSpec β) :
    BlockD sk M := by
  induction M using OracleComp.inductionOn with
  | pure value => exact BlockD.pure' sk value
  | query_bind input next ih => exact (BlockD.query sk input).bind ih

/-! ### The whole deterministic game -/

theorem leftProgD_internal (sk : Sphincs.Seeded.SecretKey) {β : Type} (M : OracleComp AdvSpec β) :
    leftProgD sk ((simulateQ internalImpl M).run' ∅) =
      (fun result => (result.1.1, result.2)) <$> rightProgD sk M ∅ := by
  simp only [leftProgD, rightProgD, StateT.run'_eq, simulateQ_map, WriterT.run_map]

/-- The deterministic game after its seed sample: the key's seed `S0`. -/
noncomputable def gameAfterSeedDet (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← liftM (Sphincs.Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracleDet sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The deterministic game after the scheme seed: key generation from `S`. -/
noncomputable def gameAfterMasterDet (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← liftM (Sphincs.Seeded.keygenFromMaster seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracleDet sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The deterministic game with a uniform scheme seed `S` in place of `H(leanSPHINCS || S0)`. -/
noncomputable def gameCoreMasterDet (adversary : Adversary) : OracleComp OracleWorld Bool :=
  (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= gameAfterMasterDet adversary

noncomputable def experimentMasterDet (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCoreMasterDet adversary)).run.run' ∅

/-- The game after `S0` hashes `S0` once, then plays the game after the scheme seed. -/
theorem gameAfterSeedDet_eq_master (adversary : Adversary) (seed : MasterSeed) :
    gameAfterSeedDet adversary seed =
      (liftM (schemeSeed seed : OracleComp HashSpec MasterSeed) : OracleComp OracleWorld MasterSeed) >>=
        gameAfterMasterDet adversary := by
  simp only [gameAfterSeedDet, Sphincs.Seeded.keygenFromSeed, liftM_bind, bind_assoc]
  rfl

theorem gameCoreDet_eq_sampling (adversary : Adversary) :
    gameCoreDet adversary = (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>=
      gameAfterSeedDet adversary := rfl

theorem gameAfterSeedDet_eq (adversary : Adversary) (seed : MasterSeed) :
    gameAfterSeedDet adversary seed = (liftM (Sphincs.Seeded.keygenFromSeed seed) :
      OracleComp OracleWorld _) >>= fun keys =>
        leftProgD keys.2 (adversary.main keys.1) >>= verifyPart keys.1 := rfl

theorem restD_rel (adversary : Adversary) (keys : PublicKey × Sphincs.Seeded.SecretKey)
    (short : QueryCache HashSpec) :
    ((fun result => result.1) <$>
        leftRun (leftProgD keys.2 (adversary.main keys.1) >>= verifyPart keys.1) (merge short ∅)) =ᵈ ((fun result => result.1) <$>
        rightRun (leftProgD keys.2 ((internalize adversary).main keys.1) >>= verifyPart keys.1) short) := by
  rw [show (internalize adversary).main keys.1 =
      (simulateQ internalImpl (adversary.main keys.1)).run' ∅ from rfl, leftProgD_internal,
    leftRun_bind, rightRun_bind, map_bind, map_bind]
  simp only [rightRun_map, bind_map_left]
  refine evalDist_bind_rel _ _ leftView rightView (blockD_all keys.2 _ short ∅) _ _
    (fun first => (fun second => (second.1.1, first.2.1 + second.1.2)) <$>
      leftRun (verifyPart keys.1 first.1) first.2.2) (fun first => ?_) (fun first => ?_)
  · simp only [Functor.map_map]
    rfl
  · simp only [Functor.map_map]
    change _ =ᵈ _ <$> leftRun (verifyPart keys.1 (first.1.1.1.1, first.1.1.2))
      (merge first.2 first.1.1.1.2)
    rw [leftRun_short _ (OnlyW.verifyPart _ _), Functor.map_map]
    rfl

theorem gameAfterSeedDet_rel (adversary : Adversary) (seed : MasterSeed) (short : QueryCache HashSpec) :
    ((fun result => result.1) <$> leftRun (gameAfterSeedDet adversary seed) (merge short ∅)) =ᵈ ((fun result => result.1) <$> rightRun (gameAfterSeedDet (internalize adversary) seed) short) := by
  rw [gameAfterSeedDet_eq, gameAfterSeedDet_eq, leftRun_bind, rightRun_bind, map_bind, map_bind]
  refine evalDist_bind_rel _ _ id (fun result => (result.1, merge result.2 ∅))
    (by rw [leftRun_short _ (OnlyW.liftHash (Short.Seeded.Only.keygenFromSeed seed)), Functor.map_map]
        rfl) _ _
    (fun first => (fun second => (second.1.1, first.1.2 + second.1.2)) <$>
      leftRun (leftProgD first.1.1.2 (adversary.main first.1.1.1) >>= verifyPart first.1.1.1) first.2)
    (fun first => ?_) (fun first => ?_)
  · simp only [Functor.map_map]
    rfl
  · simp only [Functor.map_map]
    have h := (restD_rel adversary first.1.1 first.2).symm
    exact evalDist_map_rel
      (rightRun (leftProgD first.1.1.2 ((internalize adversary).main first.1.1.1) >>=
        verifyPart first.1.1.1) first.2)
      (leftRun (leftProgD first.1.1.2 (adversary.main first.1.1.1) >>= verifyPart first.1.1.1)
        (merge first.2 ∅))
      (fun result => result.1) (fun result => result.1) h
      (fun inner : Bool × Nat => (inner.1, first.1.2 + inner.2))
      (fun a => (a.1.1, first.1.2 + a.1.2)) (fun a => (a.1.1, first.1.2 + a.1.2))
      (fun _ => rfl) (fun _ => rfl)

theorem experimentDet_eq_rightRun (adversary : Adversary) :
    experimentDet adversary = (fun result => result.1) <$> rightRun (gameCoreDet adversary) ∅ := by
  rw [experimentDet, rightRun, ← simulateQ_countHashQueries]
  rfl

theorem evalDist_experimentDet_internalize (adversary : Adversary) :
    experimentDet (internalize adversary) =ᵈ ((fun result => result.1) <$> leftRun (gameCoreDet adversary) ∅) := by
  rw [experimentDet_eq_rightRun, gameCoreDet_eq_sampling, gameCoreDet_eq_sampling,
    show leftRun ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>=
      gameAfterSeedDet adversary) ∅ = leftRun ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>=
      gameAfterSeedDet adversary) (merge ∅ ∅) by rw [merge_empty],
    leftRun_bind, rightRun_bind, map_bind, map_bind]
  symm
  refine evalDist_bind_rel _ _ id (fun result => (result.1, merge result.2 ∅))
    (by rw [leftRun_short _ (OnlyW.liftProb _), Functor.map_map]; rfl) _ _
    (fun first => (fun second => (second.1.1, first.1.2 + second.1.2)) <$>
      leftRun (gameAfterSeedDet adversary first.1.1) first.2)
    (fun first => ?_) (fun first => ?_)
  · simp only [Functor.map_map]
    rfl
  · simp only [Functor.map_map]
    have h := (gameAfterSeedDet_rel adversary first.1.1 first.2).symm
    exact evalDist_map_rel
      (rightRun (gameAfterSeedDet (internalize adversary) first.1.1) first.2)
      (leftRun (gameAfterSeedDet adversary first.1.1) (merge first.2 ∅))
      (fun result => result.1) (fun result => result.1) h
      (fun inner : Bool × Nat => (inner.1, first.1.2 + inner.2))
      (fun a => (a.1.1, first.1.2 + a.1.2)) (fun a => (a.1.1, first.1.2 + a.1.2))
      (fun _ => rfl) (fun _ => rfl)

section Budgeted

attribute [local irreducible] experimentDet count2 leftRun rightRun sampleMasterSeed

/-- Internalizing long inputs never lowers the probability of a budgeted win. -/
theorem budgetedWin_le_internalize (adversary : Adversary) (q : Nat) :
    Pr{let result ← experimentDet adversary}[result.1 = true ∧ result.2 ≤ q] ≤
      Pr{let result ← experimentDet (internalize adversary)}[result.1 = true ∧ result.2 ≤ q] := by
  rw [(evalDist_experimentDet_internalize adversary).prEvent_eq,
    experimentDet_eq_rightRun, leftRun_eq_split, rightRun_eq_split, prEvent_map, prEvent_map,
    prEvent_map, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun result _ hresult => ⟨hresult.1, ?_⟩
  exact le_trans (Nat.le_add_right _ _) hresult.2

end Budgeted

/-! ### The internalized deterministic game only queries short inputs; its fixed-function form -/

theorem OnlyW.gameImplDet (sk : Sphincs.Seeded.SecretKey) {β : Type} (M : OracleComp AdvSpec β)
    (h : OnlyAdv M) : OnlyW (simulateQ (gameImplDet sk) M).run := by
  induction M using OracleComp.inductionOn with
  | pure value => simp [OnlyW]
  | query_bind input next ih =>
      rw [OnlyAdv, isQueryBoundP_query_bind_iff] at h
      have hnext : ∀ answer, OnlyAdv (next answer) := fun answer => by
        have := h.2 answer
        split at this <;> simpa [OnlyAdv] using this
      rw [simulateQ_bind, WriterT.run_bind]
      refine OnlyW.bind ?_ (fun result => OnlyW.map _ (ih result.1 (hnext result.1)))
      rw [simulateQ_spec_query]
      rcases input with (draw | bytes) | message
      · change OnlyW (liftM (liftM (OracleWorld.query (.inl draw)) : OracleComp OracleWorld _) :
          WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run
        exact OnlyW.writerLift (OnlyW.queryDraw draw)
      · have hshort : IsShort bytes := by
          rcases h.1 with hnot | hzero
          · simpa [LongAdv] using hnot
          · omega
        change OnlyW (liftM (liftM (OracleWorld.query (.inr bytes)) : OracleComp OracleWorld _) :
          WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run
        exact OnlyW.writerLift (OnlyW.queryShort hshort)
      · change OnlyW (signingOracleDet sk message).run
        exact OnlyW.signingDet sk message

theorem OnlyW.gameAfterSeedDet_internalize (adversary : Adversary) (seed : MasterSeed) :
    OnlyW (gameAfterSeedDet (internalize adversary) seed) := by
  rw [gameAfterSeedDet_eq]
  refine OnlyW.bind (OnlyW.liftHash (Short.Seeded.Only.keygenFromSeed seed)) (fun keys => ?_)
  refine OnlyW.bind ?_ (fun output => OnlyW.verifyPart _ _)
  exact OnlyW.gameImplDet keys.2 _ (OnlyAdv.map _ (OnlyAdv.internal _ _))

theorem OnlyW.gameAfterMasterDet_internalize (adversary : Adversary) (seed : MasterSeed) :
    OnlyW (gameAfterMasterDet (internalize adversary) seed) := by
  refine OnlyW.bind (OnlyW.liftHash (Short.Seeded.Only.keygenFromMaster seed)) (fun keys => ?_)
  refine OnlyW.bind ?_ (fun output => OnlyW.verifyPart _ _)
  exact OnlyW.gameImplDet keys.2 _ (OnlyAdv.map _ (OnlyAdv.internal _ _))

open SeedModel Graph Assembly Eager in
noncomputable local instance detLabelsSampleable : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

open SeedModel Graph Assembly Eager in
/-- The internalized deterministic experiment from a uniform scheme seed as an average of
fixed-function counted games. -/
theorem evalDist_experimentMasterDet_fixed (adversary : Adversary) :
    experimentMasterDet (internalize adversary) =ᵈ (do
      let material ← sampleMaterial
      let seed ← sampleMasterSeed
      let answers ← $ᵗ CanonicalGraphLabels
      let table ← $ᵗ Eager.Table
      simulateQ (fixedRom (extend (preparedCache material seed answers) table))
        (countHashQueries (gameAfterMasterDet (internalize adversary) seed))) := by
  rw [experimentMasterDet, gameCoreMasterDet]
  refine (evalDist_seeded_prepared_counted _).trans ?_
  refine EvalDistEq.bind_right _ (fun material => EvalDistEq.bind_right _ (fun seed => ?_))
  rw [← simulateQ_countHashQueries]
  change (simulateQ romImpl (countHashQueries (gameAfterMasterDet (internalize adversary) seed))).run'
    (programCache ∅ seed material) =ᵈ _
  refine (evalDist_graph_continuation (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) _ (PrunedGraph.active (parameter material))
    (PrunedGraph.initialLabels (parameter material) (GraphCorrectness.materialSurrogates material))
    _ (material_freshStructural (parameter material) seed material)).trans ?_
  refine EvalDistEq.bind_right _ (fun answers => ?_)
  exact evalDist_romImpl_eq_table _
    (OnlyW.counted _ _ (OnlyW.gameAfterMasterDet_internalize adversary seed)) _

end Sphincs.Security.Det
