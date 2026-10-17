import Sphincs.BridgeDetInternalize

/-! The graph-view cost program of the deterministic-randomizer game. The randomizer base
`R0` of a message is read from a table `rnd` of full hash outputs indexed by message; its one
derivation hash call is charged as a one-unit tick, so the cost program preserves the joint law of output and original
hash cost whenever `rnd` holds the answers at the seed's randomizer-derivation inputs. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Det

open Concrete Completeness Prefix HiddenGraph SeedCoupling GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Randomizer-base derivation outputs (`R0`), by message. -/
abbrev RTable := Message → HashOutput

variable [Params]

/-- The deterministic signer in the graph view: charge the one derivation call of the randomizer
base, read the base from the table, then scan from it. -/
noncomputable def signCostDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick 1
  signCostSourceLoop parameter data message digestAttemptLimit (truncateHash (rnd message))

noncomputable def costInteractionDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostDet parameter data rnd message)

noncomputable def costRestDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteractionDet parameter data rnd) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def costGameDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpec Bool := do
  HiddenCost.tick (226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight))
  costRestDet parameter data rnd adversary

/-- The deterministic signer from a scan of `attempts` trials starting at `start`. -/
def seededFrom (sk : Seeded.SecretKey) (message : Message) (attempts : Nat) (start : Randomness) :
    OracleComp HashSpec (Option Signature) := do
  let some (randomness, _) ← Seeded.signDigestLoop sk message attempts start | return none
  Randomized.finishSign sk message randomness

omit [Params] in
theorem eval_deriveRandomizer (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (message : Message) :
    evalWithAnswerFn f (deriveRandomizer parameter seed message : OracleComp HashSpec Randomness) =
      truncateHash (f (randomizerHashInput parameter seed message)) := by
  simp only [deriveRandomizer, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

omit [Params] in
theorem hashCalls_deriveRandomizer (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (message : Message) :
    hashCalls f (deriveRandomizer parameter seed message : OracleComp HashSpec Randomness) = 1 := by
  simp only [deriveRandomizer, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure]

theorem eval_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) =
      if Landed sk.parameter (blockIndex (evalWithAnswerFn f
          (messageDigestCall sk.parameter sk.root message randomness : OracleComp HashSpec HashOutput)))
      then some (blockIndex (evalWithAnswerFn f
          (messageDigestCall sk.parameter sk.root message randomness : OracleComp HashSpec HashOutput)))
      else none := by
  simp only [Seeded.signAttempt, evalWithAnswerFn_bind]
  split <;> rfl

/-- The scan in the graph view and the seeded scan have the same joint output and cost law, from
any start. -/
theorem fixed_signCostDetLoop (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (attempts : Nat) (start : Randomness) :
    simulateQ (fixedCostSource f table) (signCostSourceLoop parameter data message attempts start) =
      simulateQ (fixedWorldCost f) (liftM (seededFrom ⟨seed, parameter, data.root⟩ message attempts start) :
        OracleComp OracleWorld (Option Signature)) := by
  induction attempts generalizing start with
  | zero =>
      simp only [signCostSourceLoop, seededFrom, Seeded.signDigestLoop, pure_bind, simulateQ_pure,
        liftM_pure]
  | succ attempts ih =>
      have hX : seededFrom ⟨seed, parameter, data.root⟩ message (attempts + 1) start =
          (Seeded.signAttempt ⟨seed, parameter, data.root⟩ message start :
              OracleComp HashSpec (Option Index)) >>= fun result =>
                match result with
                | some _ => Randomized.finishSign ⟨seed, parameter, data.root⟩ message start
                | none => seededFrom ⟨seed, parameter, data.root⟩ message attempts (start + 1) := by
        simp only [seededFrom, Seeded.signDigestLoop, bind_assoc]
        refine bind_congr fun result => ?_
        cases result <;> simp
      rw [fixedWorldCost_lift_hash, hX]
      simp only [signCostSourceLoop, simulateQ_bind, fixedCostSource_lift_hash,
        fixedWorldCost_lift_hash]
      simp only [evalWithAnswerFn_bind, hashCalls_bind, hashCalls_signAttempt, eval_signAttempt,
        hashCalls_messageDigestCall]
      by_cases hland : Landed parameter (blockIndex (evalWithAnswerFn f
        (messageDigestCall parameter data.root message start : OracleComp HashSpec HashOutput)))
      · have hland' : Landed parameter (digestIndex (evalWithAnswerFn f
            (messageDigest parameter data.root message start : OracleComp HashSpec MessageDigest))) := by
          simpa only [messageDigest, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            digestIndex_truncate] using hland
        apply WriterT.ext
        simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind]
        simp only [hland, ↓reduceIte,
          finishCostSource_correct f parameter seed data table hdata htable message start hland',
          fixedWorldCost_lift_hash, WriterT.run_mk, ← PMF.monad_pure_eq_pure, map_pure, ← ofAdd_add]
      · apply WriterT.ext
        simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind]
        simp only [hland, ↓reduceIte, ih, fixedWorldCost_lift_hash, WriterT.run_mk,
          ← PMF.monad_pure_eq_pure, map_pure, ← ofAdd_add]

/-- The deterministic signer and its graph view have the same joint output and cost law. -/
theorem signCostDet_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (message : Message) :
    simulateQ (fixedCostSource f table) (signCostDet parameter data rnd message) =
      simulateQ (fixedWorldCost f) (liftM (Seeded.sign ⟨seed, parameter, data.root⟩ message :
        OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature)) := by
  have hX : (Seeded.sign ⟨seed, parameter, data.root⟩ message :
      OracleComp HashSpec (Option Signature)) =
      (deriveRandomizer parameter seed message : OracleComp HashSpec Randomness) >>= fun base =>
        seededFrom ⟨seed, parameter, data.root⟩ message digestAttemptLimit base := by
    rw [seededSign_eq]
    rfl
  rw [hX, fixedWorldCost_lift_hash]
  simp only [signCostDet, simulateQ_bind, fixedCostSource_tick,
    fixed_signCostDetLoop f parameter seed data table hdata htable, fixedWorldCost_lift_hash,
    evalWithAnswerFn_bind, hashCalls_bind, eval_deriveRandomizer, hashCalls_deriveRandomizer, hrnd]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind, map_pure, ← ofAdd_add]

theorem fixedCostSource_interactionDet (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message) :
    (fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd) =
      (fixedWorldCost f).writerTMapBase
        (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracleDet ⟨seed, parameter, data.root⟩) := by
  funext request
  cases request with
  | inl request =>
      change ((fixedCostSource f table).writerTMapBase
        (ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)))) request = _
      rw [map_lift_query, fixedCostSource_ordinary]
      apply WriterT.ext
      change (fun value => (value, (∅ : QueryLog SigningSpec))) <$> fixedWorldCost f request =
        simulateQ (fixedWorldCost f) ((fun value => (value, (∅ : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query request) : OracleComp OracleWorld _))
      rw [simulateQ_map, simulateQ_spec_query]
  | inr message =>
      change ((fixedCostSource f table).writerTMapBase
        (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
          (fun message => signCostDet parameter data rnd message))) message =
        ((fixedWorldCost f).writerTMapBase (signingOracleDet ⟨seed, parameter, data.root⟩)) message
      rw [signingOracleDet, map_logging_query, map_logging_query]
      have hsign : (fun message => simulateQ (fixedCostSource f table)
          (signCostDet parameter data rnd message)) =
          (fun message => simulateQ (fixedWorldCost f)
            (liftM (Seeded.sign ⟨seed, parameter, data.root⟩ message :
              OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature))) := by
        funext message
        exact signCostDet_correct f parameter seed data table hdata htable rnd hrnd message
      exact congrArg (fun impl : QueryImpl SigningSpec (AddWriterT Nat PMF) =>
        impl.withLogging message) hsign

theorem fixedCostSource_restDet (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costRestDet parameter data rnd adversary) =
      simulateQ (fixedWorldCost f) (do
        let pk : PublicKey := ⟨data.root, parameter⟩
        let (forgery, log) ← (simulateQ (QueryImpl.ofLift OracleWorld
          (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
          signingOracleDet ⟨seed, parameter, data.root⟩) (adversary.main pk)).run
        let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
        return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified) := by
  simp only [costRestDet, simulateQ_bind, simulateQ_pure, QueryImpl.simulateQ_writerTMapBase_run,
    fixedCostSource_interactionDet f parameter seed data table hdata htable rnd hrnd, fixedCostSource_lift_hash]

/-- Fixed-oracle equality for the complete deterministic game, with its original hash budget. -/
theorem costGameDet_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput parameter seed message) = rnd message)
    (adversary : Adversary) :
    simulateQ (fixedCostSource f table) (costGameDet parameter data rnd adversary) =
      simulateQ (fixedWorldCost f) (gameAfterMasterDet adversary seed) := by
  simp only [costGameDet, gameAfterMasterDet, simulateQ_bind, fixedCostSource_tick]
  rw [fixedWorldCost_keygen_graph f parameter seed data hdata hparameter]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind]
  rw [fixedCostSource_restDet f parameter seed data table hdata htable rnd hrnd]
  simp only [simulateQ_bind, WriterT.run_bind]

end Sphincs.Security.Det
