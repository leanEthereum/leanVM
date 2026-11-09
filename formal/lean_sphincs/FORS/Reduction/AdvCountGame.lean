module

public import FORS.Reduction.CostProgram
public import FORS.GraphView.HonestGame
public import FORS.Reduction.PreparedSample
import all PolyFun.PFunctor.Handler.Instrumentation

@[expose] public section

/-! The deterministic-randomizer game at the adversary's own count. The cost program
`costGameDet` charges key generation (one tick), the adversary's raw queries and the verifier's,
and reads the signer through honest reads (free): on a fixed answer function it has the joint law of
the game's outcome and the count `keygenHashCost + adversary's own hash calls + verification's hash
calls` of `gameAfterSeedAdv` (`costGameDetH_correct`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.AdvCount

variable [Params]

open Concrete Completeness Prefix HiddenGraph SeedCoupling GraphView Internalize Det Short

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-! ### Two writers in either order -/

omit [Params] in
/-- Simulating with a cost writer over a log writer, or a log writer over a cost writer, gives the
same results when every query does. -/
theorem simulateQ_writer_swap {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    [LawfulMonad m] {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω] {β : Type}
    (A : QueryImpl spec (AddWriterT Nat (WriterT ω m))) (B : QueryImpl spec (WriterT ω (AddWriterT Nat m)))
    (h : ∀ t, (A t).run.run = (fun r => ((r.1.1, r.2), r.1.2)) <$> (B t).run.run)
    (M : OracleComp spec β) :
    (simulateQ A M).run.run = (fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ B M).run.run := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact (map_pure (f := m) (fun r : (β × ω) × Nat => ((r.1.1, r.2), r.1.2))
        ((value, ∅), (1 : Multiplicative Nat))).symm
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map, h, ih,
        map_bind, bind_map_left, Functor.map_map]

/-! ### The deterministic signer with honest reads -/

/-- The deterministic signer with honest reads: the randomizer base and step read from the table,
then the honest scan; nothing is charged. -/
noncomputable def signCostDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (message : Message) : OracleComp CostSpecH (Option Signature) :=
  signCostSourceLoopH parameter data message (walkStep (upperHash (rnd message))) digestAttemptLimit
    (truncateHash (rnd message))

noncomputable def costInteractionDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable) :
    QueryImpl AdvSpec (WriterT (QueryLog SigningSpec) (OracleComp CostSpecH)) :=
  QueryImpl.add (ordinaryCostSourceH.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpecH)))
    (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
      (fun message => signCostDet parameter data rnd message))

/-- The rest of the game: the adversary's and the verifier's queries charged, the signer honest. -/
noncomputable def costRestDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpecH Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteractionDet parameter data rnd) (adversary.main pk)).run
  let verified ← liftRawH (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The deterministic game at the adversary's count: key generation's tick, then `costRestDet`. -/
noncomputable def costGameDet (parameter : PublicParameter) (data : PublicData) (rnd : RTable)
    (adversary : Adversary) : OracleComp CostSpecH Bool := do
  HiddenCost.tick (H := HashInput) keygenHashCost
  costRestDet parameter data rnd adversary

attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  digestAttemptLimit

/-- The honest scan on a fixed answer function is the seeded scan's value, at no cost. -/
theorem fixed_signCostDetLoop (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (prf : HashOutput) (message : Message) (step : Randomness) (attempts : Nat) (start : Randomness) :
    simulateQ (fixedCostSource f table) (signCostSourceLoopH parameter data message step attempts start) =
      pure (evalWithAnswerFn f (seededFrom ⟨seed, prf, parameter, data.root⟩ message step attempts start)) := by
  induction attempts generalizing start with
  | zero =>
      simp only [signCostSourceLoopH, seededFrom, Seeded.signDigestLoop, pure_bind, simulateQ_pure,
        evalWithAnswerFn_pure]
  | succ attempts ih =>
      have hX : seededFrom ⟨seed, prf, parameter, data.root⟩ message step (attempts + 1) start =
          (Seeded.signAttempt ⟨seed, prf, parameter, data.root⟩ message start :
              OracleComp HashSpec (Option Index)) >>= fun result =>
                match result with
                | some _ => Seeded.finishSign ⟨seed, prf, parameter, data.root⟩ message start
                | none => seededFrom ⟨seed, prf, parameter, data.root⟩ message step attempts (start + step) := by
        simp only [seededFrom, Seeded.signDigestLoop, bind_assoc]
        refine bind_congr fun result => ?_
        cases result <;> simp
      rw [hX]
      simp only [signCostSourceLoopH, simulateQ_bind, fixedCostSourceH_liftHonest, pure_bind,
        evalWithAnswerFn_bind, eval_signAttempt]
      by_cases hland : Landed parameter (blockIndex (evalWithAnswerFn f
        (messageDigestCall parameter data.root message start firstCall : OracleComp HashSpec HashOutput)))
      · have hland' : Landed parameter (digestIndex (evalWithAnswerFn f
            (messageDigest parameter data.root message start : OracleComp HashSpec MessageDigest))) :=
          landed_full _ _
        simp only [hland, ↓reduceIte, fixed_finishCostSource,
          eval_finishSign_assembled f parameter seed data table hdata htable prf message start hland']
      · simp only [hland, ↓reduceIte, ih]

/-- The honest deterministic signer on a fixed answer function is the deterministic signer's value,
at no cost, when the table holds the answers at the randomizer-derivation inputs. -/
theorem fixed_signCostDetH (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (prf : HashOutput) (rnd : RTable)
    (hrnd : ∀ message, f (randomizerHashInput prf parameter message) = rnd message) (message : Message) :
    simulateQ (fixedCostSource f table) (signCostDet parameter data rnd message) =
      pure (evalWithAnswerFn f (Seeded.sign ⟨seed, prf, parameter, data.root⟩ message :
        OracleComp HashSpec (Option Signature))) := by
  have hX : (Seeded.sign ⟨seed, prf, parameter, data.root⟩ message :
      OracleComp HashSpec (Option Signature)) =
      (deriveRandomizer prf parameter message : OracleComp HashSpec (Randomness × Randomness)) >>= fun walk =>
        seededFrom ⟨seed, prf, parameter, data.root⟩ message walk.2 digestAttemptLimit walk.1 := by
    rw [seededSign_eq]
    rfl
  rw [hX, signCostDet, fixed_signCostDetLoop f parameter seed data table hdata htable prf,
    evalWithAnswerFn_bind, eval_deriveRandomizer, hrnd]

/-! ### Honest-signer cost program on a fixed answer function -/

theorem fixedCostSourceH_tick (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) (amount : Nat) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.tick (H := HashInput) (D := HashInput) (R := HashOutput) (ι := Coordinate) amount) =
      AddWriterT.addTell amount := by
  rw [HiddenCost.tick, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, fixedCostAnswer, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, AddWriterT.addTell]
  simp only [← PMF.monad_pure_eq_pure, map_pure]

/-! ### The experiment at the adversary's own count -/

/-- The adversary's own hash queries. -/
def AdvHash : AdvSpec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

instance : DecidablePred AdvHash := fun input => by
  rcases input with (draw | bytes) | message <;> unfold AdvHash <;> infer_instance

/-- The verification at the adversary's count: the win and `keygenHashCost + calls + checks`. -/
noncomputable def verifyAdv (pk : PublicKey) (output : (Forgery × Nat) × QueryLog SigningSpec) :
    OracleComp OracleWorld (Bool × Nat) :=
  (fun checked => (decide (SigningTranscript.Valid output.2 ∧
      ¬SigningTranscript.Contains output.2 output.1.1) && checked.1,
    keygenHashCost + output.1.2 + checked.2)) <$>
    countHashQueries (liftM (Concrete.verify pk output.1.1.message output.1.1.signature :
      OracleComp HashSpec Bool))

/-- The deterministic game after `SK.seed` with the count `keygenHashCost + the adversary's own hash
calls + the verification's hash calls` as part of its output; the signer's calls are not counted. -/
noncomputable def gameAfterSeedAdv (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld (Bool × Nat) :=
  (liftM (FORS.Seeded.keygenFromSeed seed) : OracleComp OracleWorld _) >>= fun keys =>
    leftProgD keys.2 (QueryCap.counted AdvHash (adversary.main keys.1)) >>= verifyAdv keys.1

/-- The random-oracle experiment counting key generation, the adversary's own hash calls and the
verification's, but not the signer's: whether the adversary won, and that count. -/
noncomputable def experimentAdv (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ romImpl ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>=
    gameAfterSeedAdv adversary)).run' ∅

omit [Params] in
theorem fst_counted {ι : Type} {spec : OracleSpec ι} (selected : ι → Prop) [DecidablePred selected]
    {α : Type} (oa : OracleComp spec α) : Prod.fst <$> QueryCap.counted selected oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [QueryCap.counted_query_bind]
      simp only [map_bind, map_pure]
      refine bind_congr fun answer => ?_
      conv_rhs => rw [← ih answer]
      rw [map_eq_bind_pure_comp]
      rfl

theorem leftProgD_map (sk : FORS.Seeded.SecretKey) {β γ : Type} (g : β → γ) (M : OracleComp AdvSpec β) :
    leftProgD sk (g <$> M) = (fun result => (g result.1, result.2)) <$> leftProgD sk M := by
  rw [leftProgD, leftProgD, simulateQ_map, WriterT.run_map]

theorem fst_verifyAdv (pk : PublicKey) (output : (Forgery × Nat) × QueryLog SigningSpec) :
    Prod.fst <$> verifyAdv pk output = verifyPart pk (output.1.1, output.2) := by
  rw [verifyAdv, Functor.map_map, verifyPart, countHashQueries]
  conv_rhs => rw [← fst_counted (fun input : OracleWorld.Domain => input matches .inr _)
    (liftM (Concrete.verify pk output.1.1.message output.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)]
  rw [bind_map_left, map_eq_bind_pure_comp]
  rfl

theorem fst_gameAfterSeedAdv (adversary : Adversary) (seed : MasterSeed) :
    Prod.fst <$> gameAfterSeedAdv adversary seed = gameAfterSeedDet adversary seed := by
  rw [gameAfterSeedAdv, gameAfterSeedDet_eq]
  simp only [map_bind]
  refine bind_congr fun keys => ?_
  conv_rhs => rw [← fst_counted AdvHash (adversary.main keys.1), leftProgD_map, bind_map_left]
  exact bind_congr fun output => fst_verifyAdv keys.1 output

theorem fst_experimentAdv (adversary : Adversary) :
    Prod.fst <$> experimentAdv adversary = (simulateQ romImpl (gameCore adversary)).run' ∅ := by
  have h : (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= gameAfterSeedDet adversary =
      Prod.fst <$> ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>=
        gameAfterSeedAdv adversary) := by
    simp only [map_bind, fst_gameAfterSeedAdv]
  rw [experimentAdv, gameCore_eq_sampling, h, simulateQ_map]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem fst_experiment (adversary : Adversary) :
    Prod.fst <$> experiment adversary = (simulateQ romImpl (gameCore adversary)).run' ∅ := by
  rw [experiment, ← simulateQ_countHashQueries]
  conv_rhs => rw [← fst_counted (fun input : OracleWorld.Domain => input matches .inr _) (gameCore adversary)]
  rw [simulateQ_map]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl

/-! ### The cost program has the law of the adversary-count game -/

theorem interaction_query (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (prf : HashOutput) (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput prf parameter message) = rnd message)
    (t : AdvSpec.Domain) :
    ((((Prefix.fixedHashWorld f).writerTMapBase (gameImplDet ⟨seed, prf, parameter, data.root⟩)).withAddCost
        (fun t => if AdvHash t then 1 else 0)) t).run.run =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        (((fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd)) t).run.run := by
  have hA : ∀ request : OracleWorld.Domain,
      (Prefix.fixedHashWorld f).writerTMapBase (gameImplDet ⟨seed, prf, parameter, data.root⟩) (.inl request) =
        (liftM (Prefix.fixedHashWorld f request) : WriterT (QueryLog SigningSpec) PMF _) := by
    intro request
    apply WriterT.ext
    change simulateQ (Prefix.fixedHashWorld f) ((liftM (liftM (OracleWorld.query request) :
      OracleComp OracleWorld _) : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run) = _
    rw [WriterT.run_liftM, simulateQ_map, simulateQ_spec_query, WriterT.run_liftM]
    rfl
  have hB : ∀ request : OracleWorld.Domain,
      (fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd) (.inl request) =
        (liftM (Prefix.fixedWorldCost f request) : WriterT (QueryLog SigningSpec) (AddWriterT Nat PMF) _) := by
    intro request
    change ((fixedCostSource f table).writerTMapBase
      (ordinaryCostSourceH.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpecH)))) request = _
    rw [map_lift_query, fixedCostSourceH_ordinary]
  rcases t with (draw | bytes) | message
  · simp only [QueryImpl.withAddCost_apply, hA, hB]
    simp [Prefix.fixedWorldCost, Prefix.fixedHashWorld, AdvHash, QueryImpl.withAddCost_apply, WriterT.run_liftM,
      AddWriterT.addTell]
  · simp only [QueryImpl.withAddCost_apply, hA, hB]
    simp [Prefix.fixedWorldCost, Prefix.fixedHashWorld, AdvHash, QueryImpl.withAddCost_apply, WriterT.run_liftM,
      AddWriterT.addTell]
  · have hA' : (Prefix.fixedHashWorld f).writerTMapBase (gameImplDet ⟨seed, prf, parameter, data.root⟩)
        (.inr message) = ((Prefix.fixedHashWorld f).writerTMapBase
          (signingOracle ⟨seed, prf, parameter, data.root⟩)) message := rfl
    have hB' : (fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd) (.inr message) =
        ((fixedCostSource f table).writerTMapBase (QueryImpl.withLogging (spec := SigningSpec)
          (m := OracleComp CostSpecH) (fun message => signCostDet parameter data rnd message))) message := rfl
    simp only [QueryImpl.withAddCost_apply, hA', hB']
    rw [signingOracle, map_logging_query, map_logging_query]
    simp only [fixed_signCostDetH f parameter seed data table hdata htable prf rnd hrnd,
      Prefix.fixedHashWorld_lift_hash]
    simp [AdvHash, WriterT.run_liftM, AddWriterT.addTell]
    simp only [← PMF.monad_pure_eq_pure, map_pure, ← PMF.monad_bind_eq_bind, pure_bind, List.nil_append]

theorem fixedHashWorld_verifyAdv (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (output : (Forgery × Nat) × QueryLog SigningSpec) :
    simulateQ (Prefix.fixedHashWorld f) (verifyAdv pk output) =
      PMF.pure (decide (SigningTranscript.Valid output.2 ∧ ¬SigningTranscript.Contains output.2 output.1.1) &&
          evalWithAnswerFn f (Concrete.verify pk output.1.1.message output.1.1.signature : OracleComp HashSpec Bool),
        keygenHashCost + output.1.2 +
          hashCalls f (Concrete.verify pk output.1.1.message output.1.1.signature : OracleComp HashSpec Bool)) := by
  rw [verifyAdv, simulateQ_map, Assembly.fixedHashWorld_countHashQueries, fixedWorldCost_lift_hash,
    WriterT.run_mk, ← PMF.monad_pure_eq_pure, map_pure]
  rfl

theorem fixedHashWorld_leftProgD_counted (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (prf : HashOutput) (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput prf parameter message) = rnd message)
    (M : OracleComp AdvSpec Forgery) :
    simulateQ (Prefix.fixedHashWorld f) (leftProgD ⟨seed, prf, parameter, data.root⟩ (QueryCap.counted AdvHash M)) =
      (fun r => ((r.1.1, r.2), r.1.2)) <$>
        (simulateQ ((fixedCostSource f table).writerTMapBase (costInteractionDet parameter data rnd)) M).run.run := by
  rw [leftProgD, QueryImpl.simulateQ_writerTMapBase_run, QueryCap.simulate_withCost]
  exact simulateQ_writer_swap _ _
    (interaction_query f parameter seed data table hdata htable prf rnd hrnd) M

/-- **The adversary-count cost program is the game.** On a fixed answer function, the honest
deterministic cost game has the joint law of `gameAfterSeedAdv`'s outcome and count. -/
theorem costGameDetH_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (hparameter : evalWithAnswerFn f (derivePublicSeed seed : OracleComp HashSpec PublicParameter) = parameter)
    (prf : HashOutput) (hprf : evalWithAnswerFn f (derivePrf seed : OracleComp HashSpec HashOutput) = prf)
    (rnd : RTable) (hrnd : ∀ message, f (randomizerHashInput prf parameter message) = rnd message)
    (adversary : Adversary) :
    (simulateQ (fixedCostSource f table) (costGameDet parameter data rnd adversary)).run =
      simulateQ (Prefix.fixedHashWorld f) (gameAfterSeedAdv adversary seed) := by
  have hkeys : simulateQ (Prefix.fixedHashWorld f) (liftM (FORS.Seeded.keygenFromSeed seed) :
      OracleComp OracleWorld (PublicKey × FORS.Seeded.SecretKey)) =
      PMF.pure ((⟨data.root, parameter⟩, ⟨seed, prf, parameter, data.root⟩) :
        PublicKey × FORS.Seeded.SecretKey) := by
    rw [Prefix.fixedHashWorld_lift_hash]
    simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure, hparameter, hprf,
      ← hdata.root]
  rw [gameAfterSeedAdv, simulateQ_bind, hkeys, ← PMF.monad_pure_eq_pure, pure_bind, simulateQ_bind,
    fixedHashWorld_leftProgD_counted f parameter seed data table hdata htable prf rnd hrnd]
  simp only [fixedHashWorld_verifyAdv, costGameDet, costRestDet, simulateQ_bind, simulateQ_pure,
    fixedCostSourceH_tick, QueryImpl.simulateQ_writerTMapBase_run, fixedCostSourceH_liftRawH,
    fixedWorldCost_lift_hash, WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell]
  simp only [pure_bind, bind_map_left, map_bind]
  refine bind_congr fun x => ?_
  simp only [← PMF.monad_pure_eq_pure, pure_bind, map_pure, WriterT.run_pure]
  congr 2
  generalize hashCalls f (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) x.1.1.message x.1.1.signature :
    OracleComp HashSpec Bool) = h
  generalize x.2 = w
  change keygenHashCost + (Multiplicative.toAdd w + (h + 0)) = keygenHashCost + Multiplicative.toAdd w + h
  omega

/-! ### The win: `experimentAdv`'s outcome is the SUF-CMA game's -/

omit [Params] in
theorem fst_leftRun {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => result.1.1) <$> leftRun oa cache = (simulateQ romImpl oa).run' cache := by
  rw [leftRun, countShort]
  conv_rhs => rw [← fst_counted ShortQuery oa]
  rw [simulateQ_map]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]

/-- The adversary-count experiment wins exactly as often as the SUF-CMA experiment. -/
theorem winAdv_eq (adversary : Adversary) :
    Pr{let result ← experimentAdv adversary}[result.1 = true] = forgeAdvantage adversary := by
  rw [forgeAdvantage, ← prEvent_map (experimentAdv adversary) Prod.fst (fun b => b = true),
    ← prEvent_map (experiment adversary) Prod.fst (fun b => b = true), fst_experimentAdv, fst_experiment]

/-- Internalizing long inputs does not change the advantage. -/
theorem forgeAdvantage_internalize (adversary : Adversary) :
    forgeAdvantage (internalize adversary) = forgeAdvantage adversary := by
  rw [forgeAdvantage, forgeAdvantage, (evalDist_experiment_internalize adversary).prEvent_eq, prEvent_map,
    ← prEvent_map (leftRun (gameCore adversary) ∅) (fun result => result.1.1) (fun b => b = true), fst_leftRun,
    ← prEvent_map (experiment adversary) Prod.fst (fun b => b = true), fst_experiment]

/-! ### The count: at most `keygenHashCost + q + V` on every path -/

omit [Params] in
theorem counted_le_of_isQueryBoundP {ι : Type} {spec : OracleSpec ι} (selected : ι → Prop)
    [DecidablePred selected] {α : Type} (oa : OracleComp spec α) (n : Nat) (h : oa.IsQueryBoundP selected n) :
    ∀ result ∈ support (QueryCap.counted selected oa), result.2 ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure value =>
      intro result hresult
      rw [QueryCap.counted_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      intro result hresult
      rw [QueryCap.counted_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨tail, htail, hresult⟩ := hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      have := ih answer _ (h.2 answer) tail htail
      rw [hresult]
      by_cases hsel : selected input
      · simp only [hsel, ↓reduceIte] at this ⊢
        rcases h.1 with hnot | hpos
        · exact absurd hsel hnot
        · omega
      · simp only [hsel, ↓reduceIte] at this ⊢
        omega

omit [Params] in
theorem fst_mem_support_writer_run {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {ω : Type}
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] {β : Type}
    (impl : QueryImpl spec (WriterT ω (OracleComp spec'))) (M : OracleComp spec β) :
    ∀ result ∈ support (simulateQ impl M).run, result.1 ∈ support M := by
  induction M using OracleComp.inductionOn with
  | pure value =>
      intro result hresult
      simp only [simulateQ_pure, WriterT.run_pure', support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      exact mem_support_pure_iff _ _ |>.2 rfl
  | query_bind input next ih =>
      intro result hresult
      rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨first, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      exact (mem_support_bind_iff _ _ _).2 ⟨first.1, mem_support_query _ _, ih first.1 tail htail⟩

theorem isQueryBoundP_liftWorld_prob {α : Type} (computation : ProbComp α) :
    (liftWorld (liftM computation : OracleComp OracleWorld α)).IsQueryBoundP AdvHash 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [liftWorld]
  | query_bind input next ih =>
      rw [liftM_bind, liftWorld, simulateQ_bind]
      change IsQueryBoundP (simulateQ liftWorldImpl (liftM (OracleWorld.query (.inl input))) >>= fun answer =>
        liftWorld (liftM (next answer))) AdvHash 0
      rw [simulateQ_spec_query]
      exact isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim) ih

/-- Internalizing keeps the adversary's own hash-call bound. -/
theorem isQueryBoundP_internalize (adversary : Adversary) (q : Nat)
    (hq : ∀ pk, (adversary.main pk).IsQueryBoundP AdvHash q) (pk : PublicKey) :
    ((internalize adversary).main pk).IsQueryBoundP AdvHash q := by
  change ((simulateQ internalImpl (adversary.main pk)).run' ∅).IsQueryBoundP AdvHash q
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine IsQueryBoundP.simulateQ_run_StateT_of_step (hq pk) (fun input cache => ?_) ∅
  rcases input with (draw | bytes) | message
  · exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim)
  · by_cases hshort : IsShort bytes
    · simp only [internalImpl, hshort, ↓reduceIte]
      exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    · simp only [internalImpl, hshort, ↓reduceIte, StateT.run, privateRead]
      split
      · exact isQueryBoundP_pure _ _ _
      · exact ((isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_liftWorld_prob _)).mono (Nat.zero_le _)
  · exact (isQueryBoundP_map_iff _ _ _).2 ((isQueryBoundP_query_iff _ _ _).2 fun h => h.elim)

omit [Params] in
theorem countHashQueries_liftM {α : Type} (computation : OracleComp HashSpec α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (liftM (QueryCap.counted (fun _ => True) computation) : OracleComp OracleWorld (α × Nat)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, countHashQueries, QueryCap.counted_pure]
  | query_bind input next ih =>
      simp only [countHashQueries] at ih
      simp only [liftM_bind, countHashQueries]
      change QueryCap.counted _ (liftM (OracleWorld.query (.inr input)) >>= fun output => liftM (next output)) = _
      simp only [QueryCap.counted_query_bind, ih, liftM_bind, liftM_pure, ite_true]
      rfl

/-- **The budget.** If the adversary makes at most `q` hash calls of its own on every path and the
verifier at most `V`, every run of `experimentAdv` counts at most `keygenHashCost + q + V`. -/
theorem experimentAdv_count_le (adversary : Adversary) (q V : Nat)
    (hq : ∀ pk, (adversary.main pk).IsQueryBoundP AdvHash q)
    (hV : ∀ pk message signature,
      (Concrete.verify pk message signature : OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) V) :
    ∀ result ∈ support (experimentAdv adversary), result.2 ≤ keygenHashCost + q + V := by
  intro result hresult
  have hgame := support_simulateQ_run'_subset romImpl _ ∅ hresult
  rw [mem_support_bind_iff] at hgame
  obtain ⟨seed, _, hgame⟩ := hgame
  rw [gameAfterSeedAdv, mem_support_bind_iff] at hgame
  obtain ⟨keys, _, hgame⟩ := hgame
  rw [mem_support_bind_iff] at hgame
  obtain ⟨output, houtput, hverify⟩ := hgame
  have hcalls := counted_le_of_isQueryBoundP AdvHash _ q (hq keys.1) _
    (fst_mem_support_writer_run _ _ output houtput)
  rw [verifyAdv, support_map] at hverify
  obtain ⟨checked, hchecked, rfl⟩ := hverify
  rw [countHashQueries_liftM] at hchecked
  have hchecks := counted_le_of_isQueryBoundP (fun _ => True) _ V (hV _ _ _) _
    (mem_support_of_mem_support_liftComp _ _ _ hchecked)
  show keygenHashCost + output.1.2 + checked.2 ≤ _
  omega

/-! ### The internalized game as an average of fixed-function games -/

theorem OnlyAdv.countedAdv {β : Type} (M : OracleComp AdvSpec β) (h : OnlyAdv M) :
    OnlyAdv (QueryCap.counted AdvHash M) := by
  induction M using OracleComp.inductionOn with
  | pure value => rw [QueryCap.counted_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind input next ih =>
      rw [OnlyAdv, isQueryBoundP_query_bind_iff] at h
      rw [QueryCap.counted_query_bind, OnlyAdv, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      have hnext : OnlyAdv (next answer) := by
        have := h.2 answer
        split at this <;> simpa [OnlyAdv] using this
      have hbind : OnlyAdv (QueryCap.counted AdvHash (next answer) >>= fun result =>
          (pure (result.1, (if AdvHash input then 1 else 0) + result.2) : OracleComp AdvSpec (β × Nat))) :=
        OnlyAdv.bind (ih answer hnext) (fun _ => by simp [OnlyAdv])
      split <;> simpa [OnlyAdv] using hbind

theorem OnlyW.gameAfterSeedAdv_internalize (adversary : Adversary) (seed : MasterSeed) :
    OnlyW (gameAfterSeedAdv (internalize adversary) seed) := by
  refine OnlyW.bind (OnlyW.liftHash (Short.Seeded.Only.keygenFromSeed seed)) (fun keys => ?_)
  refine OnlyW.bind (OnlyW.gameImplDet keys.2 _
    (OnlyAdv.countedAdv _ (OnlyAdv.map _ (OnlyAdv.internal _ _)))) (fun output => ?_)
  exact OnlyW.map _ (Assembly.OnlyW.counted _ _ (OnlyW.liftHash (Short.Only.verify _ _ _)))

open SeedModel _root_.FORS.Security.Graph Assembly Eager in
noncomputable local instance advLabelsSampleable : SampleableType CanonicalGraphLabels :=
  graphLabelsSampleable

open SeedModel _root_.FORS.Security.Graph Assembly Eager in
/-- The internalized adversary-count experiment as an average of fixed-function games. -/
theorem evalDist_experimentAdv_fixed (adversary : Adversary) :
    experimentAdv (internalize adversary) =ᵈ (do
      let material ← sampleMaterial
      let seed ← sampleMasterSeed
      let answers ← $ᵗ CanonicalGraphLabels
      let table ← $ᵗ Eager.Table
      simulateQ (fixedRom (extend (preparedCache material seed answers) table))
        (gameAfterSeedAdv (internalize adversary) seed) : ProbComp (Bool × Nat)) := by
  rw [experimentAdv]
  refine (evalDist_seeded_prepared _).trans ?_
  refine EvalDistEq.bind_right _ (fun material => EvalDistEq.bind_right _ (fun seed => ?_))
  refine (evalDist_graph_continuation (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) _ (PrunedGraph.active (parameter material))
    (PrunedGraph.initialLabels (parameter material) (GraphCorrectness.materialSurrogates material))
    _ (material_freshStructural (parameter material) seed material)).trans ?_
  refine EvalDistEq.bind_right _ (fun answers => ?_)
  exact evalDist_romImpl_eq_table _ (OnlyW.gameAfterSeedAdv_internalize adversary seed) _

end FORS.Security.AdvCount
