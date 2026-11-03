import FORS.GraphView.Cost
import FORS.GraphView.HashCalls

section

/-! The counted graph-reveal signer. Its final assembly preserves the joint law of the actual
signature and its original hash cost on a fixed answer function. Internal graph work is charged
even when encoding exhausts. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.finishSign digestAttemptLimit sequenceFin

abbrev CostSpec := HiddenCost.SourceCostSpec HashInput HashOutput Coordinate

noncomputable def fixedCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpec (AddWriterT Nat PMF) :=
  QueryImpl.withAddCost (spec := CostSpec)
    (fun | .inl request => fixedSource f table request | .inr _ => PMF.pure ())
    HiddenCost.sourceCost

theorem fixedCostSource_lift_hash (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (liftM computation : OracleComp CostSpec α) =
      simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      rfl

theorem fixedWorldCost_lift_hash (f : QueryImpl HashSpec Id)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) =
      WriterT.mk (PMF.pure (evalWithAnswerFn f computation,
        Multiplicative.ofAdd (hashCalls f computation))) := by
  apply WriterT.ext
  have hcount : (simulateQ (fixedWorldCost f)
      (liftM computation : OracleComp OracleWorld α)).run =
      simulateQ (fixedHashWorld f) (QueryCap.counted SourceHash
        (liftM computation : OracleComp OracleWorld α)) := by
    rw [QueryCap.simulate_withCost]
    congr 2
    funext input
    cases input <;> rfl
  rw [hcount, fixedHashWorld_counted_lift_hash]
  rfl

theorem fixedCostSource_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (coordinate : Coordinate) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.reveal (D := HashInput) (R := HashOutput) coordinate) =
      pure (table coordinate) := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, fixedSource, fixedView]
  change (fun a => (a, (1 : Multiplicative Nat))) <$> PMF.pure (table coordinate) = _
  simp only [← PMF.monad_pure_eq_pure, map_pure]

theorem fixedCostSource_tick (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (amount : Nat) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.tick (D := HashInput) (R := HashOutput) (ι := Coordinate) amount) =
      AddWriterT.addTell amount := by
  rw [HiddenCost.tick, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, AddWriterT.addTell]
  simp only [← PMF.monad_pure_eq_pure, map_pure]

theorem fixedCostSource_sequence_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {n : Nat} (which : Fin n → Coordinate) :
    simulateQ (fixedCostSource f table) (sequenceFin fun index =>
      HiddenCost.reveal (D := HashInput) (R := HashOutput) (which index)) =
      pure (fun index => table (which index)) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext index
      exact index.elim0
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, fixedCostSource_reveal, pure_bind,
        simulateQ_pure, ih]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

theorem fixedCostSource_sequenceFin_pure (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} {n : Nat} (computation : Fin n → OracleComp CostSpec α) (values : Fin n → α)
    (h : ∀ i, simulateQ (fixedCostSource f table) (computation i) = pure (values i)) :
    simulateQ (fixedCostSource f table) (sequenceFin computation) = pure values := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure]
      congr 1
      funext index
      exact index.elim0
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, h 0, pure_bind, simulateQ_pure,
        ih (fun index => computation index.succ) (fun index => values index.succ) (fun i => h i.succ)]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

/-- One tree's opening at the cost level: its secret and leaf are revealed, the path is public. -/
noncomputable def treeCostSource (data : PublicData) (index : Index) (κ : FTree) (leaf : FLeaf) :
    OracleComp CostSpec TreeOpening := do
  let values ← sequenceFin fun k : Fin 2 =>
    HiddenCost.reveal (D := HashInput) (R := HashOutput) (.fors index κ leaf k)
  return ⟨values 0, data.forsPath index κ leaf⟩

theorem fixed_forsCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) (data : PublicData)
    (index : Index) (leaves : FTree → FLeaf) :
    simulateQ (fixedCostSource f table) (sequenceFin fun κ => treeCostSource data index κ (leaves κ)) =
      pure (assembledFors data table index leaves) := by
  apply fixedCostSource_sequenceFin_pure
  intro κ
  rw [treeCostSource, simulateQ_bind, fixedCostSource_sequence_reveal, pure_bind, simulateQ_pure]
  rfl

/-- The counter search of one layer at the cost level: the honest cost of the key's message is
charged first, and on success the chain values and the path. -/
noncomputable def layerCostSearch (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) : OracleComp CostSpec (Option (Counter × Encoding)) := do
  HiddenCost.tick (keyMessageCost lay)
  let found ← liftM (layerSearch parameter data index lay)
  match found with
  | some pair => do
      HiddenCost.tick (160 + treePathCost lay)
      return some pair
  | none => return none

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  HiddenCost.tick (forsTrees * treeOpenCost)
  let index := digestIndex digest
  let some found ← sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)
    | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain => HiddenCost.reveal
    (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun κ => treeCostSource data index κ (digestLeaves digest κ)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

theorem fixed_layerCostSearch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (index : Index) (lay : Layer) :
    simulateQ (fixedCostSource f table) (layerCostSearch parameter data index lay) =
      WriterT.mk (PMF.pure (firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0,
        Multiplicative.ofAdd (layerHashCost f parameter data index lay))) := by
  simp only [layerCostSearch, simulateQ_bind, fixedCostSource_tick, fixedCostSource_lift_hash,
    fixedWorldCost_lift_hash]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell, ← PMF.monad_pure_eq_pure,
    pure_bind, layerSearch, ReferenceChoice.eval_search, layerHashCost]
  cases hs : firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0 with
  | none =>
      simp only [simulateQ_pure, WriterT.run_pure, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero, map_pure, mul_one]
      simp only [← ofAdd_add]
  | some pair =>
      simp only [simulateQ_bind, fixedCostSource_tick, simulateQ_pure, WriterT.run_bind,
        WriterT.run_pure, AddWriterT.run_addTell, pure_bind, Option.isSome_some, ↓reduceIte,
        map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]

/-- Sequencing cost-level computations of fixed results and costs. -/
theorem fixed_sequenceDep (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    ∀ {n : Nat} {α : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpec (Option (α i)))
      (results : (i : Fin n) → Option (α i)) (cost : Fin n → Nat),
      (∀ i, simulateQ (fixedCostSource f table) (computation i) =
        WriterT.mk (PMF.pure (results i, Multiplicative.ofAdd (cost i)))) →
      simulateQ (fixedCostSource f table) (sequenceDep computation) =
        WriterT.mk (PMF.pure (Completeness.allSome results,
          Multiplicative.ofAdd (seqCost (fun i => (results i).isSome) cost)))
  | 0, _, _, _, _, _ => by
      simp only [sequenceDep, simulateQ_pure]
      apply WriterT.ext
      simp only [WriterT.run_pure, WriterT.run_mk, Completeness.allSome, seqCost]
      rw [dif_pos (fun i => Fin.elim0 i)]
      simp only [← PMF.monad_pure_eq_pure, ofAdd_zero]
      congr 3
      funext i
      exact i.elim0
  | n + 1, α, computation, results, cost, h => by
      have h0 := h 0
      have ih := fixed_sequenceDep f table (α := fun i => α i.succ) (fun i => computation i.succ)
        (fun i => results i.succ) (fun i => cost i.succ) (fun i => h i.succ)
      apply WriterT.ext
      rw [sequenceDep, simulateQ_bind, h0]
      cases hhead : results 0 with
      | none =>
          simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind,
            simulateQ_pure, WriterT.run_pure, map_pure, seqCost, hhead, Option.isSome_none,
            Bool.false_eq_true, ↓reduceIte, Nat.add_zero, mul_one]
          congr 2
          unfold Completeness.allSome
          rw [dif_neg (fun hall => by simpa [hhead] using hall 0)]
      | some head =>
          simp only [WriterT.run_bind, WriterT.run_mk, ← PMF.monad_pure_eq_pure, pure_bind,
            simulateQ_bind, ih, seqCost, hhead, Option.isSome_some, ↓reduceIte]
          by_cases hall : ∀ i : Fin n, (results i.succ).isSome
          · have hsome : Completeness.allSome (fun i : Fin n => results i.succ) =
                some fun i => (results i.succ).get (hall i) := dif_pos hall
            have hall' : ∀ i : Fin (n + 1), (results i).isSome := by
              intro i
              refine Fin.cases ?_ (fun j => hall j) i
              simp [hhead]
            have hsome' : Completeness.allSome results = some fun i => (results i).get (hall' i) :=
              dif_pos hall'
            simp only [hsome, hsome', simulateQ_pure, WriterT.run_pure, map_pure, mul_one, ← ofAdd_add]
            congr 3
            funext i
            refine Fin.cases ?_ (fun j => ?_) i
            · simp [hhead]
            · simp
          · have hnone : Completeness.allSome (fun i : Fin n => results i.succ) = none := dif_neg hall
            have hnone' : Completeness.allSome results = none :=
              dif_neg (fun hall' => hall fun i => hall' i.succ)
            simp only [hnone, hnone', simulateQ_pure, WriterT.run_pure, map_pure, mul_one, ← ofAdd_add]

theorem fixed_layersCostSearch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (index : Index) :
    simulateQ (fixedCostSource f table)
        (sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearch parameter data index)) =
      WriterT.mk (PMF.pure (assembledEncodings f parameter data index,
        Multiplicative.ofAdd (seqCost (layerFound f parameter data index)
          (layerHashCost f parameter data index)))) :=
  fixed_sequenceDep f table _ _ _ (fun lay => fixed_layerCostSearch f parameter data table index lay)

theorem fixed_finishCostSource (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      WriterT.mk (PMF.pure (assembled f parameter data table message randomness,
        Multiplicative.ofAdd (finishHashCost f parameter data message randomness))) := by
  simp only [finishCostSource, simulateQ_bind, fixedCostSource_lift_hash,
    fixedWorldCost_lift_hash, fixedCostSource_tick, fixed_layersCostSearch]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind, assembled, finishHashCost, hashCalls_messageDigest,
    assembledEncodings]
  cases hs : Completeness.allSome fun lay : Layer => firstEncoding f parameter lay
      (treeIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest))) lay)
      (leafIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest))) lay)
      (data.keyMessage lay _ _) encodingAttemptLimit 0 with
  | none =>
      simp only [simulateQ_pure, WriterT.run_pure, Option.map_none, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]
  | some found =>
      have hvalues : simulateQ (fixedCostSource f table) (sequenceFin fun lay : Layer => sequenceFin fun chain =>
          HiddenCost.reveal (D := HashInput) (R := HashOutput)
            (.chain lay (treeIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
              message randomness : OracleComp HashSpec MessageDigest))) lay)
              (leafIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
                message randomness : OracleComp HashSpec MessageDigest))) lay) chain ((found lay).2 chain))) =
          pure (assembledValues table (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root
            message randomness : OracleComp HashSpec MessageDigest))) found) := by
        apply fixedCostSource_sequenceFin_pure
        intro lay
        exact fixedCostSource_sequence_reveal f table _
      simp only [simulateQ_bind, hvalues, fixed_forsCostSource, pure_bind,
        simulateQ_pure, WriterT.run_pure, pure_bind,
        Option.map_some, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]

theorem finishCostSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      simulateQ (fixedWorldCost f)
        (liftM (Seeded.finishSign ⟨seed, parameter, data.root⟩ message randomness) :
          OracleComp OracleWorld (Option Signature)) := by
  rw [fixed_finishCostSource, fixedWorldCost_lift_hash,
    eval_finishSign_assembled f parameter seed data table hdata htable message randomness hland,
    hashCalls_finishSign_exact f parameter seed data hdata message randomness hland]

/-- The scan from a start with a step: no randomness. -/
noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) (step : Randomness) : Nat → Randomness → OracleComp CostSpec (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← liftM (messageDigestCall parameter data.root message randomness firstCall :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceLoop parameter data message step attempts (randomness + step)

/-- The step of the walk of `message`. -/
def PublicData.step (data : PublicData) (message : Message) : Randomness := walkStep (data.steps message)

/-- One uniform start, then the scan with the message's step. -/
noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  let start ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceLoop parameter data message (data.step message) digestAttemptLimit start

end FORS.Security.GraphView

end

section

/-! The counted graph signer composed through an arbitrary adaptive adversary and the actual
verifier: explicit-reveal cost programs for the interaction, the rest of the game and the whole
game, which retain the strong signing log, and the cost of key generation on a fixed answer
function. -/

open OracleComp OracleSpec
namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph SeedCoupling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] signCostSource Seeded.keygenFromSeed

def ordinaryCostSource : QueryImpl OracleWorld (OracleComp CostSpec)
  | .inl request => liftM (CostSpec.query (.inl (.inl request)))
  | .inr request => liftM (CostSpec.query (.inl (.inr (.inl request))))

theorem fixedCostSource_ordinary (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (request : OracleWorld.Domain) :
    simulateQ (fixedCostSource f table) (ordinaryCostSource request) = fixedWorldCost f request := by
  cases request <;> rw [ordinaryCostSource, simulateQ_spec_query] <;> rfl


noncomputable def costInteraction (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) :=
  ordinaryCostSource.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpec)) +
    QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message)

noncomputable def costRest (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteraction parameter data) (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpec Bool := do
  HiddenCost.tick keygenHashCost
  costRest parameter data adversary

theorem fixedWorldCost_keygen_graph (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (hdata : DataCorrect f parameter seed data)
    (hparameter : evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter) :
    simulateQ (fixedWorldCost f) (liftM (Seeded.keygenFromSeed seed) :
      OracleComp OracleWorld (PublicKey × Seeded.SecretKey)) =
      WriterT.mk (PMF.pure ((⟨data.root, parameter⟩, ⟨seed, parameter, data.root⟩),
        Multiplicative.ofAdd keygenHashCost)) := by
  rw [fixedWorldCost_lift_hash, hashCalls_keygenFromSeed]
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    hparameter, ← hdata.root]

end FORS.Security.GraphView

end
