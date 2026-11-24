module

public import FORS.GraphView.CountedGame
public import FORS.LazyRun.HonestRead
import all PolyFun.PFunctor.Handler.Instrumentation

@[expose] public section

section

/-! The graph-reveal signer with honest reads: the signer's hash computations (its WOTS+C counter
searches, the message digest and the landing call) are honest reads of the cost interface, free and
unrecorded, and its honest-work ticks are gone. Key generation's tick, the coordinate reveals and
the adversary's and the verifier's raw queries keep their cost. On a fixed answer function the
signer's answer is the counted signer's (`assembled`), at the cost of its reveals only
(`fixed_finishCostSource`). -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.finishSign digestAttemptLimit sequenceFin

/-- The cost interface with honest reads of raw hash inputs. -/
abbrev CostSpecH := HiddenCost.SourceCostSpec HashInput HashOutput Coordinate HashInput

/-- A hash query as an honest read. -/
noncomputable def honestHash : QueryImpl HashSpec (OracleComp CostSpecH) := fun bytes =>
  HiddenCost.honestRead (D := HashInput) (R := HashOutput) (ι := Coordinate) bytes

/-- A hash computation run through honest reads. -/
noncomputable def liftHonest {α : Type} (computation : OracleComp HashSpec α) : OracleComp CostSpecH α :=
  simulateQ honestHash computation

/-- A hash query as a raw (charged, recorded) query. `liftM` from `HashSpec` into `CostSpecH` is NOT
this: it lands on the honest summand (both summands have the oracle type `HashInput →ₒ HashOutput`),
so a charged hash computation must be lifted with `liftRawH`. -/
def rawHashH : QueryImpl HashSpec (OracleComp CostSpecH) := fun bytes =>
  liftM (CostSpecH.query (.inl (.inr (.inl bytes))))

/-- A hash computation with every read raw (charged). -/
noncomputable def liftRawH {α : Type} (computation : OracleComp HashSpec α) : OracleComp CostSpecH α :=
  simulateQ rawHashH computation

theorem liftRawH_pure {α : Type} (a : α) : liftRawH (pure a : OracleComp HashSpec α) = pure a := by
  simp [liftRawH]

theorem liftRawH_query_bind {α : Type} (q : HashInput) (rest : HashOutput → OracleComp HashSpec α) :
    liftRawH ((liftM (HashSpec.query q) : OracleComp HashSpec HashOutput) >>= rest) =
      liftM (CostSpecH.query (.inl (.inr (.inl q)))) >>= fun v => liftRawH (rest v) := by
  unfold liftRawH
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

/-- The cost interface's answers with a fixed answer function, honest reads answered as the raw
query they stand for. -/
noncomputable def fixedCostAnswer (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpecH PMF
  | .inl request => fixedSource f table request
  | .inr (.inl _) => PMF.pure ()
  | .inr (.inr honest) => fixedSource f table (.inr (.inl honest))

noncomputable def fixedCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl CostSpecH (AddWriterT Nat PMF) :=
  QueryImpl.withAddCost (spec := CostSpecH) (fixedCostAnswer f table) HiddenCost.sourceCost

theorem fixedCostSourceH_honestRead (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (bytes : HashInput) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.honestRead (D := HashInput) (R := HashOutput) (ι := Coordinate) bytes) =
      pure (f bytes) := by
  rw [HiddenCost.honestRead, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, fixedCostAnswer, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, fixedSource, fixedView]
  change (fun a => (a, (1 : Multiplicative Nat))) <$> PMF.pure (f bytes) = _
  simp only [← PMF.monad_pure_eq_pure, map_pure]

/-- An honest hash computation on a fixed answer function: its value, at no cost. -/
theorem fixedCostSourceH_liftHonest (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (liftHonest computation) =
      pure (evalWithAnswerFn f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftHonest, simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind input next ih =>
      simp only [liftHonest] at ih ⊢
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
        id_map]
      simp only [honestHash, fixedCostSourceH_honestRead, pure_bind, ih, evalWithAnswerFn_bind,
        evalWithAnswerFn_liftM_query]

theorem fixedCostSourceH_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (coordinate : Coordinate) :
    simulateQ (fixedCostSource f table)
      (HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput) coordinate) =
      pure (table coordinate) := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  apply WriterT.ext
  simp [fixedCostSource, fixedCostAnswer, QueryImpl.withAddCost, QueryImpl.withCost,
    HiddenCost.sourceCost, fixedSource, fixedView]
  change (fun a => (a, (1 : Multiplicative Nat))) <$> PMF.pure (table coordinate) = _
  simp only [← PMF.monad_pure_eq_pure, map_pure]

theorem fixedCostSourceH_sequenceFin_pure (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} {n : Nat} (computation : Fin n → OracleComp CostSpecH α) (values : Fin n → α)
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

theorem fixedCostSourceH_sequence_reveal (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {n : Nat} (which : Fin n → Coordinate) :
    simulateQ (fixedCostSource f table) (sequenceFin fun index =>
      HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput) (which index)) =
      pure (fun index => table (which index)) :=
  fixedCostSourceH_sequenceFin_pure f table _ _ fun i => fixedCostSourceH_reveal f table (which i)

/-- Sequencing honest computations of fixed results. -/
theorem fixedCostSourceH_sequenceDep_pure (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    ∀ {n : Nat} {α : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpecH (Option (α i)))
      (results : (i : Fin n) → Option (α i)),
      (∀ i, simulateQ (fixedCostSource f table) (computation i) = pure (results i)) →
      simulateQ (fixedCostSource f table) (sequenceDep computation) =
        pure (Completeness.allSome results)
  | 0, _, _, _, _ => by
      simp only [sequenceDep, simulateQ_pure, Completeness.allSome]
      rw [dite_eq_left (fun i => Fin.elim0 i)]
      congr 2
      funext i
      exact i.elim0
  | n + 1, α, computation, results, h => by
      have ih := fixedCostSourceH_sequenceDep_pure f table (α := fun i => α i.castSucc)
        (fun i => computation i.castSucc) (fun i => results i.castSucc) (fun i => h i.castSucc)
      rw [sequenceDep, simulateQ_bind, h (Fin.last _)]
      cases hhead : results (Fin.last _) with
      | none =>
          simp only [pure_bind, simulateQ_pure]
          congr 1
          unfold Completeness.allSome
          rw [dite_eq_right (fun hall => by simpa [hhead] using hall (Fin.last _))]
      | some head =>
          simp only [pure_bind, simulateQ_bind, ih]
          by_cases hall : ∀ i : Fin n, (results i.castSucc).isSome
          · have hsome : Completeness.allSome (fun i : Fin n => results i.castSucc) =
                some fun i => (results i.castSucc).get (hall i) := dite_eq_left hall
            have hall' : ∀ i : Fin (n + 1), (results i).isSome := by
              intro i
              refine Fin.lastCases ?_ (fun j => hall j) i
              simp [hhead]
            have hsome' : Completeness.allSome results = some fun i => (results i).get (hall' i) :=
              dite_eq_left hall'
            simp only [hsome, hsome', simulateQ_pure]
            congr 2
            funext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [hhead]
            · simp
          · have hnone : Completeness.allSome (fun i : Fin n => results i.castSucc) = none :=
              dite_eq_right hall
            have hnone' : Completeness.allSome results = none :=
              dite_eq_right (fun hall' => hall fun i => hall' i.castSucc)
            simp only [hnone, hnone', simulateQ_pure]

/-- One tree's opening with honest reads (the same reveals). -/
noncomputable def treeCostSourceH (data : PublicData) (index : Index) (κ : FTree) (leaf : FLeaf) :
    OracleComp CostSpecH TreeOpening := do
  let values ← sequenceFin fun k : Fin 2 =>
    HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput) (.fors index κ leaf k)
  return ⟨values 0, data.forsPath index κ leaf⟩

theorem fixed_forsCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) (data : PublicData)
    (index : Index) (leaves : FTree → FLeaf) :
    simulateQ (fixedCostSource f table) (sequenceFin fun κ => treeCostSourceH data index κ (leaves κ)) =
      pure (assembledFors data table index leaves) := by
  apply fixedCostSourceH_sequenceFin_pure
  intro κ
  rw [treeCostSourceH, simulateQ_bind, fixedCostSourceH_sequence_reveal, pure_bind, simulateQ_pure]
  rfl

/-- One layer's WOTS+C counter search, as honest reads (no tick). -/
noncomputable def layerCostSearchH (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) : OracleComp CostSpecH (Option (Counter × Encoding)) :=
  liftHonest (layerSearch parameter data index lay)

/-- The signer after landing, its hash computations as honest reads. -/
noncomputable def finishCostSourceH (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpecH (Option Signature) := do
  let digest ← liftHonest (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let some found ← sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearchH parameter data index)
    | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain =>
    HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput)
      (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun κ => treeCostSourceH data index κ (digestLeaves digest κ)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

/-- **The honest signer after landing, on a fixed answer function**: the counted signer's
signature (`fixed_finishCostSource`), at no cost. -/
theorem fixed_finishCostSource (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    simulateQ (fixedCostSource f table) (finishCostSourceH parameter data message randomness) =
      pure (assembled f parameter data table message randomness) := by
  have hlayers : simulateQ (fixedCostSource f table)
      (sequenceDep (α := fun _ => Counter × Encoding) (layerCostSearchH parameter data
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest))))) =
      pure (assembledEncodings f parameter data (digestIndex (evalWithAnswerFn f
        (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) := by
    apply fixedCostSourceH_sequenceDep_pure
    intro lay
    rw [layerCostSearchH, fixedCostSourceH_liftHonest]
    simp only [layerSearch, ReferenceChoice.eval_search]
  simp only [finishCostSourceH, simulateQ_bind, fixedCostSourceH_liftHonest, pure_bind, hlayers,
    assembled]
  cases hs : assembledEncodings f parameter data (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))) with
  | none => simp only [simulateQ_pure, Option.map_none]
  | some found =>
      rw [simulateQ_bind, fixedCostSourceH_sequenceFin_pure f table _ _
        (fun lay => fixedCostSourceH_sequence_reveal f table _), pure_bind, simulateQ_bind,
        fixed_forsCostSource, pure_bind, simulateQ_pure]
      rfl

/-- The scan from a start with a step, the landing calls as honest reads. -/
noncomputable def signCostSourceLoopH (parameter : PublicParameter) (data : PublicData)
    (message : Message) (step : Randomness) : Nat → Randomness → OracleComp CostSpecH (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← liftHonest (messageDigestCall parameter data.root message randomness firstCall :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSourceH parameter data message randomness
      else signCostSourceLoopH parameter data message step attempts (randomness + step)

/-- The honest signer: one uniform start, then the scan with the message's step. -/
noncomputable def signCostSourceH (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpecH (Option Signature) := do
  let start ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceLoopH parameter data message (data.step message) digestAttemptLimit start

/-- The adversary's queries as raw (charged) queries of the honest interface. -/
def ordinaryCostSourceH : QueryImpl OracleWorld (OracleComp CostSpecH)
  | .inl request => liftM (CostSpecH.query (.inl (.inl request)))
  | .inr request => liftM (CostSpecH.query (.inl (.inr (.inl request))))

noncomputable def costInteractionH (parameter : PublicParameter) (data : PublicData) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp CostSpecH)) :=
  QueryImpl.add (ordinaryCostSourceH.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp CostSpecH)))
    (QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
      (fun message => signCostSourceH parameter data message))

/-- The game after key generation: the adversary's and the verifier's queries charged, the
signer's honest. -/
noncomputable def costRest (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpecH Bool := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteractionH parameter data) (adversary.main pk)).run
  let verified ← liftRawH (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The honest-reading game: key generation's cost as a tick, then `costRest`. -/
noncomputable def costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpecH Bool := do
  HiddenCost.tick (H := HashInput) keygenHashCost
  costRest parameter data adversary

theorem fixedCostSourceH_ordinary (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (request : OracleWorld.Domain) :
    simulateQ (fixedCostSource f table) (ordinaryCostSourceH request) = fixedWorldCost f request := by
  cases request <;> rw [ordinaryCostSourceH, simulateQ_spec_query] <;>
    simp only [fixedCostSource, fixedWorldCost, QueryImpl.withAddCost_apply] <;> rfl

/-- A raw-lifted hash computation on a fixed answer function: its value at one cost per call. -/
theorem fixedCostSourceH_liftRawH (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (fixedCostSource f table) (liftRawH computation) =
      simulateQ (fixedWorldCost f) (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftRawH, liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftRawH] at ih
      simp only [liftRawH, liftM_bind, simulateQ_bind, simulateQ_spec_query, ih]
      rfl

end FORS.Security.GraphView

end
