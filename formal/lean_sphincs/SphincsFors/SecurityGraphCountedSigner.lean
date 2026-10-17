import SphincsFors.SecurityGraphCost
import SphincsFors.SecurityPrefixErasedGame

/-! The counted graph-reveal signer. Its final assembly preserves the joint law of the actual
signature and its original hash cost on a fixed answer function. Internal graph work is charged
even when encoding exhausts. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.GraphView
open Concrete Completeness Prefix HiddenGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Randomized.finishSign digestAttemptLimit sequenceFin

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
      simulateQ (fixedHashWorld f) (SphincsBase.QueryCap.counted SourceHash
        (liftM computation : OracleComp OracleWorld α)) := by
    rw [SphincsBase.QueryCap.simulate_withCost]
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

variable [Params]

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  HiddenCost.tick 122569
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forsKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let secrets ← sequenceFin fun tree => HiddenCost.reveal
    (.ftsSecret index tree (digestLeaves digest tree))
  HiddenCost.tick (152 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, secrets, data.forsPath index (digestLeaves digest),
    Fin.cases top (fun i => Fin.elim0 i)⟩

theorem fixed_finishCostSource (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      WriterT.mk (PMF.pure (assembled f parameter data table message randomness,
        Multiplicative.ofAdd (finishHashCost f parameter data message randomness))) := by
  simp only [finishCostSource, simulateQ_bind, fixedCostSource_lift_hash,
    fixedWorldCost_lift_hash, fixedCostSource_tick]
  apply WriterT.ext
  simp only [WriterT.run_bind, WriterT.run_mk, AddWriterT.run_addTell,
    ← PMF.monad_pure_eq_pure, pure_bind, assembled, finishHashCost,
    ReferenceChoice.eval_search, hashCalls_messageDigest]
  cases hs : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forsKey (digestIndex (evalWithAnswerFn f
        (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))))
      encodingAttemptLimit 0 with
  | none =>
      simp only [simulateQ_pure, WriterT.run_pure, Option.map_none, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]
  | some pair =>
      obtain ⟨counter, word⟩ := pair
      simp only [simulateQ_bind, fixedCostSource_sequence_reveal, pure_bind,
        fixedCostSource_tick, simulateQ_pure, WriterT.run_bind, WriterT.run_pure,
        AddWriterT.run_addTell, pure_bind,
        Option.map_some, Option.isSome_some, ↓reduceIte, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]

theorem finishCostSource_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    simulateQ (fixedCostSource f table) (finishCostSource parameter data message randomness) =
      simulateQ (fixedWorldCost f)
        (liftM (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness) :
          OracleComp OracleWorld (Option Signature)) := by
  rw [fixed_finishCostSource, fixedWorldCost_lift_hash,
    eval_finishSign_assembled f parameter seed data table hdata htable message randomness hland,
    hashCalls_finishSign_exact f parameter seed data hdata]

/-- The grinding walk in the graph view: try `rho`, `rho + 1`, ... -/
noncomputable def signCostSourceWalk (parameter : PublicParameter) (data : PublicData)
    (message : Message) : Nat → Randomness → OracleComp CostSpec (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← liftM (messageDigestCall parameter data.root message randomness 0 :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceWalk parameter data message attempts (randomness + 1)

/-- The signer of the seed-free game: a uniform base randomizer, then the walk. -/
noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) (attempts : Nat) : OracleComp CostSpec (Option Signature) := do
  let base ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceWalk parameter data message attempts base

noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) :=
  signCostSourceLoop parameter data message digestAttemptLimit

end SphincsFors.Security.GraphView
