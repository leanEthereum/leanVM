import Sphincs.SecurityGraphCost
import Sphincs.SecurityPrefixErasedGame

/-! The counted graph-reveal signer. Its final assembly preserves the joint law of the actual
signature and its original hash cost on a fixed answer function. Internal graph work is charged
even when encoding exhausts. -/

open OracleComp OracleSpec

namespace Sphincs.Security.GraphView
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

/-- The cost-level reveal of one opened forest chain, at and above its opened position. -/
noncomputable def revealChainCost (index : Index) (c : Coord) (mark : CoordMark) (j : SubIdx) (i : FChain) :
    OracleComp CostSpec (FPos → Digest) :=
  sequenceFin fun k : FPos =>
    if (openedPos mark j i).val ≤ k.val then
      HiddenCost.reveal (D := HashInput) (R := HashOutput) (.fchain index c mark.super j (mark.child j) i k)
    else pure 0

/-- One tree's opening at the cost level. -/
noncomputable def coordCostSource (data : PublicData) (index : Index) (c : Coord) (mark : CoordMark) :
    OracleComp CostSpec CoordOpening := do
  let sub ← sequenceFin fun j => do
    let cols ← sequenceFin fun i => revealChainCost index c mark j i
    return (⟨fun i => cols i (openedPos mark j i),
      data.subPath index c mark.super j (mark.child j)⟩ : SubOpening)
  return ⟨sub, data.topPath index c mark.super⟩

theorem fixed_forestCostSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) (data : PublicData)
    (index : Index) (marks : Coord → CoordMark) :
    simulateQ (fixedCostSource f table) (sequenceFin fun c => coordCostSource data index c (marks c)) =
      pure (assembledForest data table index marks) := by
  apply fixedCostSource_sequenceFin_pure
  intro c
  have hcols : ∀ (j : SubIdx) (i : FChain), simulateQ (fixedCostSource f table) (revealChainCost index c (marks c) j i) =
      pure (fun k : FPos => if (openedPos (marks c) j i).val ≤ k.val then
        table (.fchain index c (marks c).super j ((marks c).child j) i k) else 0) := by
    intro j i
    apply fixedCostSource_sequenceFin_pure
    intro k
    split
    · exact fixedCostSource_reveal f table _
    · exact simulateQ_pure _ _
  have hsub : ∀ j : SubIdx, simulateQ (fixedCostSource f table) (do
      let cols ← sequenceFin fun i => revealChainCost index c (marks c) j i
      return (⟨fun i => cols i (openedPos (marks c) j i),
        data.subPath index c (marks c).super j ((marks c).child j)⟩ : SubOpening)) =
      pure (⟨fun i => table (.fchain index c (marks c).super j ((marks c).child j) i (openedPos (marks c) j i)),
        data.subPath index c (marks c).super j ((marks c).child j)⟩ : SubOpening) := by
    intro j
    rw [simulateQ_bind, fixedCostSource_sequenceFin_pure f table _ _ (hcols j), pure_bind, simulateQ_pure]
    simp only [le_refl, ↓reduceIte]
  rw [coordCostSource, simulateQ_bind, fixedCostSource_sequenceFin_pure f table _ _ hsub, pure_bind,
    simulateQ_pure]
  rfl

variable [Params]

noncomputable def finishCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp CostSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  HiddenCost.tick 118081
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forestKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let opening ← sequenceFin fun c => coordCostSource data index c (digestMarks digest c)
  HiddenCost.tick (152 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, opening, Fin.cases top (fun i => Fin.elim0 i)⟩

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
      (data.forestKey (digestIndex (evalWithAnswerFn f
        (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))))
      encodingAttemptLimit 0 with
  | none =>
      simp only [simulateQ_pure, WriterT.run_pure, Option.map_none, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, Nat.add_zero, map_pure, mul_one]
      simp only [← ofAdd_add, ← Nat.add_assoc]
  | some pair =>
      obtain ⟨counter, word⟩ := pair
      simp only [simulateQ_bind, fixedCostSource_sequence_reveal, fixed_forestCostSource, pure_bind,
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

/-- The scan from a start: no randomness. -/
noncomputable def signCostSourceLoop (parameter : PublicParameter) (data : PublicData)
    (message : Message) : Nat → Randomness → OracleComp CostSpec (Option Signature)
  | 0, _ => pure none
  | attempts + 1, randomness => do
      let first ← liftM (messageDigestCall parameter data.root message randomness :
        OracleComp HashSpec HashOutput)
      if Landed parameter (blockIndex first) then
        finishCostSource parameter data message randomness
      else signCostSourceLoop parameter data message attempts (randomness + 1)

/-- One uniform start, then the scan. -/
noncomputable def signCostSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) : OracleComp CostSpec (Option Signature) := do
  let start ← liftM ($ᵗ Randomness : ProbComp Randomness)
  signCostSourceLoop parameter data message digestAttemptLimit start

end Sphincs.Security.GraphView
