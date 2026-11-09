module

public import Batteries.Data.Fin.Coding
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.BitVec
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.IrreducibleDef
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
public import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.SubSpec
public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.ProgramLogic.Relational.ProgrammingOracle
public import VCVio.ProgramLogic.Relational.Quantitative
public import FORS.Base.Probability

@[expose] public section

/-!
Generic oracle and sampling lemmas the proof uses: counting selected queries (`QueryCap.counted`),
splitting a uniform table along an injection (`UniformTableSplit.uniform_join`), and extracting one
cell of a uniform table (`FiniteGraphSampling.evalDist_table_extract`).
-/

set_option backward.isDefEq.respectTransparency false

namespace FORS.QueryCap

open _root_.OracleComp OracleSpec

variable {Index : Type} {spec : OracleSpec Index} {Result Next : Type}
  (selected : Index → Prop) [DecidablePred selected]

noncomputable def counted (computation : OracleComp spec Result) : OracleComp spec (Result × Nat) :=
  OracleComp.construct (fun result => pure (result, 0))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, (if selected input then 1 else 0) + result.2)) computation

theorem counted_pure (result : Result) : counted selected (pure result : OracleComp spec Result) = pure (result, 0) := rfl

theorem counted_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    counted selected (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← counted selected (next answer)
      pure (result.1, (if selected input then 1 else 0) + result.2)) := rfl

theorem counted_query (input : spec.Domain) :
    counted selected (liftM (spec.query input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$>
        (liftM (spec.query input) : OracleComp spec _) := by
  change (do
    let answer ← liftM (spec.query input)
    pure (answer, (if selected input then 1 else 0) + 0)) = _
  simp only [Nat.add_zero, pure_bind, bind_pure_comp]

theorem simulate_withCost {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    simulateQ impl (counted selected computation) =
      (simulateQ (impl.withAddCost (fun input => if selected input then 1 else (0 : Nat))) computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih,
        WriterT.run_bind]
      simp [QueryImpl.withAddCost, QueryImpl.withCost,
        WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, map_eq_bind_pure_comp, bind_assoc]
      rfl

theorem counted_bind (computation : OracleComp spec Result) (next : Result → OracleComp spec Next) :
    counted selected (computation >>= next) = (do
      let first ← counted selected computation
      let second ← counted selected (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, counted_pure, zero_add, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, counted_query_bind, ih, pure_bind, Nat.add_assoc]

theorem counted_map (computation : OracleComp spec Result) (f : Result → Next) :
    counted selected (f <$> computation) = (fun result => (f result.1, result.2)) <$> counted selected computation := by
  rw [show f <$> computation = computation >>= fun result => pure (f result) from (bind_pure_comp f computation).symm,
    counted_bind]
  simp only [counted_pure, Nat.add_zero, bind_pure_comp, map_pure]

end FORS.QueryCap

namespace FORS.UniformTableSplit

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable

variable {Index Cell Answer : Type}

abbrev Outside (embed : Index → Cell) := {cell : Cell // cell ∉ Set.range embed}

noncomputable def split (embed : Index → Cell) (hinj : Function.Injective embed) :
    (Cell → Answer) ≃ (Index → Answer) × (Outside embed → Answer) :=
  (Equiv.arrowCongr ((Equiv.Set.sumCompl (Set.range embed)).symm.trans
    ((Equiv.ofInjective embed hinj).symm.sumCongr (Equiv.refl (Outside embed)))) (Equiv.refl Answer)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _)

theorem split_fst (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    (split embed hinj table).1 = table ∘ embed := by
  funext index
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]

theorem split_snd (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    (split embed hinj table).2 = fun cell => table cell.val := by
  funext cell
  simp [split, Equiv.sumArrowEquivProdArrow, Equiv.ofInjective]
  rfl

noncomputable def join (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) : Cell → Answer :=
  (split embed hinj).symm (rows, outside)

@[simp] theorem join_embed (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (index : Index) :
    join embed hinj rows outside (embed index) = rows index := by
  have h := congrArg Prod.fst ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_fst] at h
  exact congrFun h index

@[simp] theorem join_outside (embed : Index → Cell) (hinj : Function.Injective embed)
    (rows : Index → Answer) (outside : Outside embed → Answer) (cell : Outside embed) :
    join embed hinj rows outside cell.val = outside cell := by
  have h := congrArg Prod.snd ((split embed hinj).apply_symm_apply (rows, outside))
  rw [split_snd] at h
  exact congrFun h cell

theorem uniform_product {Left Right : Type} [Fintype Left] [Fintype Right] [Nonempty Left] [Nonempty Right] :
    Cslib.Probability.PMF.uniformOfFintype (Left × Right) =
      (Cslib.Probability.PMF.uniformOfFintype Left).bind (fun left => (Cslib.Probability.PMF.uniformOfFintype Right).map (fun right => (left, right))) := by
  classical
  let : DecidableEq Left := Classical.decEq Left
  let : DecidableEq Right := Classical.decEq Right
  apply PMF.ext
  rintro ⟨left, right⟩
  have hmap : ∀ a : Left,
      (Cslib.Probability.PMF.uniformOfFintype Right).map (fun b => (a, b)) (left, right) =
        if a = left then Cslib.Probability.PMF.uniformOfFintype Right right else 0 := by
    intro a
    rw [PMF.map_apply]
    by_cases ha : a = left
    · subst a
      rw [ite_eq_left rfl, tsum_eq_single right]
      · rw [ite_eq_left rfl]
      · intro b hb
        exact ite_eq_right (fun h => hb (congrArg Prod.snd h).symm)
    · rw [ite_eq_right ha]
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      exact ite_eq_right (fun h => ha (congrArg Prod.fst h).symm)
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single left]
  · simp only [ite_true, Cslib.Probability.PMF.uniformOfFintype_apply]
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]
  · intro a ha
    exact ite_eq_right ha

variable [Fintype Index] [Fintype Cell] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Index] [DecidableEq Cell]

theorem uniform_join (embed : Index → Cell) (hinj : Function.Injective embed) :
    Cslib.Probability.PMF.uniformOfFintype (Cell → Answer) =
      (Cslib.Probability.PMF.uniformOfFintype (Index → Answer)).bind (fun rows =>
        (Cslib.Probability.PMF.uniformOfFintype (Outside embed → Answer)).map (join embed hinj rows)) := by
  unfold join
  have h := Cslib.Probability.PMF.uniformOfFintype_map_of_bijective (split (Answer := Answer) embed hinj).symm
    (split embed hinj).symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def] using h.symm

end FORS.UniformTableSplit

namespace FORS.FiniteGraphSampling

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling

variable {Cell Answer : Type} [DecidableEq Cell] [_root_.Finite Cell] [_root_.Finite Answer] [Nonempty Answer]
  [SampleableType Answer] [SampleableType (Cell → Answer)]

theorem evalDist_table_extract {Result : Type} (cell : Cell)
    (next : (Cell → Answer) → Answer → ProbComp Result) :
    (do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)) =ᵈ (do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer) := by
  let : MeasurableSpace Answer := ⊤
  let : MeasurableSpace Result := ⊤
  exact EvalDistEq.of_evalDist_eq <| evalDist_bind_cell_extract ($ᵗ Answer) ($ᵗ (Cell → Answer))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample cell next

end FORS.FiniteGraphSampling
