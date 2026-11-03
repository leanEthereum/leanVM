import Batteries.Data.Fin.Coding
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.BitVec
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.ProgramLogic.Relational.ProgrammingOracle
import VCVio.ProgramLogic.Relational.Quantitative

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
  simp only [Nat.add_zero, bind_pure_comp]

theorem simulate_withCost {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    simulateQ impl (counted selected computation) =
      (simulateQ (impl.withAddCost (fun input => if selected input then 1 else (0 : Nat))) computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih,
        WriterT.run_bind]
      simp [QueryImpl.withAddCost, QueryImpl.withCost, QueryImpl.withTraceBefore_apply,
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
    PMF.uniformOfFintype (Left × Right) =
      (PMF.uniformOfFintype Left).bind (fun left => (PMF.uniformOfFintype Right).map (fun right => (left, right))) := by
  classical
  letI : DecidableEq Left := Classical.decEq Left
  letI : DecidableEq Right := Classical.decEq Right
  apply PMF.ext
  rintro ⟨left, right⟩
  have hmap : ∀ a : Left,
      (PMF.uniformOfFintype Right).map (fun b => (a, b)) (left, right) =
        if a = left then PMF.uniformOfFintype Right right else 0 := by
    intro a
    rw [PMF.map_apply]
    by_cases ha : a = left
    · subst a
      rw [if_pos rfl, tsum_eq_single right]
      · rw [if_pos rfl]
      · intro b hb
        exact if_neg (fun h => hb (congrArg Prod.snd h).symm)
    · rw [if_neg ha]
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      exact if_neg (fun h => ha (congrArg Prod.fst h).symm)
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single left]
  · simp only [if_true, PMF.uniformOfFintype_apply]
    rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp)]
  · intro a ha
    exact if_neg ha

variable [Fintype Index] [Fintype Cell] [Fintype Answer] [Nonempty Answer]
  [DecidableEq Index] [DecidableEq Cell]

theorem uniform_join (embed : Index → Cell) (hinj : Function.Injective embed) :
    PMF.uniformOfFintype (Cell → Answer) =
      (PMF.uniformOfFintype (Index → Answer)).bind (fun rows =>
        (PMF.uniformOfFintype (Outside embed → Answer)).map (join embed hinj rows)) := by
  unfold join
  have h := PMF.uniformOfFintype_map_of_bijective (split (Answer := Answer) embed hinj).symm
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
    𝒟[do let table ← ($ᵗ (Cell → Answer) : ProbComp _); next table (table cell)] =
      𝒟[do
        let answer ← ($ᵗ Answer : ProbComp _)
        let table ← ($ᵗ (Cell → Answer) : ProbComp _)
        next (Function.update table cell answer) answer] := by
  have h := congrArg (fun distribution : SPMF (Cell → Answer) =>
    distribution >>= fun table => 𝒟[next table (table cell)])
    (evalDist_uniformSample_bind_update (R := Answer) cell)
  simpa only [evalDist_bind, bind_assoc, evalDist_pure, pure_bind, Function.update_self] using h.symm

end FORS.FiniteGraphSampling
