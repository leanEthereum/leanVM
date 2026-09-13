import SphincsSecurity.Proof.Base.FirstSuccessFamily
import SphincsSecurity.Proof.Base.UniformTableCompletion
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem uniformTable_eq_product {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Value] [DecidableEq Value] (allowed : Coordinate → Finset Value)
    (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    uniformTable allowed ha = FinitePmfProduct.law (fun coordinate => PMF.uniformOfFinset (allowed coordinate) (ha coordinate)) := by
  apply PMF.ext
  intro table
  rw [uniformTable_apply, FinitePmfProduct.apply]
  simp only [PMF.uniformOfFinset_apply]
  by_cases ht : ∀ coordinate, table coordinate ∈ allowed coordinate
  · simp only [ht, implies_true, if_true]
    rw [Nat.cast_prod, ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (by finiteness))]
  · rw [if_neg ht]
    obtain ⟨coordinate, hc⟩ := not_forall.mp ht
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ coordinate) (if_neg hc)

theorem FinitePmfProduct.uncurry {Index Coordinate Value : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Coordinate] [DecidableEq Coordinate] [Fintype Value]
    (family : Index → Coordinate → PMF Value) :
    (law (fun index => law (family index))).map Function.uncurry =
      law (fun coordinate : Index × Coordinate => family coordinate.1 coordinate.2) := by
  classical
  apply PMF.ext
  intro table
  rw [PMF.map_apply, tsum_eq_single (Function.curry table)]
  · simp only [Function.uncurry_curry, if_true, apply]
    rw [Fintype.prod_prod_type]
    rfl
  · intro candidate hne
    apply if_neg
    intro heq
    apply hne
    exact (congrArg Function.curry heq).symm

theorem uniformTable_univ {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Value] [DecidableEq Value] [Nonempty Value] :
    uniformTable (fun _ : Coordinate => (Finset.univ : Finset Value)) (fun _ => Finset.univ_nonempty) =
      PMF.uniformOfFintype (Coordinate → Value) := by
  apply PMF.ext
  intro table
  simp only [uniformTable_apply, Finset.mem_univ, implies_true, if_true, Finset.card_univ,
    Finset.prod_const, Nat.cast_pow, PMF.uniformOfFintype_apply, Fintype.card_fun]

end SphincsSecurity.Concrete
