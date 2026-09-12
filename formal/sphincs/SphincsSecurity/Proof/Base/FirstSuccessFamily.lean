import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessTable
import SphincsSecurity.Statement

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace FinitePmfProduct

variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]

noncomputable def law (family : Index → PMF Value) : PMF (Index → Value) :=
  PMF.ofFintype (fun values => ∏ index, family index (values index)) (by
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro index _
    simpa only [tsum_fintype] using PMF.tsum_coe (family index))

theorem apply (family : Index → PMF Value) (values : Index → Value) :
    law family values = ∏ index, family index (values index) := rfl

theorem uniform [Nonempty Value] :
    law (fun _ : Index => PMF.uniformOfFintype Value) = PMF.uniformOfFintype (Index → Value) := by
  apply PMF.ext
  intro values
  simp only [apply, PMF.uniformOfFintype_apply, Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

end FinitePmfProduct

namespace FirstSuccessFamily

variable {Index Answer Value : Type} [Fintype Index] [DecidableEq Index]
  [Fintype Answer] [DecidableEq Answer] [Nonempty Answer] [Fintype Value]

def select (decode : Answer → Option Value) (n : Nat) (tables : Index → Fin n → Answer) :
    Index → Option (Fin n × Value) := fun index => FirstSuccessTable.select decode (tables index)

noncomputable def selected (decode : Answer → Option Value) (n : Nat) :
    PMF (Index → Option (Fin n × Value)) :=
  FinitePmfProduct.law (fun _ => FirstSuccessTable.selected decode n)

noncomputable def afterSelect (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value)) :
    PMF (Index → Fin n → Answer) :=
  FinitePmfProduct.law (fun index => FirstSuccessTable.afterSelect decode n hinvalid (results index))

theorem selected_mul_afterSelect (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value))
    (tables : Index → Fin n → Answer) :
    selected decode n results * afterSelect decode n hinvalid results tables =
      if select decode n tables = results then PMF.uniformOfFintype (Index → Fin n → Answer) tables else 0 := by
  rw [selected, afterSelect, FinitePmfProduct.apply, FinitePmfProduct.apply, ← Finset.prod_mul_distrib]
  simp only [FirstSuccessTable.selected_mul_afterSelect]
  by_cases h : select decode n tables = results
  · rw [if_pos h]
    have hcoordinate (index : Index) : FirstSuccessTable.select decode (tables index) = results index := congrFun h index
    simp only [hcoordinate, if_true, FirstSuccessTable.full_eq_uniform]
    exact congrFun (congrArg DFunLike.coe (FinitePmfProduct.uniform (Index := Index) (Value := Fin n → Answer))) tables
  · rw [if_neg h]
    have hex : ∃ index, FirstSuccessTable.select decode (tables index) ≠ results index := by
      by_contra! hall
      exact h (funext hall)
    obtain ⟨index, hindex⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ index) (if_neg hindex)

theorem uniform_bind_eq_selected {Result : Type} (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty)
    (next : (Index → Option (Fin n × Value)) → (Index → Fin n → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Index → Fin n → Answer)).bind (fun tables => next (select decode n tables) tables) =
      (selected decode n).bind (fun results => (afterSelect decode n hinvalid results).bind (next results)) := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, selected_mul_afterSelect,
    ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp

end FirstSuccessFamily

end SphincsSecurity.Concrete
