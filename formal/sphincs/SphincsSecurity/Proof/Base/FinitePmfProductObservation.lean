import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessFamily
namespace SphincsSecurity.Concrete.FinitePmfProduct

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index Value : Type} [Fintype Index] [DecidableEq Index] [Fintype Value]

theorem marginal (family : Index → PMF Value) (index : Index) :
    (law family).map (fun values => values index) = family index := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro value
  have hfactor (values : Index → Value) :
      (if value = values index then law family values else 0) =
        ∏ other, if other = index then
          (if value = values other then family other (values other) else 0) else family other (values other) := by
    by_cases hvalue : value = values index
    · rw [if_pos hvalue, apply]
      apply Finset.prod_congr rfl
      intro other _
      by_cases hother : other = index
      · subst other
        simp only [if_true, hvalue]
      · simp only [hother, if_false]
    · rw [if_neg hvalue]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp only [if_true, hvalue, if_false])
  rw [PMF.map_apply, tsum_fintype]
  trans ∑ values : Index → Value, ∏ other, if other = index then
    (if value = values other then family other (values other) else 0) else family other (values other)
  · exact Finset.sum_congr rfl (fun values _ => hfactor values)
  rw [← Fintype.prod_sum (fun other (candidate : Value) =>
    if other = index then (if value = candidate then family other candidate else 0) else family other candidate),
    Finset.prod_eq_single index]
  · simp only [if_true]
    simp
  · intro other _ hother
    simp only [hother, if_false]
    simpa only [tsum_fintype] using PMF.tsum_coe (family other)
  · simp

theorem fin_succ {n : Nat} (family : Fin (n + 1) → PMF Value) :
    law family = (family 0).bind (fun first => (law (fun index : Fin n => family index.succ)).map (Fin.cons first)) := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro values
  have hmap (first : Value) :
      (law (fun index : Fin n => family index.succ)).map (Fin.cons first) values =
        if first = values 0 then law (fun index : Fin n => family index.succ) (Fin.tail values) else 0 := by
    rw [PMF.map_apply]
    by_cases hfirst : first = values 0
    · rw [if_pos hfirst, tsum_eq_single (Fin.tail values)]
      · rw [hfirst, Fin.cons_self_tail, if_pos rfl]
      · intro tail htail
        exact if_neg (fun h => htail (by simpa using (congrArg Fin.tail h).symm))
    · rw [if_neg hfirst]
      apply ENNReal.tsum_eq_zero.mpr
      intro tail
      exact if_neg (fun h => hfirst (by simpa using (congrFun h 0).symm))
  rw [PMF.bind_apply]
  simp only [hmap, mul_ite, mul_zero]
  rw [tsum_eq_single (values 0)]
  · simp only [if_true, apply, Fin.prod_univ_succ, Fin.tail]
  · intro value hvalue
    exact if_neg hvalue

theorem update_apply (family : Index → PMF Value) (index : Index) (replacement : PMF Value)
    (values : Index → Value) :
    law (Function.update family index replacement) values =
      replacement (values index) * ∏ other ∈ Finset.univ.erase index, family other (values other) := by
  rw [apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => Function.update family index replacement other (values other)) (Finset.mem_univ index)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro other hother
  rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]

theorem observe_mass [DecidableEq Value] (family : Index → PMF Value) (index : Index) (value : Value) (values : Index → Value) :
    family index value * law (Function.update family index (PMF.pure value)) values =
      if values index = value then law family values else 0 := by
  classical
  rw [update_apply, apply, ← Finset.mul_prod_erase Finset.univ
    (fun other => family other (values other)) (Finset.mem_univ index)]
  by_cases hvalue : values index = value
  · simp only [hvalue, PMF.pure_apply_self, one_mul, if_true]
  · simp only [PMF.pure_apply, if_false, zero_mul, mul_zero, hvalue]

end SphincsSecurity.Concrete.FinitePmfProduct
