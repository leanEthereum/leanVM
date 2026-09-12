import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessFamily
import SphincsSecurity.Proof.Fts.UnrestrictedRowSwap
namespace SphincsSecurity.Concrete.FirstSuccessPrefix

open ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index Cell Answer Value : Type}

def kept {n : Nat} (result : Option (Fin n × Value)) (coordinate : Fin n) : Prop :=
  result.elim True (fun selected => coordinate ≤ selected.1)

def familyKept {n : Nat} (results : Index → Option (Fin n × Value)) (row : Index × Fin n) : Prop :=
  kept (results row.1) row.2

theorem select_eq_of_kept (decode : Answer → Option Value) {n : Nat} (left right : Fin n → Answer)
    (result : Option (Fin n × Value)) (hselect : FirstSuccessTable.select decode left = result)
    (hkept : ∀ coordinate, kept result coordinate → left coordinate = right coordinate) :
    FirstSuccessTable.select decode right = result := by
  cases result with
  | none =>
      apply (FirstSuccessTable.select_none_iff decode right).mpr
      intro coordinate
      rw [← hkept coordinate trivial]
      exact (FirstSuccessTable.select_none_iff decode left).mp hselect coordinate
  | some result =>
      rcases result with ⟨index, value⟩
      have h := (FirstSuccessTable.select_some_iff decode left index value).mp hselect
      apply (FirstSuccessTable.select_some_iff decode right index value).mpr
      constructor
      · rw [← hkept index (Nat.le_refl _)]
        exact h.1
      · intro coordinate hlt
        rw [← hkept coordinate hlt.le]
        exact h.2 coordinate hlt

theorem kept_nonselected_invalid (decode : Answer → Option Value) {n : Nat} (table : Fin n → Answer)
    (result : Option (Fin n × Value)) (hselect : FirstSuccessTable.select decode table = result)
    (coordinate : Fin n) (hkept : kept result coordinate) (hnot : result.map Prod.fst ≠ some coordinate) :
    decode (table coordinate) = none := by
  cases result with
  | none => exact (FirstSuccessTable.select_none_iff decode table).mp hselect coordinate
  | some result =>
      rcases result with ⟨index, value⟩
      have hle : coordinate ≤ index := hkept
      have hne : coordinate ≠ index := by
        intro heq
        subst coordinate
        exact hnot rfl
      exact ((FirstSuccessTable.select_some_iff decode table index value).mp hselect).2 coordinate (lt_of_le_of_ne hle hne)

variable [Fintype Answer] [DecidableEq Answer] [Nonempty Answer]

theorem afterSelect_congr (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (result : Option (Fin n × Value))
    (left right : Fin n → Answer) (hkept : ∀ coordinate, kept result coordinate → left coordinate = right coordinate) :
    FirstSuccessTable.afterSelect decode n hinvalid result left =
      FirstSuccessTable.afterSelect decode n hinvalid result right := by
  cases result with
  | none =>
      have heq : left = right := funext (fun coordinate => hkept coordinate trivial)
      rw [heq]
  | some result =>
      rcases result with ⟨index, value⟩
      simp only [FirstSuccessTable.afterSelect]
      split
      · simp only [FirstSuccessTable.conditional, uniformTable_apply]
        congr 1
        apply propext
        apply forall_congr'
        intro coordinate
        by_cases hk : coordinate ≤ index
        · rw [hkept coordinate hk]
        · have hlt : ¬coordinate < index := fun h => hk h.le
          have hne : coordinate ≠ index := fun h => hk h.le
          simp only [FirstSuccessTable.allowed, if_neg hlt, if_neg hne, Finset.mem_univ]
      · simp only [FirstSuccessTable.full_eq_uniform, PMF.uniformOfFintype_apply]

variable [Fintype Index] [DecidableEq Index]

noncomputable def familyRows (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value)) :
    PMF (Index × Fin n → Answer) :=
  (FirstSuccessFamily.afterSelect decode n hinvalid results).map Function.uncurry

omit [DecidableEq Answer] in
theorem familyRows_apply (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value))
    (rows : Index × Fin n → Answer) :
    familyRows decode n hinvalid results rows =
      FirstSuccessFamily.afterSelect decode n hinvalid results (Function.curry rows) := by
  rw [familyRows, PMF.map_apply, tsum_eq_single (Function.curry rows)]
  · simp only [Function.uncurry_curry, if_true]
  · intro other hne
    apply if_neg
    intro heq
    apply hne
    funext index coordinate
    exact (congrFun heq (index, coordinate)).symm

theorem familyRows_congr (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value))
    (left right : Index × Fin n → Answer) (hkept : ∀ row, familyKept results row → left row = right row) :
    familyRows decode n hinvalid results left = familyRows decode n hinvalid results right := by
  simp only [familyRows_apply, FirstSuccessFamily.afterSelect, FinitePmfProduct.apply]
  apply Finset.prod_congr rfl
  intro index _
  exact afterSelect_congr decode n hinvalid (results index) _ _ (fun coordinate hk => hkept (index, coordinate) hk)

variable [Fintype Cell] [DecidableEq Cell]

theorem overwrite_eq_prefix (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value))
    (embed : Index × Fin n → Cell) (hinj : Function.Injective embed) :
    (familyRows decode n hinvalid results).bind (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
      (fun seed => ((fun row : {row // familyKept results row} => rows row.val), UniformTableSplit.overwrite embed hinj rows seed))) =
    (familyRows decode n hinvalid results).bind (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
      (fun seed => ((fun row : {row // familyKept results row} => rows row.val),
        UnrestrictedRowSwap.prefixOverwrite embed hinj (familyKept results) rows seed))) :=
  UnrestrictedRowSwap.overwrite_eq_prefix embed hinj (familyKept results) _ (familyRows_congr decode n hinvalid results)

theorem overwrite_table_eq_prefix (decode : Answer → Option Value) (n : Nat)
    (hinvalid : (FirstSuccessTable.invalid decode).Nonempty) (results : Index → Option (Fin n × Value))
    (embed : Index × Fin n → Cell) (hinj : Function.Injective embed) :
    (FirstSuccessFamily.afterSelect decode n hinvalid results).bind
      (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
        (UniformTableSplit.overwrite embed hinj (Function.uncurry rows))) =
    (FirstSuccessFamily.afterSelect decode n hinvalid results).bind
      (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
        (UnrestrictedRowSwap.prefixOverwrite embed hinj (familyKept results) (Function.uncurry rows))) := by
  have h := congrArg (fun law => PMF.map Prod.snd law) (overwrite_eq_prefix decode n hinvalid results embed hinj)
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, familyRows, PMF.bind_map] using h

end SphincsSecurity.Concrete.FirstSuccessPrefix
