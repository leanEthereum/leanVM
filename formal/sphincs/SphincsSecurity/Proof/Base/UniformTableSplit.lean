import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.IdealStatement

namespace SphincsSecurity.Concrete.UniformTableSplit

open _root_.OracleComp ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index Cell Answer : Type}

abbrev Outside (embed : Index → Cell) := {cell : Cell // cell ∉ Set.range embed}

theorem inclusion_not_range {α : Type} {small large : Set α} (hsubset : small ⊆ large)
    (cell : large) (houtside : cell.val ∉ small) : cell ∉ Set.range (Set.inclusion hsubset) := by
  rintro ⟨input, heq⟩
  exact houtside ((congrArg Subtype.val heq) ▸ input.property)

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

@[simp] theorem join_split (embed : Index → Cell) (hinj : Function.Injective embed) (table : Cell → Answer) :
    join embed hinj (table ∘ embed) (fun cell => table cell.val) = table := by
  rw [← split_fst embed hinj table, ← split_snd embed hinj table]
  exact (split embed hinj).symm_apply_apply table

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

theorem uniform_bind_split {Result : Type} (embed : Index → Cell) (hinj : Function.Injective embed)
    (next : (Cell → Answer) → PMF Result) :
    (PMF.uniformOfFintype (Cell → Answer)).bind next =
      (PMF.uniformOfFintype (Index → Answer)).bind (fun rows =>
        (PMF.uniformOfFintype (Outside embed → Answer)).bind (fun outside => next (join embed hinj rows outside))) := by
  conv_lhs => rw [uniform_join embed hinj]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

end SphincsSecurity.Concrete.UniformTableSplit
