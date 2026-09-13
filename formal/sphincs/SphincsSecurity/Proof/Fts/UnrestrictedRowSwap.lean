import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.UniformTableOverwrite
namespace SphincsSecurity.Concrete.UnrestrictedRowSwap

open ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Index Cell Answer : Type}

noncomputable def swap (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (pair : (Index → Answer) × (Cell → Answer)) : (Index → Answer) × (Cell → Answer) :=
  (fun index => if kept index then pair.1 index else pair.2 (embed index),
    UniformTableSplit.overwrite embed hinj
      (fun index => if kept index then pair.2 (embed index) else pair.1 index) pair.2)

theorem swap_fst_kept (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (pair : (Index → Answer) × (Cell → Answer)) (index : Index) (hkept : kept index) :
    (swap embed hinj kept pair).1 index = pair.1 index := if_pos hkept

theorem swap_snd_embed (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (pair : (Index → Answer) × (Cell → Answer)) (index : Index) :
    (swap embed hinj kept pair).2 (embed index) = if kept index then pair.2 (embed index) else pair.1 index :=
  UniformTableSplit.overwrite_embed embed hinj _ _ index

theorem swap_snd_outside (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (pair : (Index → Answer) × (Cell → Answer)) (cell : Cell) (hout : cell ∉ Set.range embed) :
    (swap embed hinj kept pair).2 cell = pair.2 cell :=
  UniformTableSplit.overwrite_outside embed hinj _ _ cell hout

theorem swap_involutive (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop) :
    Function.Involutive (swap (Answer := Answer) embed hinj kept) := by
  intro pair
  apply Prod.ext
  · funext index
    change (if kept index then (swap embed hinj kept pair).1 index else (swap embed hinj kept pair).2 (embed index)) = _
    rw [swap_snd_embed]
    by_cases hk : kept index <;> simp only [swap, hk, if_true, if_false]
  · funext cell
    by_cases hin : cell ∈ Set.range embed
    · obtain ⟨index, rfl⟩ := hin
      rw [swap_snd_embed, swap_snd_embed]
      by_cases hk : kept index <;> simp only [swap, hk, if_true, if_false]
    · rw [swap_snd_outside embed hinj kept _ cell hin, swap_snd_outside embed hinj kept _ cell hin]

noncomputable def prefixOverwrite (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (rows : Index → Answer) (seed : Cell → Answer) : Cell → Answer :=
  UniformTableSplit.overwrite embed hinj (fun index => if kept index then rows index else seed (embed index)) seed

theorem prefixOverwrite_embed (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (rows : Index → Answer) (seed : Cell → Answer) (index : Index) :
    prefixOverwrite embed hinj kept rows seed (embed index) = if kept index then rows index else seed (embed index) :=
  UniformTableSplit.overwrite_embed embed hinj _ _ index

theorem prefixOverwrite_outside (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (rows : Index → Answer) (seed : Cell → Answer) (cell : Cell) (hout : cell ∉ Set.range embed) :
    prefixOverwrite embed hinj kept rows seed cell = seed cell :=
  UniformTableSplit.overwrite_outside embed hinj _ _ cell hout

theorem prefixOverwrite_swap (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (pair : (Index → Answer) × (Cell → Answer)) :
    prefixOverwrite embed hinj kept (swap embed hinj kept pair).1 (swap embed hinj kept pair).2 =
      UniformTableSplit.overwrite embed hinj pair.1 pair.2 := by
  funext cell
  by_cases hin : cell ∈ Set.range embed
  · obtain ⟨index, rfl⟩ := hin
    simp only [prefixOverwrite, UniformTableSplit.overwrite_embed, swap_snd_embed]
    by_cases hk : kept index <;> simp only [swap, hk, if_true, if_false]
  · rw [prefixOverwrite, UniformTableSplit.overwrite_outside embed hinj _ _ cell hin,
      swap_snd_outside embed hinj kept _ cell hin, UniformTableSplit.overwrite_outside embed hinj _ _ cell hin]

noncomputable def pairLaw {Left Right : Type} (left : PMF Left) (right : PMF Right) : PMF (Left × Right) :=
  left.bind (fun a => right.map (fun b => (a, b)))

theorem pairLaw_apply {Left Right : Type} (left : PMF Left) (right : PMF Right) (pair : Left × Right) :
    pairLaw left right pair = left pair.1 * right pair.2 := by
  letI : DecidableEq Left := Classical.decEq Left
  letI : DecidableEq Right := Classical.decEq Right
  rcases pair with ⟨a, b⟩
  have hmap (other : Left) : right.map (fun b => (other, b)) (a, b) = if other = a then right b else 0 := by
    rw [PMF.map_apply]
    by_cases heq : other = a
    · subst other
      simp only [Prod.mk.injEq, true_and, ite_true]
      simp
    · simp only [Prod.mk.injEq, heq, Ne.symm heq, false_and, if_false, tsum_zero]
  simp only [pairLaw, PMF.bind_apply, hmap, mul_ite, mul_zero]
  simp

theorem map_involutive {Value : Type} (law : PMF Value) (f : Value → Value)
    (hinv : Function.Involutive f) (hmass : ∀ value, law (f value) = law value) : law.map f = law := by
  letI : DecidableEq Value := Classical.decEq Value
  apply PMF.ext
  intro value
  rw [PMF.map_apply, tsum_eq_single (f value)]
  · rw [if_pos (hinv value).symm, hmass]
  · intro other hne
    exact if_neg (fun h => hne ((hinv other).symm.trans (congrArg f h.symm)))

variable [Fintype Cell] [DecidableEq Cell] [Fintype Answer] [Nonempty Answer]

theorem pairLaw_swap (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (law : PMF (Index → Answer))
    (hkept : ∀ left right, (∀ index, kept index → left index = right index) → law left = law right) :
    (pairLaw law (PMF.uniformOfFintype (Cell → Answer))).map (swap embed hinj kept) =
      pairLaw law (PMF.uniformOfFintype (Cell → Answer)) := by
  apply map_involutive _ _ (swap_involutive embed hinj kept)
  intro pair
  simp only [pairLaw_apply, PMF.uniformOfFintype_apply]
  rw [hkept _ pair.1 (fun index hk => swap_fst_kept embed hinj kept pair index hk)]

theorem overwrite_eq_prefix (embed : Index → Cell) (hinj : Function.Injective embed) (kept : Index → Prop)
    (law : PMF (Index → Answer))
    (hkept : ∀ left right, (∀ index, kept index → left index = right index) → law left = law right) :
    law.bind (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
      (fun seed => ((fun index : {index // kept index} => rows index.val), UniformTableSplit.overwrite embed hinj rows seed))) =
    law.bind (fun rows => (PMF.uniformOfFintype (Cell → Answer)).map
      (fun seed => ((fun index : {index // kept index} => rows index.val), prefixOverwrite embed hinj kept rows seed))) := by
  have h := congrArg (fun distribution : PMF ((Index → Answer) × (Cell → Answer)) => distribution.map
    (fun pair => ((fun index : {index // kept index} => pair.1 index.val), prefixOverwrite embed hinj kept pair.1 pair.2)))
    (pairLaw_swap embed hinj kept law hkept)
  simpa only [PMF.map_comp, Function.comp_def, prefixOverwrite_swap, swap_fst_kept _ _ _ _ _ (Subtype.property _),
    pairLaw, PMF.map_bind] using h

end SphincsSecurity.Concrete.UnrestrictedRowSwap
