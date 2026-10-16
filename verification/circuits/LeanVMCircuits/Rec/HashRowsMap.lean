module

public import LeanVMCircuits.Rec.HashRows

@[expose] public section

/-!
`HashRows.rowsOf` at another valuation of the slots: an additive map of the slots' values maps every row's forms
(`rowsOf_map`). At `δ = unit` the rows are `hashA0`'s and `hashB0`'s, so `checkhashrows`, which evaluates `rowsOf` at
column weights and compares the values with Rust's `Circuit::row_values` of `Hash::circuit`, reads those matrices' rows
at the weights.
-/

namespace LeanVMCircuits.Rec.HashRows

open LeanVMCircuits Gates Blake2s Flock

attribute [local irreducible] program Compress.artifact

variable {α : Type} [Add α]

section Map

variable {β : Type} [Add β] (f : α → β)

/-- A builder part way, its forms mapped by `f`. -/
def St.map (st : St α) : St β where
  rows := st.rows.map fun r => (r.1, f r.2.1, f r.2.2)
  next := st.next
  σ i := (st.σ i).map f

omit [Add α] [Add β] in
theorem update_map (σ : ℕ → Option α) (o : ℕ) (v : Option α) :
    (fun i => (Function.update σ o v i).map f) = Function.update (fun i => (σ i).map f) o (v.map f) := by
  funext i
  by_cases h : i = o
  · subst h
    simp
  · simp [Function.update_of_ne h]

variable {f} (hf : ∀ a b, f (a + b) = f a + f b) (δ : ℕ → α)
include hf

theorem wxor_map (x y : Option α) : (wxor x y).map f = wxor (x.map f) (y.map f) := by
  cases x <;> cases y <;> simp [wxor, hf]

theorem emit_map (σ : ℕ → Option α) (e : Affine) :
    (emit δ σ e).map f = emit (f ∘ δ) (fun i => (σ i).map f) e := by
  induction e with
  | zero => rfl
  | one => rfl
  | var i => rfl
  | xor a b iha ihb => simp only [emit, wxor_map hf, iha, ihb]

theorem step_map (st : St α) (s : Step) : (step δ st s).map f = step (f ∘ δ) (st.map f) s := by
  cases s with
  | define o v =>
    simp only [step, St.map, ← emit_map hf, update_map]
  | product o l r =>
    have hl' : emit (f ∘ δ) (st.map f).σ l = (emit δ st.σ l).map f := (emit_map hf δ _ l).symm
    have hr' : emit (f ∘ δ) (st.map f).σ r = (emit δ st.σ r).map f := (emit_map hf δ _ r).symm
    cases hl : emit δ st.σ l <;> cases hr : emit δ st.σ r <;>
      simp only [step, hl, hr, hl', hr', Option.map_some, Option.map_none] <;>
      simp [St.map, update_map]

theorem foldl_map (steps : List Step) (st : St α) :
    (steps.foldl (step δ) st).map f = steps.foldl (step (f ∘ δ)) (st.map f) := by
  induction steps generalizing st with
  | nil => rfl
  | cons s rest ih => simp only [List.foldl_cons, ih, step_map hf]

omit hf [Add α] [Add β] in
theorem init_map : (init δ).map f = init (f ∘ δ) := by
  simp only [St.map, init, List.map_cons, List.map_map, St.mk.injEq, true_and]
  refine ⟨rfl, ?_⟩
  funext v
  split <;> rfl

theorem outRows_map (σ : ℕ → Option α) :
    (outRows δ σ).map (fun r => (r.1, f r.2.1, f r.2.2)) = outRows (f ∘ δ) (fun i => (σ i).map f) := by
  simp only [outRows, List.map_filterMap]
  congr 1
  funext k
  rw [← emit_map hf]
  cases emit δ σ (outAff k) <;> rfl

/-- `rowsOf` at `f ∘ δ` is `rowsOf` at `δ`, each row's forms mapped by `f`: at `δ = unit` the rows are `hashA0`'s and
`hashB0`'s, so `checkhashrows`, which evaluates `rowsOf` at column weights, reads those matrices' rows at the weights. -/
theorem rowsOf_map : rowsOf (f ∘ δ) = (rowsOf δ).map fun r => (r.1, f r.2.1, f r.2.2) := by
  have h : (run δ).map f = run (f ∘ δ) := by
    unfold run
    rw [foldl_map hf, init_map δ]
  unfold rowsOf
  rw [← h, List.map_append, outRows_map hf]
  rfl

end Map

end LeanVMCircuits.Rec.HashRows
