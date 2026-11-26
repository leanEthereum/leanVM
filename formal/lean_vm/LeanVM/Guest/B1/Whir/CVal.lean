/-
  LeanVM.Guest.B1.Whir.CVal

  Building a valuation block by block, for the completeness direction.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# Valuations, block by block

The template numbers its values in order: a block reads values below its first `k` and writes
`[k, k')`. `Blk C rd σ k k' ss Out`: from the valuation `σ` (its values below `k` fixed), some
values `f` on `[k, k')` make every valuation agreeing with `σ` below `k` and with `f` on
`[k, k')` hold `ss` and `Out`. Blocks compose in sequence (`Blk.seq`), the second built on any
valuation the first leaves (`fill`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- `σ'` agrees with `σ` on the values `.n i`, `i < k`. -/
def AgreeBelow (k : ℕ) (σ σ' : Val) : Prop := ∀ i < k, σ' (.n i) = σ (.n i)

/-- `σ` holds `f i` at `.n i`, `k ≤ i < k'`. -/
def RangeVals (σ : Val) (k k' : ℕ) (f : ℕ → E) : Prop := ∀ i, k ≤ i → i < k' → σ (.n i) = f i

/-- `σ` with `f` on `[k, k')`. -/
def fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : Val := fun v ↦
  if v.path = [] ∧ v.tag = 0 ∧ k ≤ v.idx ∧ v.idx < k' then f v.idx else σ v

theorem fill_lt {σ : Val} {k k' i : ℕ} {f : ℕ → E} (h : i < k) : fill σ k k' f (.n i) = σ (.n i) := by
  unfold fill
  rw [ite_eq_right_iff]
  intro h'
  exact absurd h'.2.2.1 (by simp; omega)

theorem fill_in {σ : Val} {k k' i : ℕ} {f : ℕ → E} (h1 : k ≤ i) (h2 : i < k') :
    fill σ k k' f (.n i) = f i := by
  unfold fill
  rw [ite_eq_left_iff]
  intro h'
  exact absurd ⟨rfl, rfl, h1, h2⟩ h'

theorem agree_fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : AgreeBelow k σ (fill σ k k' f) :=
  fun _ h ↦ fill_lt h

theorem range_fill (σ : Val) (k k' : ℕ) (f : ℕ → E) : RangeVals (fill σ k k' f) k k' f :=
  fun _ h1 h2 ↦ fill_in h1 h2

theorem AgreeBelow.mono {k k' : ℕ} {σ σ' : Val} (h : AgreeBelow k' σ σ') (hk : k ≤ k') :
    AgreeBelow k σ σ' := fun i hi ↦ h i (by omega)

/-- **A block**: some values on `[k, k')` make `ss` and `Out` hold. -/
def Blk (C : CallRel) (rd : Reader) (σ : Val) (k k' : ℕ) (ss : List Stmt) (Out : Val → Prop) :
    Prop :=
  ∃ f : ℕ → E, ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → AllOk C rd σ' ss ∧ Out σ'

variable {C : CallRel} {rd : Reader}

theorem Blk.mono {σ : Val} {k k' : ℕ} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : Blk C rd σ k k' ss Out) (hO : ∀ σ', Out σ' → Out' σ') : Blk C rd σ k k' ss Out' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun σ' ha hr ↦ ⟨(hf σ' ha hr).1, hO _ (hf σ' ha hr).2⟩⟩

theorem Blk.nil {σ : Val} {k : ℕ} {Out : Val → Prop} (hO : ∀ σ', AgreeBelow k σ σ' → Out σ') :
    Blk C rd σ k k [] Out :=
  ⟨fun _ ↦ 0, fun σ' ha _ ↦ ⟨allOk_nil, hO σ' ha⟩⟩

/-! ## Blocks with their values named -/

/-- **A block at the values `f`**: every valuation agreeing with `σ` below `k` and holding `f` on
`[k, k')` holds `ss` and `Out`. -/
def BlkF (C : CallRel) (rd : Reader) (σ : Val) (k k' : ℕ) (f : ℕ → E) (ss : List Stmt)
    (Out : Val → Prop) : Prop :=
  ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → AllOk C rd σ' ss ∧ Out σ'

theorem BlkF.blk {σ : Val} {k k' : ℕ} {f : ℕ → E} {ss : List Stmt} {Out : Val → Prop}
    (h : BlkF C rd σ k k' f ss Out) : Blk C rd σ k k' ss Out := ⟨f, h⟩

theorem BlkF.mono {σ : Val} {k k' : ℕ} {f : ℕ → E} {ss : List Stmt} {Out Out' : Val → Prop}
    (h : BlkF C rd σ k k' f ss Out) (hO : ∀ σ', Out σ' → Out' σ') : BlkF C rd σ k k' f ss Out' :=
  fun σ' ha hr ↦ ⟨(h σ' ha hr).1, hO _ (h σ' ha hr).2⟩

theorem BlkF.nil {σ : Val} {k : ℕ} {f : ℕ → E} {Out : Val → Prop}
    (hO : ∀ σ', AgreeBelow k σ σ' → Out σ') : BlkF C rd σ k k f [] Out :=
  fun σ' ha _ ↦ ⟨allOk_nil, hO σ' ha⟩

theorem BlkF.congr {σ : Val} {k k' : ℕ} {f g : ℕ → E} {ss : List Stmt} {Out : Val → Prop}
    (h : BlkF C rd σ k k' f ss Out) (e : ∀ i, k ≤ i → i < k' → f i = g i) :
    BlkF C rd σ k k' g ss Out :=
  fun σ' ha hr ↦ h σ' ha fun i h1 h2 ↦ (hr i h1 h2).trans (e i h1 h2).symm

/-! ## Values by segments -/

/-- A block whose outcome holds of every later valuation agreeing below `k'`. -/
def Stable (k' : ℕ) (Out : Val → Prop) : Prop := ∀ σ σ', Out σ → AgreeBelow k' σ σ' → Out σ'

end
end LeanVM.Guest.B1.Whir
