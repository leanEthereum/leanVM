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

theorem AgreeBelow.trans {k : ℕ} {σ σ' σ'' : Val} (h : AgreeBelow k σ σ') (h' : AgreeBelow k σ' σ'') :
    AgreeBelow k σ σ'' := fun i hi ↦ (h' i hi).trans (h i hi)

theorem AgreeBelow.mono {k k' : ℕ} {σ σ' : Val} (h : AgreeBelow k' σ σ') (hk : k ≤ k') :
    AgreeBelow k σ σ' := fun i hi ↦ h i (by omega)

/-- **A block**: some values on `[k, k')` make `ss` and `Out` hold. -/
def Blk (C : CallRel) (rd : Reader) (σ : Val) (k k' : ℕ) (ss : List Stmt) (Out : Val → Prop) :
    Prop :=
  ∃ f : ℕ → E, ∀ σ', AgreeBelow k σ σ' → RangeVals σ' k k' f → AllOk C rd σ' ss ∧ Out σ'

variable {C : CallRel} {rd : Reader}

/-- **Two blocks in sequence**, the second from any valuation the first leaves. -/
theorem Blk.seq {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : Blk C rd σ k k1 A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → Blk C rd σ1 k1 k2 B OutB) :
    Blk C rd σ k k2 (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  obtain ⟨fA, hfA⟩ := hA
  set σ1 := fill σ k k1 fA with hσ1
  have ⟨_, hO1⟩ := hfA σ1 (agree_fill _ _ _ _) (range_fill _ _ _ _)
  obtain ⟨fB, hfB⟩ := hB σ1 (agree_fill _ _ _ _) hO1
  refine ⟨fun i ↦ if i < k1 then fA i else fB i, fun σ' ha hr ↦ ?_⟩
  have hrA : RangeVals σ' k k1 fA := fun i hi1 hi2 ↦ by
    rw [hr i hi1 (by omega)]; simp only [hi2, ↓reduceIte]
  have hrB : RangeVals σ' k1 k2 fB := fun i hi1 hi2 ↦ by
    rw [hr i (by omega) hi2]; simp only [show ¬ i < k1 by omega, ↓reduceIte]
  have hab : AgreeBelow k1 σ1 σ' := fun i hi ↦ by
    by_cases hk : i < k
    · rw [ha i hk, hσ1, fill_lt hk]
    · rw [hrA i (by omega) hi, hσ1, fill_in (by omega) hi]
  obtain ⟨okA, oA⟩ := hfA σ' ha hrA
  obtain ⟨okB, oB⟩ := hfB σ' hab hrB
  exact ⟨allOk_append.mpr ⟨okA, okB⟩, oA, oB⟩

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

/-- The values of two blocks in sequence: the first's, then the second's from the valuation the
first leaves. -/
def seqF (σ : Val) (k k1 : ℕ) (fA : ℕ → E) (fB : Val → ℕ → E) : ℕ → E :=
  fun i ↦ if i < k1 then fA i else fB (fill σ k k1 fA) i

/-- **Two blocks in sequence, their values named.** -/
theorem BlkF.seq {σ : Val} {k k1 k2 : ℕ} {A B : List Stmt} {OutA OutB : Val → Prop}
    {fA : ℕ → E} {fB : Val → ℕ → E}
    (h1 : k ≤ k1) (h2 : k1 ≤ k2) (hA : BlkF C rd σ k k1 fA A OutA)
    (hB : ∀ σ1, AgreeBelow k σ σ1 → OutA σ1 → BlkF C rd σ1 k1 k2 (fB σ1) B OutB) :
    BlkF C rd σ k k2 (seqF σ k k1 fA fB) (A ++ B) (fun σ' ↦ OutA σ' ∧ OutB σ') := by
  set σ1 := fill σ k k1 fA with hσ1
  have ⟨_, hO1⟩ := hA σ1 (agree_fill _ _ _ _) (range_fill _ _ _ _)
  have hfB := hB σ1 (agree_fill _ _ _ _) hO1
  intro σ' ha hr
  have hrA : RangeVals σ' k k1 fA := fun i hi1 hi2 ↦ by
    rw [hr i hi1 (by omega)]; simp only [seqF, hi2, ↓reduceIte]
  have hrB : RangeVals σ' k1 k2 (fB σ1) := fun i hi1 hi2 ↦ by
    rw [hr i (by omega) hi2]; simp only [seqF, show ¬ i < k1 by omega, ↓reduceIte, hσ1]
  have hab : AgreeBelow k1 σ1 σ' := fun i hi ↦ by
    by_cases hk : i < k
    · rw [ha i hk, hσ1, fill_lt hk]
    · rw [hrA i (by omega) hi, hσ1, fill_in (by omega) hi]
  obtain ⟨okA, oA⟩ := hA σ' ha hrA
  obtain ⟨okB, oB⟩ := hfB σ' hab hrB
  exact ⟨allOk_append.mpr ⟨okA, okB⟩, oA, oB⟩

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

/-- Values given as consecutive segments `(length, values)`. -/
def segLookup : List (ℕ × (ℕ → E)) → ℕ → E
  | [], _ => 0
  | (n, g) :: rest, j => if j < n then g j else segLookup rest (j - n)

/-- The total length of segments. -/
def segLen (segs : List (ℕ × (ℕ → E))) : ℕ := (segs.map (·.1)).sum

theorem segLookup_get : ∀ (segs : List (ℕ × (ℕ → E))) (m : ℕ) (hm : m < segs.length) (i : ℕ)
    (_ : i < segs[m].1), segLookup segs (segLen (segs.take m) + i) = segs[m].2 i
  | (n, g) :: _, 0, _, i, hi => by simp [segLookup, segLen, show i < n from hi]
  | (n, g) :: rest, m + 1, hm, i, hi => by
    have := segLookup_get rest m (by simpa using hm) i (by simpa using hi)
    simp only [List.take_succ_cons, segLen, List.map_cons, List.sum_cons, segLookup,
      List.getElem_cons_succ] at this ⊢
    simp only [show ¬ (n + (List.map (·.1) (List.take m rest)).sum + i < n) by omega, ↓reduceIte]
    rw [show n + (List.map (·.1) (List.take m rest)).sum + i - n =
      (List.map (·.1) (List.take m rest)).sum + i by omega]
    exact this

theorem segLen_take_add_le : ∀ (segs : List (ℕ × (ℕ → E))) (m : ℕ) (hm : m < segs.length),
    segLen (segs.take m) + segs[m].1 ≤ segLen segs
  | (n, g) :: rest, 0, _ => by simp [segLen]
  | (n, g) :: rest, m + 1, hm => by
    have := segLen_take_add_le rest m (by simpa using hm)
    simp only [segLen, List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ] at this ⊢
    omega

/-- **A segment's values** in a valuation holding the segments from `k`. -/
theorem seg_val {σ : Val} {k : ℕ} {segs : List (ℕ × (ℕ → E))}
    (hv : ∀ j < segLen segs, σ (.n (k + j)) = segLookup segs j) (m : ℕ) (hm : m < segs.length)
    (o : ℕ) (ho : segLen (segs.take m) = o) (i : ℕ) (hi : i < segs[m].1) :
    σ (.n (k + o + i)) = segs[m].2 i := by
  have := segLen_take_add_le segs m hm
  rw [Nat.add_assoc, hv _ (by omega), ← ho]
  exact segLookup_get segs m hm i hi

/-- A block whose outcome holds of every later valuation agreeing below `k'`. -/
def Stable (k' : ℕ) (Out : Val → Prop) : Prop := ∀ σ σ', Out σ → AgreeBelow k' σ σ' → Out σ'

end
end LeanVM.Guest.B1.Whir
