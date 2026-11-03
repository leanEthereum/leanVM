import FORS.Base.Domination
import Mathlib

section

open OracleComp

/-! The virtual future used by the FORS forecast potentials. A slot is one future signature:
a fresh uniform view, disclosed and kept as an item, and an independent coin of probability `wbar`
for every existing item, disclosing that item's view again. All potentials are expectations of a
monotone supermodular base function of the final multiset of disclosures. -/

open ENNReal

namespace FORS.Base.Domination

variable {V : Type}

/-! ### Coins with a fixed list -/

theorem slotValue_mono (f : Multiset V → ℝ≥0∞) (hmono : Monotone' f) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)), Monotone' fun current => slotValue f current coins
  | [], small, large, hle => hmono small large hle
  | (p, extra) :: rest, small, large, hle => by
      simp only [slotValue]
      gcongr
      · exact slotValue_mono f hmono rest _ _ (add_le_add hle le_rfl)
      · exact slotValue_mono f hmono rest _ _ hle

theorem slotValue_swap (f : Multiset V → ℝ≥0∞) (first second : ℝ≥0∞ × Multiset V)
    (rest : List (ℝ≥0∞ × Multiset V)) (current : Multiset V) :
    slotValue f current (first :: second :: rest) = slotValue f current (second :: first :: rest) := by
  obtain ⟨p, s⟩ := first
  obtain ⟨q, t⟩ := second
  simp only [slotValue]
  have e : current + s + t = current + t + s := by abel
  rw [e]
  ring

theorem slotValue_perm (f : Multiset V → ℝ≥0∞) {coins coins' : List (ℝ≥0∞ × Multiset V)}
    (hperm : coins.Perm coins') : ∀ current, slotValue f current coins = slotValue f current coins' := by
  induction hperm with
  | nil => intro current; rfl
  | cons head _ ih =>
      intro current
      obtain ⟨p, s⟩ := head
      simp only [slotValue, ih]
  | swap first second rest =>
      intro current
      exact slotValue_swap f second first rest current
  | trans _ _ ih1 ih2 => intro current; rw [ih1, ih2]

theorem slotValue_congr {f g : Multiset V → ℝ≥0∞} (hfg : ∀ m, f m = g m) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) current, slotValue f current coins = slotValue g current coins
  | [], current => hfg current
  | (p, s) :: rest, current => by
      simp only [slotValue, slotValue_congr hfg rest]

theorem slotValue_le_of_le {f g : Multiset V → ℝ≥0∞} (hfg : ∀ m, f m ≤ g m) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) current, slotValue f current coins ≤ slotValue g current coins
  | [], current => hfg current
  | (p, s) :: rest, current => by
      simp only [slotValue]
      gcongr
      · exact slotValue_le_of_le hfg rest _
      · exact slotValue_le_of_le hfg rest _

/-! ### Closure properties -/

/-- Coins attached to items with a common probability. -/
def itemCoins (wbar : ℝ≥0∞) (items : List V) : List (ℝ≥0∞ × Multiset V) :=
  items.map fun w => (wbar, ({w} : Multiset V))

/-! ### The virtual future -/

section Virtual

variable (U : Finset V) (wbar : ℝ≥0∞) (f : Multiset V → ℝ≥0∞)

/-- Expected base value after `m` virtual slots, from the items and the disclosures. -/
noncomputable def virtual : ℕ → List V → Multiset V → ℝ≥0∞
  | 0, _, d => f d
  | m + 1, items, d => freshAvg U fun u => slotValue (virtual m (u :: items)) (d + {u}) (itemCoins wbar items)

variable {U wbar f}

theorem itemCoins_le (hw : wbar ≤ 1) (items : List V) : ∀ c ∈ itemCoins wbar items, c.1 ≤ 1 := by
  intro c hc
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hc
  exact hw

theorem freshAvg_ne_top {g : V → ℝ≥0∞} (hU : U.Nonempty) (hg : ∀ u, g u ≠ ⊤) : freshAvg U g ≠ ⊤ := by
  unfold freshAvg
  refine ENNReal.mul_ne_top ?_ (ENNReal.sum_ne_top.2 fun u _ => hg u)
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hU.card_pos.ne')

end Virtual

/-! ### Items -/

section Items

variable {U : Finset V} {wbar : ℝ≥0∞} {f : Multiset V → ℝ≥0∞}

theorem slotValue_translate (H : Multiset V → ℝ≥0∞) (shift : Multiset V) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) e,
      slotValue (fun x => H (x + shift)) e coins = slotValue H (e + shift) coins
  | [], e => rfl
  | (p, T) :: rest, e => by
      simp only [slotValue, slotValue_translate H shift rest]
      rw [add_right_comm e T shift]

theorem itemCoins_cons (w : V) (items : List V) :
    itemCoins wbar (w :: items) = (wbar, ({w} : Multiset V)) :: itemCoins wbar items := rfl

end Items

/-! ### Linearity and order in the base function -/

section Linear

variable {U : Finset V} {wbar : ℝ≥0∞}

theorem slotValue_add (f g : Multiset V → ℝ≥0∞) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) current,
      slotValue (fun m => f m + g m) current coins = slotValue f current coins + slotValue g current coins
  | [], current => rfl
  | (p, s) :: rest, current => by
      simp only [slotValue, slotValue_add f g rest]
      ring

theorem slotValue_const_mul (c : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) current,
      slotValue (fun m => c * f m) current coins = c * slotValue f current coins
  | [], current => rfl
  | (p, s) :: rest, current => by
      simp only [slotValue, slotValue_const_mul c f rest]
      ring

theorem slotValue_const (c : ℝ≥0∞) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)), (∀ x ∈ coins, x.1 ≤ 1) → ∀ current,
      slotValue (fun _ => c) current coins = c
  | [], _, current => rfl
  | (p, s) :: rest, h, current => by
      simp only [slotValue, slotValue_const c rest (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      rw [← add_mul, add_tsub_cancel_of_le (h _ (List.mem_cons_self ..)), one_mul]

theorem virtual_add (hU : U.Nonempty) (f g : Multiset V → ℝ≥0∞) :
    ∀ m items d, virtual U wbar (fun x => f x + g x) m items d =
      virtual U wbar f m items d + virtual U wbar g m items d
  | 0, _, _ => rfl
  | m + 1, items, d => by
      simp only [virtual]
      rw [← freshAvg_add]
      congr 1
      funext u
      rw [← slotValue_add]
      exact slotValue_congr (fun e => virtual_add hU f g m (u :: items) e) _ _

theorem virtual_const_mul (c : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) :
    ∀ m items d, virtual U wbar (fun x => c * f x) m items d = c * virtual U wbar f m items d
  | 0, _, _ => rfl
  | m + 1, items, d => by
      simp only [virtual]
      rw [← freshAvg_mul]
      congr 1
      funext u
      rw [← slotValue_const_mul]
      exact slotValue_congr (fun e => virtual_const_mul c f m (u :: items) e) _ _

theorem virtual_const (hU : U.Nonempty) (hw : wbar ≤ 1) (c : ℝ≥0∞) :
    ∀ m items d, virtual U wbar (fun _ => c) m items d = c
  | 0, _, _ => rfl
  | m + 1, items, d => by
      simp only [virtual]
      have h : ∀ u, slotValue (virtual U wbar (fun _ => c) m (u :: items)) (d + {u}) (itemCoins wbar items) = c := by
        intro u
        rw [slotValue_congr (fun e => virtual_const hU hw c m (u :: items) e)]
        exact slotValue_const c _ (itemCoins_le hw items) _
      simp only [h]
      exact freshAvg_const U hU c

theorem virtual_mono_base {f g : Multiset V → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) :
    ∀ m items d, virtual U wbar f m items d ≤ virtual U wbar g m items d
  | 0, _, d => hfg d
  | m + 1, items, d => by
      simp only [virtual]
      refine freshAvg_mono U fun u _ => ?_
      exact slotValue_le_of_le (fun e => virtual_mono_base hfg m (u :: items) e) _ _

end Linear

/-! ### Future pairs created by the remaining budget -/

section Creation

variable (U : Finset V) (land : ℝ≥0∞)

/-- Expected value after `k` future pairs, each an item with a uniform view with probability
`land`. -/
noncomputable def creations (G : List V → ℝ≥0∞) : ℕ → List V → ℝ≥0∞
  | 0, items => G items
  | k + 1, items => (1 - land) * creations G k items + land * freshAvg U (fun v => creations G k (v :: items))

variable {U land}

theorem creations_mono {G H : List V → ℝ≥0∞} (hGH : ∀ items, G items ≤ H items) :
    ∀ k items, creations U land G k items ≤ creations U land H k items
  | 0, items => hGH items
  | k + 1, items => by
      simp only [creations]
      gcongr
      · exact creations_mono hGH k items
      · exact freshAvg_mono U fun v _ => creations_mono hGH k (v :: items)

theorem creations_add (G H : List V → ℝ≥0∞) :
    ∀ k items, creations U land (fun I => G I + H I) k items =
      creations U land G k items + creations U land H k items
  | 0, items => rfl
  | k + 1, items => by
      simp only [creations]
      rw [creations_add G H k items]
      have : (fun v => creations U land (fun I => G I + H I) k (v :: items)) =
          fun v => creations U land G k (v :: items) + creations U land H k (v :: items) := by
        funext v; exact creations_add G H k (v :: items)
      rw [this, freshAvg_add]
      ring

theorem creations_const_mul (c : ℝ≥0∞) (G : List V → ℝ≥0∞) :
    ∀ k items, creations U land (fun I => c * G I) k items = c * creations U land G k items
  | 0, items => rfl
  | k + 1, items => by
      simp only [creations]
      rw [creations_const_mul c G k items]
      have : (fun v => creations U land (fun I => c * G I) k (v :: items)) =
          fun v => c * creations U land G k (v :: items) := by
        funext v; exact creations_const_mul c G k (v :: items)
      rw [this, freshAvg_mul]
      ring

theorem creations_const (hU : U.Nonempty) (hland : land ≤ 1) (c : ℝ≥0∞) :
    ∀ k items, creations U land (fun _ => c) k items = c
  | 0, _ => rfl
  | k + 1, items => by
      simp only [creations]
      have : (fun v => creations U land (fun _ => c) k (v :: items)) = fun _ => c := by
        funext v; exact creations_const hU hland c k (v :: items)
      rw [this, freshAvg_const U hU, creations_const hU hland c k items, ← add_mul,
        tsub_add_cancel_of_le hland, one_mul]

/-- If the base value grows with items, so does the number of future pairs. -/
theorem creations_le_succ (hU : U.Nonempty) (hland : land ≤ 1) {G : List V → ℝ≥0∞}
    (hG : ∀ v items, G items ≤ G (v :: items)) (hperm : ∀ items items', items.Perm items' → G items = G items') :
    ∀ k items, creations U land G k items ≤ creations U land G (k + 1) items := by
  -- adding one future pair in front is the same as adding it at the end
  have hmono : ∀ k items v, creations U land G k items ≤ creations U land G k (v :: items) := by
    intro k
    induction k with
    | zero => intro items v; exact hG v items
    | succ k ih =>
        intro items v
        simp only [creations]
        gcongr
        · exact ih items v
        · refine freshAvg_mono U fun w _ => ?_
          calc creations U land G k (w :: items) ≤ creations U land G k (v :: w :: items) := ih _ v
            _ = creations U land G k (w :: v :: items) := by
                have hp : ∀ k' (a b : List V), a.Perm b → creations U land G k' a = creations U land G k' b := by
                  intro k'
                  induction k' with
                  | zero => intro a b hab; exact hperm a b hab
                  | succ k' ih' =>
                      intro a b hab
                      simp only [creations]
                      rw [ih' a b hab, show (fun x => creations U land G k' (x :: a)) =
                        (fun x => creations U land G k' (x :: b)) from funext fun x => ih' _ _ (hab.cons x)]
                exact hp k _ _ (List.Perm.swap w v items)
  intro k items
  simp only [creations]
  calc creations U land G k items = (1 - land) * creations U land G k items + land * creations U land G k items := by
        rw [← add_mul, tsub_add_cancel_of_le hland, one_mul]
    _ ≤ _ := by
        gcongr
        calc creations U land G k items = freshAvg U (fun _ => creations U land G k items) :=
              (freshAvg_const U hU _).symm
          _ ≤ _ := freshAvg_mono U fun v _ => hmono k items v

/-- Expectations over an outcome commute with future pairs. -/
theorem creations_tsum {β : Type} (weights : β → ℝ≥0∞) (G : β → List V → ℝ≥0∞) :
    ∀ k items, ∑' x, weights x * creations U land (G x) k items =
      creations U land (fun I => ∑' x, weights x * G x I) k items
  | 0, items => rfl
  | k + 1, items => by
      simp only [creations]
      rw [← creations_tsum weights G k items]
      have : (fun v => creations U land (fun I => ∑' x, weights x * G x I) k (v :: items)) =
          fun v => ∑' x, weights x * creations U land (G x) k (v :: items) := by
        funext v; exact (creations_tsum weights G k (v :: items)).symm
      rw [this]
      simp only [mul_add, ENNReal.tsum_add, freshAvg, Finset.mul_sum]
      congr 1
      · rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring
      · rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => by ring

end Creation

/-! ### More on future pairs and slots -/

section More

variable {U : Finset V} {land wbar : ℝ≥0∞} {f : Multiset V → ℝ≥0∞}

theorem creations_mono_count (hU : U.Nonempty) (hland : land ≤ 1) {G : List V → ℝ≥0∞}
    (hG : ∀ v items, G items ≤ G (v :: items)) (hperm : ∀ items items', items.Perm items' → G items = G items')
    {k k' : ℕ} (hk : k ≤ k') (items : List V) : creations U land G k items ≤ creations U land G k' items := by
  induction hk with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (creations_le_succ hU hland hG hperm _ items)

theorem creations_zero_fun : ∀ k (items : List V), creations U land (fun _ => 0) k items = 0
  | 0, _ => rfl
  | k + 1, items => by
      simp only [creations, creations_zero_fun k]
      simp [freshAvg]

theorem creations_finset_sum {κ : Type} [DecidableEq κ] (S : Finset κ) (G : κ → List V → ℝ≥0∞) (k : ℕ) (items : List V) :
    creations U land (fun I => ∑ i ∈ S, G i I) k items = ∑ i ∈ S, creations U land (G i) k items := by
  induction S using Finset.induction_on with
  | empty => simpa using creations_zero_fun k items
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [creations_add (G a) (fun I => ∑ i ∈ S, G i I), ih]

theorem virtual_zero_fun : ∀ m (items : List V) d, virtual U wbar (fun _ => 0) m items d = 0 := by
  intro m items d
  have h := virtual_const_mul (U := U) (wbar := wbar) 0 (fun _ => (1 : ℝ≥0∞)) m items d
  simpa using h

theorem virtual_finset_sum (hU : U.Nonempty) {κ : Type} [DecidableEq κ] (S : Finset κ) (g : κ → Multiset V → ℝ≥0∞) (m : ℕ)
    (items : List V) (d : Multiset V) :
    virtual U wbar (fun D => ∑ i ∈ S, g i D) m items d = ∑ i ∈ S, virtual U wbar (g i) m items d := by
  induction S using Finset.induction_on generalizing m items d with
  | empty => simpa using virtual_zero_fun m items d
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [virtual_add hU (g a) (fun D => ∑ i ∈ S, g i D), ih]

/-- The virtual future of an average is the average of the virtual futures. -/
theorem virtual_freshAvg (hU : U.Nonempty) {W : Type} [DecidableEq W] (T : Finset W) (g : W → Multiset V → ℝ≥0∞) (m : ℕ)
    (items : List V) (d : Multiset V) :
    virtual U wbar (fun D => freshAvg T fun i => g i D) m items d =
      freshAvg T fun i => virtual U wbar (g i) m items d := by
  unfold freshAvg
  rw [virtual_const_mul, virtual_finset_sum hU]

theorem creations_freshAvg {W : Type} [DecidableEq W] (T : Finset W) (G : W → List V → ℝ≥0∞) (k : ℕ) (items : List V) :
    creations U land (fun I => freshAvg T fun i => G i I) k items =
      freshAvg T fun i => creations U land (G i) k items := by
  unfold freshAvg
  rw [creations_const_mul, creations_finset_sum]

end More

end FORS.Base.Domination

end

section

/-! The count of views per index (`cnt`) and the statement that a fresh view has a uniform index
(`UniformIndex`). Generic in the view type `V` and the index map `idx`. -/

open ENNReal

namespace FORS.Base.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- Number of disclosed views at index `l`. -/
def cnt (d : Multiset V) (l : ι) : ℕ := (d.filter fun v => idx v = l).card

theorem cnt_add_single (d : Multiset V) (u : V) (l : ι) :
    cnt idx (d + {u}) l = cnt idx d l + if idx u = l then 1 else 0 := by
  unfold cnt
  rw [Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton]
  split_ifs <;> simp

theorem cnt_zero (l : ι) : cnt idx (0 : Multiset V) l = 0 := by simp [cnt]

theorem prod_split {f : ι → ℝ≥0∞} (j : ι) : ∏ l, f l = f j * ∏ l ∈ Finset.univ.erase j, f l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

/-- The fresh view has a uniform index. -/
def UniformIndex (U : Finset V) : Prop :=
  ∀ g : ι → ℝ≥0∞, freshAvg U (fun u => g (idx u)) = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ l, g l

end FORS.Base.H0

end
