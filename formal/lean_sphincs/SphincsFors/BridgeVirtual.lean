import SphincsFors.BridgeDomination

open OracleComp

/-! The virtual future used by the FORS forecast potentials. A slot is one future signature:
a fresh uniform view, disclosed and kept as an item, and an independent coin of probability `wbar`
for every existing item, disclosing that item's view again. All potentials are expectations of a
monotone supermodular base function of the final multiset of disclosures. -/

open ENNReal

namespace SphincsFors.Security.Domination

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

theorem slotValue_super (f : Multiset V → ℝ≥0∞) (hsuper : Supermodular f) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)), Supermodular fun current => slotValue f current coins
  | [], small, large, extra, hle => hsuper small large extra hle
  | (p, add) :: rest, small, large, extra, hle => by
      simp only [slotValue]
      have h1 := slotValue_super f hsuper rest (small + add) (large + add) extra (add_le_add hle le_rfl)
      have h2 := slotValue_super f hsuper rest small large extra hle
      have e1 : small + extra + add = small + add + extra := by abel
      have e2 : large + extra + add = large + add + extra := by abel
      rw [e1, e2]
      calc p * slotValue f (small + add + extra) rest + (1 - p) * slotValue f (small + extra) rest +
            (p * slotValue f (large + add) rest + (1 - p) * slotValue f large rest)
          = p * (slotValue f (small + add + extra) rest + slotValue f (large + add) rest) +
            (1 - p) * (slotValue f (small + extra) rest + slotValue f large rest) := by ring
        _ ≤ p * (slotValue f (large + add + extra) rest + slotValue f (small + add) rest) +
            (1 - p) * (slotValue f (large + extra) rest + slotValue f small rest) := by gcongr
        _ = _ := by ring

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

theorem mono_translate {h : Multiset V → ℝ≥0∞} (hh : Monotone' h) (shift : Multiset V) :
    Monotone' fun d => h (d + shift) := fun _ _ hle => hh _ _ (add_le_add hle le_rfl)

theorem super_translate {h : Multiset V → ℝ≥0∞} (hh : Supermodular h) (shift : Multiset V) :
    Supermodular fun d => h (d + shift) := by
  intro small large extra hle
  have := hh (small + shift) (large + shift) extra (add_le_add hle le_rfl)
  simpa only [add_right_comm _ extra shift] using this

theorem mono_freshAvg (U : Finset V) {h : V → Multiset V → ℝ≥0∞} (hh : ∀ u, Monotone' (h u)) :
    Monotone' fun d => freshAvg U fun u => h u d :=
  fun _ _ hle => freshAvg_mono U fun u _ => hh u _ _ hle

theorem super_freshAvg (U : Finset V) {h : V → Multiset V → ℝ≥0∞} (hh : ∀ u, Supermodular (h u)) :
    Supermodular fun d => freshAvg U fun u => h u d := by
  intro small large extra hle
  simp only [← freshAvg_add]
  exact freshAvg_mono U fun u _ => hh u small large extra hle

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

/-- Monotone, supermodular and finite in the disclosures. -/
theorem virtual_props (hU : U.Nonempty) (hw : wbar ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) :
    ∀ m items, Monotone' (virtual U wbar f m items) ∧ Supermodular (virtual U wbar f m items) ∧
      ∀ d, virtual U wbar f m items d ≠ ⊤
  | 0, _ => ⟨hmono, hsuper, hfin⟩
  | m + 1, items => by
      have ih := fun u => virtual_props hU hw hmono hsuper hfin m (u :: items)
      refine ⟨?_, ?_, ?_⟩
      · exact mono_freshAvg U fun u => mono_translate (slotValue_mono _ (ih u).1 _) {u}
      · exact super_freshAvg U fun u => super_translate (slotValue_super _ (ih u).2.1 _) {u}
      · intro d
        exact freshAvg_ne_top hU fun u => slotValue_ne_top _ (ih u).2.2 _ _ (itemCoins_le hw items)

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

theorem virtual_perm : ∀ (m : ℕ) {items items' : List V}, items.Perm items' →
    ∀ d, virtual U wbar f m items d = virtual U wbar f m items' d
  | 0, _, _, _, d => rfl
  | m + 1, items, items', hperm, d => by
      simp only [virtual]
      congr 1
      funext u
      rw [slotValue_congr (fun e => virtual_perm m (hperm.cons u) e)]
      exact slotValue_perm _ (hperm.map _) _

theorem itemCoins_cons (w : V) (items : List V) :
    itemCoins wbar (w :: items) = (wbar, ({w} : Multiset V)) :: itemCoins wbar items := rfl

/-- More items, more virtual disclosures. -/
theorem virtual_le_cons (hU : U.Nonempty) (hw : wbar ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) :
    ∀ (m : ℕ) (items : List V) (w : V) d, virtual U wbar f m items d ≤ virtual U wbar f m (w :: items) d
  | 0, _, _, d => le_rfl
  | m + 1, items, w, d => by
      simp only [virtual]
      refine freshAvg_mono U fun u _ => ?_
      have hstep1 : ∀ e, virtual U wbar f m (u :: items) e ≤ virtual U wbar f m (u :: w :: items) e := by
        intro e
        rw [virtual_perm m (List.Perm.swap w u items) e]
        exact virtual_le_cons hU hw hmono hsuper hfin m (u :: items) w e
      have hG := virtual_props hU hw hmono hsuper hfin m (u :: w :: items)
      refine le_trans (slotValue_le_of_le hstep1 _ _) ?_
      rw [itemCoins_cons]
      simp only [slotValue]
      set a := slotValue (virtual U wbar f m (u :: w :: items)) (d + {u} + {w}) (itemCoins wbar items)
      set b := slotValue (virtual U wbar f m (u :: w :: items)) (d + {u}) (itemCoins wbar items)
      have hab : b ≤ a := slotValue_mono _ hG.1 _ _ _ (Multiset.le_add_right _ _)
      calc b = wbar * b + (1 - wbar) * b := by rw [← add_mul, add_tsub_cancel_of_le hw, one_mul]
        _ ≤ wbar * a + (1 - wbar) * b := by gcongr

end Items

/-! ### What a signing call discloses -/

/-- What a signing call discloses: nothing, a fresh view (which becomes an item), or the view of
an existing item. -/
inductive Pick (V : Type) where
  | none
  | fresh (view : V)
  | pool (view : V)

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

/-- The virtual future only adds disclosures. -/
theorem base_le_virtual (hU : U.Nonempty) (hw : wbar ≤ 1) {f : Multiset V → ℝ≥0∞} (hmono : Monotone' f)
    (hsuper : Supermodular f) (hfin : ∀ m, f m ≠ ⊤) :
    ∀ m items d, f d ≤ virtual U wbar f m items d
  | 0, _, d => le_rfl
  | m + 1, items, d => by
      simp only [virtual]
      have hprops := fun u => virtual_props hU hw hmono hsuper hfin m (u :: items)
      calc f d = freshAvg U (fun _ => f d) := (freshAvg_const U hU _).symm
        _ ≤ _ := freshAvg_mono U fun u _ => by
            calc f d ≤ virtual U wbar f m (u :: items) (d + {u}) :=
                  le_trans (hmono _ _ (Multiset.le_add_right _ _)) (base_le_virtual hU hw hmono hsuper hfin m _ _)
              _ = slotValue (virtual U wbar f m (u :: items)) (d + {u}) [] := rfl
              _ ≤ _ := by
                  have hcoins := coins_gain (virtual U wbar f m (u :: items)) (hprops u).1 (hprops u).2.1
                    (hprops u).2.2 (items.map fun w => (wbar, w))
                    (by intro i hi; obtain ⟨w, _, rfl⟩ := List.mem_map.1 hi; exact hw) (d + {u}) (d + {u}) le_rfl
                  have hc' : coinsOf (items.map fun w => (wbar, w)) = itemCoins wbar items := by
                    simp [coinsOf, itemCoins, Function.comp_def]
                  rw [hc'] at hcoins
                  exact le_trans le_self_add hcoins

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

theorem creations_perm {G : List V → ℝ≥0∞} (hperm : ∀ a b, a.Perm b → G a = G b) :
    ∀ k (a b : List V), a.Perm b → creations U land G k a = creations U land G k b := by
  intro k
  induction k with
  | zero => intro a b hab; exact hperm a b hab
  | succ k ih =>
      intro a b hab
      simp only [creations]
      rw [ih a b hab, show (fun x => creations U land G k (x :: a)) =
        (fun x => creations U land G k (x :: b)) from funext fun x => ih _ _ (hab.cons x)]

/-- Existing items can be moved into the base function. -/
theorem creations_prepend {G : List V → ℝ≥0∞} (hperm : ∀ a b, a.Perm b → G a = G b) (extra : List V) :
    ∀ k items, creations U land G k (extra ++ items) = creations U land (fun J => G (extra ++ J)) k items := by
  intro k
  induction k with
  | zero => intro items; rfl
  | succ k ih =>
      intro items
      simp only [creations]
      rw [ih items, show (fun v => creations U land G k (v :: (extra ++ items))) =
        (fun v => creations U land (fun J => G (extra ++ J)) k (v :: items)) from funext fun v => by
          rw [creations_perm hperm k (v :: (extra ++ items)) (extra ++ v :: items) List.perm_middle.symm]
          exact ih (v :: items)]

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

/-- Comparing base functions only on lists that extend the starting items. -/
theorem creations_mono_suffix {G H : List V → ℝ≥0∞} :
    ∀ k (I : List V), (∀ news, G (news ++ I) ≤ H (news ++ I)) → creations U land G k I ≤ creations U land H k I
  | 0, I, h => by simpa [creations] using h []
  | k + 1, I, h => by
      simp only [creations]
      gcongr
      · exact creations_mono_suffix k I h
      · exact freshAvg_mono U fun v _ => creations_mono_suffix k (v :: I) fun news => by
          simpa using h (news ++ [v])

end More

end SphincsFors.Security.Domination
