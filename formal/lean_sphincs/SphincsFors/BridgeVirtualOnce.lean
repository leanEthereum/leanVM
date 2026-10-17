import SphincsFors.BridgeVirtual

/-! A virtual future for signers that never sign a message twice. A slot is one future signature:
a fresh uniform view, disclosed. An item (a cached landed pair of a message not yet signed) has one
independent coin of probability `w` over the whole future, since only the single signing call of
its message can select it. -/

open ENNReal OracleComp

namespace SphincsFors.Security.Domination

variable {V : Type}

/-! ### Coins over lists and averages -/

theorem slotValue_append (f : Multiset V → ℝ≥0∞) :
    ∀ (first second : List (ℝ≥0∞ × Multiset V)) current,
      slotValue f current (first ++ second) = slotValue (fun e => slotValue f e second) current first
  | [], _, _ => rfl
  | (p, S) :: rest, second, current => by
      simp only [List.cons_append, slotValue, slotValue_append f rest second]

theorem slotValue_freshAvg {W : Type} (U : Finset W) (h : W → Multiset V → ℝ≥0∞) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) current,
      slotValue (fun e => freshAvg U fun u => h u e) current coins =
        freshAvg U fun u => slotValue (h u) current coins
  | [], _ => rfl
  | (p, S) :: rest, current => by
      simp only [slotValue, slotValue_freshAvg U h rest]
      rw [← freshAvg_mul, ← freshAvg_mul, ← freshAvg_add]

theorem slotValue_zero_coins (f : Multiset V → ℝ≥0∞) :
    ∀ (items : List V) current, slotValue f current (itemCoins 0 items) = f current
  | [], _ => rfl
  | w :: rest, current => by
      rw [itemCoins_cons]
      simp only [slotValue, slotValue_zero_coins f rest, zero_mul, zero_add, tsub_zero, one_mul]

/-! ### Fresh slots -/

section Fresh

variable (U : Finset V) (f : Multiset V → ℝ≥0∞)

/-- Expected base value after `m` fresh disclosed slots. -/
noncomputable def fresh : ℕ → Multiset V → ℝ≥0∞
  | 0, d => f d
  | m + 1, d => freshAvg U fun u => fresh m (d + {u})

variable {U f}

/-- Fresh slots are the virtual future without coins. -/
theorem fresh_eq_virtual : ∀ (m : ℕ) (items : List V) d, fresh U f m d = virtual U 0 f m items d
  | 0, _, _ => rfl
  | m + 1, items, d => by
      simp only [fresh, virtual, slotValue_zero_coins]
      congr 1
      funext u
      exact fresh_eq_virtual m (u :: items) (d + {u})

theorem fresh_props (hU : U.Nonempty) (hmono : Monotone' f) (hsuper : Supermodular f) (hfin : ∀ m, f m ≠ ⊤)
    (m : ℕ) : Monotone' (fresh U f m) ∧ Supermodular (fresh U f m) ∧ ∀ d, fresh U f m d ≠ ⊤ := by
  have h := virtual_props hU (zero_le_one) hmono hsuper hfin m []
  have he : fresh U f m = virtual U 0 f m [] := funext fun d => fresh_eq_virtual m [] d
  rw [he]
  exact h

end Fresh

/-! ### One coin per item -/

section Once

variable (U : Finset V) (w : ℝ≥0∞) (f : Multiset V → ℝ≥0∞)

/-- One coin of probability `w` for every item, then `m` fresh slots. -/
noncomputable def virtualOnce (m : ℕ) (coins : List V) (d : Multiset V) : ℝ≥0∞ :=
  slotValue (fresh U f m) d (itemCoins w coins)

variable {U w f}

theorem virtualOnce_props (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (m : ℕ) (coins : List V) :
    Monotone' (virtualOnce U w f m coins) ∧ Supermodular (virtualOnce U w f m coins) ∧
      ∀ d, virtualOnce U w f m coins d ≠ ⊤ := by
  have hF := fresh_props hU hmono hsuper hfin m
  exact ⟨slotValue_mono _ hF.1 _, slotValue_super _ hF.2.1 _,
    fun d => slotValue_ne_top _ hF.2.2 _ _ (itemCoins_le hw coins)⟩

theorem virtualOnce_perm (m : ℕ) {coins coins' : List V} (hperm : coins.Perm coins') (d : Multiset V) :
    virtualOnce U w f m coins d = virtualOnce U w f m coins' d :=
  slotValue_perm _ (hperm.map _) _

/-- More coins, more virtual disclosures. -/
theorem virtualOnce_le_cons (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (m : ℕ) (coins : List V) (v : V) (d : Multiset V) :
    virtualOnce U w f m coins d ≤ virtualOnce U w f m (v :: coins) d := by
  have hG := virtualOnce_props hU hw hmono hsuper hfin m coins
  unfold virtualOnce
  rw [itemCoins_cons]
  simp only [slotValue]
  change virtualOnce U w f m coins d ≤ w * virtualOnce U w f m coins (d + {v}) + (1 - w) * virtualOnce U w f m coins d
  have hab : virtualOnce U w f m coins d ≤ virtualOnce U w f m coins (d + {v}) :=
    hG.1 _ _ (Multiset.le_add_right _ _)
  calc virtualOnce U w f m coins d = w * virtualOnce U w f m coins d + (1 - w) * virtualOnce U w f m coins d := by
        rw [← add_mul, add_tsub_cancel_of_le hw, one_mul]
    _ ≤ _ := by gcongr

theorem virtualOnce_add (hU : U.Nonempty) (f g : Multiset V → ℝ≥0∞) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w (fun x => f x + g x) m coins d = virtualOnce U w f m coins d + virtualOnce U w g m coins d := by
  unfold virtualOnce
  rw [← slotValue_add]
  refine slotValue_congr (fun e => ?_) _ _
  rw [fresh_eq_virtual m [] e, fresh_eq_virtual m [] e, fresh_eq_virtual m [] e]
  exact virtual_add hU f g m [] e

theorem virtualOnce_const_mul (c : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w (fun x => c * f x) m coins d = c * virtualOnce U w f m coins d := by
  unfold virtualOnce
  rw [← slotValue_const_mul]
  refine slotValue_congr (fun e => ?_) _ _
  rw [fresh_eq_virtual m [] e, fresh_eq_virtual m [] e]
  exact virtual_const_mul c f m [] e

theorem virtualOnce_const (hU : U.Nonempty) (hw : w ≤ 1) (c : ℝ≥0∞) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w (fun _ => c) m coins d = c := by
  unfold virtualOnce
  rw [slotValue_congr (fun e => (fresh_eq_virtual m [] e).trans (virtual_const hU zero_le_one c m [] e))]
  exact slotValue_const c _ (itemCoins_le hw coins) _

theorem virtualOnce_mono_base {f g : Multiset V → ℝ≥0∞} (hfg : ∀ x, f x ≤ g x) (m : ℕ) (coins : List V)
    (d : Multiset V) : virtualOnce U w f m coins d ≤ virtualOnce U w g m coins d := by
  unfold virtualOnce
  refine slotValue_le_of_le (fun e => ?_) _ _
  rw [fresh_eq_virtual m [] e, fresh_eq_virtual m [] e]
  exact virtual_mono_base hfg m [] e

/-- The virtual future only adds disclosures. -/
theorem base_le_virtualOnce (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (m : ℕ) (coins : List V) (d : Multiset V) : f d ≤ virtualOnce U w f m coins d := by
  have hF := fresh_props hU hmono hsuper hfin m
  have h1 : f d ≤ fresh U f m d := by
    rw [fresh_eq_virtual m [] d]
    exact base_le_virtual hU zero_le_one hmono hsuper hfin m [] d
  refine le_trans h1 ?_
  have hcoins := coins_gain (fresh U f m) hF.1 hF.2.1 hF.2.2 (coins.map fun v => (w, v))
    (by intro i hi; obtain ⟨v, _, rfl⟩ := List.mem_map.1 hi; exact hw) d d le_rfl
  have hc' : coinsOf (coins.map fun v => (w, v)) = itemCoins w coins := by
    simp [coinsOf, itemCoins, Function.comp_def]
  rw [hc'] at hcoins
  exact le_trans le_self_add hcoins

/-- One fresh slot after the coins of `rest`: the virtual future of one more slot, seen through the
coins of the other items. -/
theorem virtualOnce_succ (m : ℕ) (first rest : List V) (d : Multiset V) :
    virtualOnce U w f (m + 1) (first ++ rest) d =
      slotValue (fun e => freshAvg U fun u => virtualOnce U w f m rest (e + {u})) d (itemCoins w first) := by
  unfold virtualOnce itemCoins
  rw [List.map_append, slotValue_append]
  refine slotValue_congr (fun e => ?_) _ _
  change slotValue (fun e' => freshAvg U fun u => fresh U f m (e' + {u})) e _ = _
  rw [slotValue_freshAvg]
  congr 1
  funext u
  exact slotValue_translate (fresh U f m) {u} _ e

theorem virtualOnce_freshAvg (hU : U.Nonempty) {W : Type} [DecidableEq W] (T : Finset W)
    (g : W → Multiset V → ℝ≥0∞) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w (fun D => freshAvg T fun i => g i D) m coins d =
      freshAvg T fun i => virtualOnce U w (g i) m coins d := by
  unfold virtualOnce
  rw [slotValue_congr (fun e => (fresh_eq_virtual m [] e).trans (virtual_freshAvg hU T g m [] e))]
  rw [slotValue_freshAvg]
  congr 1
  funext i
  exact slotValue_congr (fun e => (fresh_eq_virtual m [] e).symm) _ _

/-- **The once-coined slot dominates a base value plus its fresh and pool gains.** -/
theorem once_slot_ge (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (m : ℕ) (first rest : List V) (d : Multiset V) :
    virtualOnce U w f m rest d + freshAvg U (gain (virtualOnce U w f m rest) d) +
        (first.map fun v => w * gain (virtualOnce U w f m rest) d v).sum ≤
      virtualOnce U w f (m + 1) (first ++ rest) d := by
  set G := virtualOnce U w f m rest with hGdef
  have hG := virtualOnce_props hU hw hmono hsuper hfin m rest
  set H : Multiset V → ℝ≥0∞ := fun e => freshAvg U fun u => G (e + {u}) with hHdef
  have hHmono : Monotone' H := mono_freshAvg U fun u => mono_translate hG.1 {u}
  have hHsuper : Supermodular H := super_freshAvg U fun u => super_translate hG.2.1 {u}
  have hHfin : ∀ e, H e ≠ ⊤ := fun e => freshAvg_ne_top hU fun u => hG.2.2 _
  rw [virtualOnce_succ]
  change G d + freshAvg U (gain G d) + (first.map fun v => w * gain G d v).sum ≤ slotValue H d (itemCoins w first)
  have hcoins := coins_gain H hHmono hHsuper hHfin (first.map fun v => (w, v))
    (by intro i hi; obtain ⟨v, _, rfl⟩ := List.mem_map.1 hi; exact hw) d d le_rfl
  have hc' : coinsOf (first.map fun v => (w, v)) = itemCoins w first := by
    simp [coinsOf, itemCoins, Function.comp_def]
  rw [hc', List.map_map] at hcoins
  refine le_trans ?_ hcoins
  have hHd : H d = G d + freshAvg U (gain G d) := by
    simp only [hHdef]
    rw [← freshAvg_const U hU (G d), ← freshAvg_add]
    congr 1
    funext u
    exact add_gain G hG.1 d u
  rw [hHd]
  refine add_le_add le_rfl (List.sum_le_sum fun v _ => ?_)
  simp only [Function.comp_apply]
  refine mul_le_mul_right ?_ w
  show gain G d v ≤ gain H d v
  unfold gain
  refine ENNReal.le_sub_of_add_le_left (hHfin d) ?_
  calc H d + (G (d + {v}) - G d) = freshAvg U (fun u => G (d + {u}) + (G (d + {v}) - G d)) := by
        simp only [hHdef]
        rw [freshAvg_add, freshAvg_const U hU]
    _ ≤ freshAvg U fun u => G (d + {v} + {u}) := freshAvg_mono U fun u _ => by
        have h := gain_le_of_le G hG.1 hG.2.1 hG.2.2 d (d + {u}) (Multiset.le_add_right _ _) v
        unfold gain at h
        rw [add_right_comm]
        exact h
    _ = H (d + {v}) := rfl

end Once

end SphincsFors.Security.Domination
