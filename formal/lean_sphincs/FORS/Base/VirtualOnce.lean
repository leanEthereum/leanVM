import FORS.Base.Virtual

/-! A virtual future for signers that never sign a message twice. A slot is one future signature:
a fresh uniform view, disclosed. An item (a cached landed pair of a message not yet signed) has one
independent coin of probability `w` over the whole future, since only the single signing call of
its message can select it. -/

open ENNReal OracleComp

namespace FORS.Base.Domination

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

end Fresh

/-! ### One coin per item -/

section Once

variable (U : Finset V) (w : ℝ≥0∞) (f : Multiset V → ℝ≥0∞)

/-- One coin of probability `w` for every item, then `m` fresh slots. -/
noncomputable def virtualOnce (m : ℕ) (coins : List V) (d : Multiset V) : ℝ≥0∞ :=
  slotValue (fresh U f m) d (itemCoins w coins)

variable {U w f}

theorem virtualOnce_perm (m : ℕ) {coins coins' : List V} (hperm : coins.Perm coins') (d : Multiset V) :
    virtualOnce U w f m coins d = virtualOnce U w f m coins' d :=
  slotValue_perm _ (hperm.map _) _

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

end Once

end FORS.Base.Domination
