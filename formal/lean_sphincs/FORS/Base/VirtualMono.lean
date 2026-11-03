import FORS.Base.VirtualOnce

/-! The one-coin virtual future for monotone base functions. The FORS witness (a cover
indicator) is monotone but not supermodular, so the lemmas that add coins by their gains do
not apply. Instead a list of `ℓ` coins of probability `w` dominates any disclosure of a single item
of the list with probability `e` per item, `e (1 + w ℓ) ≤ w`, together with the base value: a coin
coupling that gives each item the leftover mass of the coins before it. For the grinding signer
`w = 1/R` and `e = 1/(ℓ + R)` with `R = (2^128 - Cmax) landing`. -/

open ENNReal

namespace FORS.Security.Domination

open FORS.Base.Domination

variable {V : Type}

/-! ### Fresh slots and coins for monotone base functions -/

section Mono

variable (U : Finset V) {f : Multiset V → ℝ≥0∞}

theorem fresh_mono (hmono : Monotone' f) : ∀ m, Monotone' (fresh U f m)
  | 0 => hmono
  | m + 1 => fun _ _ hle => freshAvg_mono U fun _ _ =>
      fresh_mono hmono m _ _ (add_le_add hle le_rfl)

theorem fresh_ne_top (hU : U.Nonempty) (hfin : ∀ d, f d ≠ ⊤) : ∀ m d, fresh U f m d ≠ ⊤
  | 0, d => hfin d
  | m + 1, _ => freshAvg_ne_top hU fun _ => fresh_ne_top hU hfin m _

theorem base_le_fresh (hU : U.Nonempty) (hmono : Monotone' f) : ∀ m d, f d ≤ fresh U f m d
  | 0, _ => le_rfl
  | m + 1, d => by
      calc f d = freshAvg U (fun _ => f d) := (freshAvg_const U hU _).symm
        _ ≤ _ := freshAvg_mono U fun u _ =>
            le_trans (hmono _ _ (Multiset.le_add_right _ _)) (base_le_fresh hU hmono m _)

variable {U}

theorem base_le_slotValue {Φ : Multiset V → ℝ≥0∞} (hmono : Monotone' Φ) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)), (∀ c ∈ coins, c.1 ≤ 1) → ∀ d, Φ d ≤ slotValue Φ d coins
  | [], _, _ => le_rfl
  | (p, extra) :: rest, hp, d => by
      have hp1 : p ≤ 1 := hp _ (List.mem_cons_self ..)
      have hrest : ∀ c ∈ rest, c.1 ≤ 1 := fun c hc => hp c (List.mem_cons_of_mem _ hc)
      simp only [slotValue]
      calc Φ d = p * Φ d + (1 - p) * Φ d := by rw [← add_mul, add_tsub_cancel_of_le hp1, one_mul]
        _ ≤ _ := by
            gcongr
            · exact le_trans (hmono _ _ (Multiset.le_add_right _ _)) (base_le_slotValue hmono rest hrest _)
            · exact base_le_slotValue hmono rest hrest d

variable {w : ℝ≥0∞}

theorem virtualOnce_mono (hmono : Monotone' f) (m : ℕ) (coins : List V) :
    Monotone' (virtualOnce U w f m coins) :=
  slotValue_mono _ (fresh_mono U hmono m) _

theorem virtualOnce_ne_top (hU : U.Nonempty) (hw : w ≤ 1) (hfin : ∀ d, f d ≠ ⊤) (m : ℕ) (coins : List V)
    (d : Multiset V) : virtualOnce U w f m coins d ≠ ⊤ :=
  slotValue_ne_top _ (fresh_ne_top U hU hfin m) _ _ (itemCoins_le hw coins)

/-- More coins, more virtual disclosures. -/
theorem virtualOnce_le_consM (hw : w ≤ 1) (hmono : Monotone' f) (m : ℕ) (coins : List V) (v : V)
    (d : Multiset V) : virtualOnce U w f m coins d ≤ virtualOnce U w f m (v :: coins) d := by
  unfold virtualOnce
  rw [itemCoins_cons]
  simp only [slotValue]
  change virtualOnce U w f m coins d ≤ w * virtualOnce U w f m coins (d + {v}) + (1 - w) * virtualOnce U w f m coins d
  have hab : virtualOnce U w f m coins d ≤ virtualOnce U w f m coins (d + {v}) :=
    virtualOnce_mono hmono m coins _ _ (Multiset.le_add_right _ _)
  calc virtualOnce U w f m coins d = w * virtualOnce U w f m coins d + (1 - w) * virtualOnce U w f m coins d := by
        rw [← add_mul, add_tsub_cancel_of_le hw, one_mul]
    _ ≤ _ := by gcongr

/-- The virtual future only adds disclosures. -/
theorem base_le_virtualOnceM (hU : U.Nonempty) (hw : w ≤ 1) (hmono : Monotone' f) (m : ℕ) (coins : List V)
    (d : Multiset V) : f d ≤ virtualOnce U w f m coins d :=
  le_trans (base_le_fresh U hU hmono m d)
    (base_le_slotValue (fresh_mono U hmono m) _ (itemCoins_le hw coins) d)

end Mono

/-! ### The coin coupling -/

variable {Φ : Multiset V → ℝ≥0∞}

end FORS.Security.Domination
