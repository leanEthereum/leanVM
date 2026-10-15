import SphincsFors.BridgeVirtualOnce

/-! The walk of a signer that tries `R0, R0 + 1, ...`. `val` is the expected payoff of a walk of
`a` attempts from a start: at `x` the walk stops with weight `s x` (payoff `c x`) and continues
with weight `t x`. Nothing here depends on the scheme: the randomizer space is a finite type with
a successor bijection. The facts proved are the ones a potential needs: linearity, the martingale
identity under one more query, and the bound on the mass that unqueried starts carry to a point. -/

open ENNReal

namespace SphincsFors.Security.Walk

variable {R : Type}

/-- Expected payoff of a walk of `a` attempts from `x`; `ev` is paid when the attempts run out. -/
noncomputable def val (e : R → R) (s t c : R → ℝ≥0∞) (ev : ℝ≥0∞) : ℕ → R → ℝ≥0∞
  | 0, _ => ev
  | a + 1, x => s x * c x + t x * val e s t c ev a (e x)

section Basic

variable (e : R → R) (s t : R → ℝ≥0∞)

theorem val_mono {c c' : R → ℝ≥0∞} {ev ev' : ℝ≥0∞} (hc : ∀ x, c x ≤ c' x) (hev : ev ≤ ev') :
    ∀ a x, val e s t c ev a x ≤ val e s t c' ev' a x
  | 0, _ => hev
  | a + 1, x => by
      simp only [val]
      exact add_le_add (mul_le_mul_right (hc x) _) (mul_le_mul_right (val_mono hc hev a (e x)) _)

theorem val_add (c c' : R → ℝ≥0∞) (ev ev' : ℝ≥0∞) :
    ∀ a x, val e s t (fun z => c z + c' z) (ev + ev') a x = val e s t c ev a x + val e s t c' ev' a x
  | 0, _ => rfl
  | a + 1, x => by
      simp only [val, val_add c c' ev ev' a (e x)]
      ring

theorem val_const_mul (k : ℝ≥0∞) (c : R → ℝ≥0∞) (ev : ℝ≥0∞) :
    ∀ a x, val e s t (fun z => k * c z) (k * ev) a x = k * val e s t c ev a x
  | 0, _ => rfl
  | a + 1, x => by
      simp only [val, val_const_mul k c ev a (e x)]
      ring

theorem val_const (hst : ∀ x, s x + t x = 1) (K : ℝ≥0∞) : ∀ a x, val e s t (fun _ => K) K a x = K
  | 0, _ => rfl
  | a + 1, x => by
      simp only [val, val_const hst K a (e x)]
      rw [← add_mul, hst, one_mul]

theorem val_le (hst : ∀ x, s x + t x ≤ 1) {c : R → ℝ≥0∞} {ev K : ℝ≥0∞} (hc : ∀ x, c x ≤ K) (hev : ev ≤ K) :
    ∀ a x, val e s t c ev a x ≤ K
  | 0, _ => hev
  | a + 1, x => by
      simp only [val]
      calc s x * c x + t x * val e s t c ev a (e x) ≤ s x * K + t x * K :=
            add_le_add (mul_le_mul_right (hc x) _) (mul_le_mul_right (val_le hst hc hev a (e x)) _)
        _ = (s x + t x) * K := by ring
        _ ≤ K := mul_le_of_le_one_left' (hst x)

theorem val_ge (hst : ∀ x, s x + t x = 1) {c : R → ℝ≥0∞} {ev K : ℝ≥0∞} (hc : ∀ x, K ≤ c x) (hev : K ≤ ev) :
    ∀ a x, K ≤ val e s t c ev a x
  | 0, _ => hev
  | a + 1, x => by
      simp only [val]
      calc K = s x * K + t x * K := by rw [← add_mul, hst, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_right (hc x) _) (mul_le_mul_right (val_ge hst hc hev a (e x)) _)

/-- Raising every payoff by `g` raises the value by at most `g`. -/
theorem val_add_const_le (hst : ∀ x, s x + t x ≤ 1) (c : R → ℝ≥0∞) (ev g : ℝ≥0∞) (a : ℕ) (x : R) :
    val e s t (fun z => c z + g) (ev + g) a x ≤ val e s t c ev a x + g := by
  rw [val_add]
  exact add_le_add le_rfl (val_le e s t hst (fun _ => le_rfl) le_rfl a x)

/-- The value only depends on the weights and payoffs along the walk. -/
theorem val_congr {s' t' c c' : R → ℝ≥0∞} (ev : ℝ≥0∞) :
    ∀ a x, (∀ j, j < a → s (e^[j] x) = s' (e^[j] x) ∧ t (e^[j] x) = t' (e^[j] x) ∧ c (e^[j] x) = c' (e^[j] x)) →
      val e s t c ev a x = val e s' t' c' ev a x
  | 0, _, _ => rfl
  | a + 1, x, h => by
      simp only [val]
      have h0 := h 0 (Nat.succ_pos a)
      simp only [Function.iterate_zero, id] at h0
      rw [h0.1, h0.2.1, h0.2.2, val_congr ev a (e x) fun j hj => by
        have := h (j + 1) (Nat.succ_lt_succ hj)
        simpa only [Function.iterate_succ_apply] using this]

end Basic

/-! ### One more query -/

section Query

variable [DecidableEq R] (e : R → R) (s t : R → ℝ≥0∞) (y : R)

/-- Weight with which a walk of `a` attempts from `x` reaches `y`. -/
noncomputable def arrive : ℕ → R → ℝ≥0∞
  | 0, _ => 0
  | a + 1, x => if x = y then 1 else t x * arrive a (e x)

theorem val_arrive :
    ∀ a x, val e (Function.update s y 1) (Function.update t y 0) (fun z => if z = y then 1 else 0) 0 a x =
      arrive e t y a x
  | 0, _ => rfl
  | a + 1, x => by
      simp only [val, arrive, val_arrive a (e x)]
      by_cases hx : x = y
      · subst hx; simp
      · simp [hx, Function.update_of_ne hx]

/-- **Martingale identity.** A point `y` that stops with weight `p` (payoff `c y`) becomes a stop
with payoff `cL` with probability `p` and a pass with probability `1 - p`: the mean value changes
by the arriving weight times the change of payoff. Valid while the walk meets `y` at most once. -/
theorem val_query (p : ℝ≥0∞) (hp : p ≤ 1) (hs : s y = p) (ht : t y = 1 - p) (c : R → ℝ≥0∞) (cL ev : ℝ≥0∞)
    (A : ℕ) (hfree : ∀ j, j < A → e^[j] (e y) ≠ y) :
    ∀ a x, a ≤ A + 1 →
      p * val e (Function.update s y 1) (Function.update t y 0) (Function.update c y cL) ev a x +
          (1 - p) * val e (Function.update s y 0) (Function.update t y 1) c ev a x +
          p * arrive e t y a x * c y =
        val e s t c ev a x + p * arrive e t y a x * cL
  | 0, x, _ => by
      simp only [val, arrive, mul_zero, zero_mul, add_zero]
      rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
  | a + 1, x, ha => by
      have hq : p + (1 - p) = 1 := add_tsub_cancel_of_le hp
      by_cases hx : x = y
      · subst hx
        have hkeep : val e (Function.update s x 0) (Function.update t x 1) c ev a (e x) = val e s t c ev a (e x) := by
          refine val_congr e _ _ ev a (e x) fun j hj => ?_
          have hne : e^[j] (e x) ≠ x := hfree j (by omega)
          simp [Function.update_of_ne hne]
        simp only [val, arrive, Function.update_self, if_true, hkeep, hs, ht]
        ring
      · have ih := val_query p hp hs ht c cL ev A hfree a (e x) (by omega)
        simp only [val, arrive, if_neg hx, Function.update_of_ne hx]
        set VL := val e (Function.update s y 1) (Function.update t y 0) (Function.update c y cL) ev a (e x)
        set VN := val e (Function.update s y 0) (Function.update t y 1) c ev a (e x)
        set V := val e s t c ev a (e x)
        set Ar := arrive e t y a (e x)
        calc p * (s x * c x + t x * VL) + (1 - p) * (s x * c x + t x * VN) + p * (t x * Ar) * c y
            = (p + (1 - p)) * (s x * c x) + t x * (p * VL + (1 - p) * VN + p * Ar * c y) := by ring
          _ = s x * c x + t x * (V + p * Ar * cL) := by rw [hq, one_mul, ih]
          _ = _ := by ring

/-- Making a point a stop with the least payoff lowers the value. -/
theorem val_stop_le (hst : ∀ x, s x + t x = 1) {c c' : R → ℝ≥0∞} {ev K : ℝ≥0∞} (hK : ∀ x, K ≤ c x)
    (hev : K ≤ ev) (hc : ∀ x, x ≠ y → c' x = c x) (hy : c' y = K) :
    ∀ a x, val e (Function.update s y 1) (Function.update t y 0) c' ev a x ≤ val e s t c ev a x
  | 0, _ => le_rfl
  | a + 1, x => by
      by_cases hx : x = y
      · subst hx
        simp only [val, Function.update_self, one_mul, zero_mul, add_zero, hy]
        exact val_ge e s t hst hK hev (a + 1) x
      · simp only [val, Function.update_of_ne hx, hc x hx]
        exact add_le_add le_rfl (mul_le_mul_right (val_stop_le hst hK hev hc hy a (e x)) _)

end Query

/-! ### Mass arriving from a set of starts -/

section Rank

variable [Fintype R] [DecidableEq R] (e : R ≃ R) (t : R → ℝ≥0∞) (y : R)

/-- Continuation weight with `y` absorbing. -/
noncomputable def tStop (x : R) : ℝ≥0∞ := if x = y then 0 else t x

/-- Weighted arrivals, read backwards from the target. -/
noncomputable def back (w : R → ℝ≥0∞) : ℕ → R → ℝ≥0∞
  | 0, _ => 0
  | a + 1, z => w z + tStop t y (e.symm z) * back w a (e.symm z)

/-- Weighted arrivals at `y`, with the weights pushed along the walk. -/
noncomputable def bsum (z : R) : ℕ → (R → ℝ≥0∞) → ℝ≥0∞
  | 0, _ => 0
  | a + 1, w => w z + bsum z a (fun x => tStop t y (e.symm x) * w (e.symm x))

theorem arrive_succ (a : ℕ) (x : R) :
    arrive e t y (a + 1) x = (if x = y then 1 else 0) + tStop t y x * arrive e t y a (e x) := by
  simp only [arrive, tStop]
  split_ifs <;> simp

theorem sum_arrive : ∀ a (w : R → ℝ≥0∞), ∑ x, w x * arrive e t y a x = bsum e t y y a w
  | 0, w => by simp [arrive, bsum]
  | a + 1, w => by
      have h1 : ∑ x, w x * (if x = y then (1 : ℝ≥0∞) else 0) = w y := by
        rw [Finset.sum_eq_single y (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ y) h)]
        simp
      have h2 : ∑ x, w x * (tStop t y x * arrive e t y a (e x)) =
          bsum e t y y a (fun x => tStop t y (e.symm x) * w (e.symm x)) := by
        calc ∑ x, w x * (tStop t y x * arrive e t y a (e x))
            = ∑ x, (fun x' => (tStop t y (e.symm x') * w (e.symm x')) * arrive e t y a x') (e x) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              simp only [Equiv.symm_apply_apply]
              ring
          _ = ∑ x', (tStop t y (e.symm x') * w (e.symm x')) * arrive e t y a x' :=
              Equiv.sum_comp e (fun x' => (tStop t y (e.symm x') * w (e.symm x')) * arrive e t y a x')
          _ = _ := sum_arrive a _
      simp only [arrive_succ, bsum, mul_add, Finset.sum_add_distrib, h1, h2]

theorem bsum_push : ∀ a (w : R → ℝ≥0∞) (z : R),
    bsum e t y z a (fun x => tStop t y (e.symm x) * w (e.symm x)) =
      tStop t y (e.symm z) * bsum e t y (e.symm z) a w
  | 0, _, _ => by simp [bsum]
  | a + 1, w, z => by
      simp only [bsum]
      rw [bsum_push a (fun x => tStop t y (e.symm x) * w (e.symm x)) z, mul_add]

theorem bsum_eq_back (w : R → ℝ≥0∞) : ∀ a z, bsum e t y z a w = back e t y w a z
  | 0, _ => rfl
  | a + 1, z => by
      simp only [bsum, back]
      rw [bsum_push, bsum_eq_back w a (e.symm z)]

/-- **Rank bound.** Starts whose continuation weight is at most `τ` carry at most `κ` to a point,
when `τ (1 + κ) ≤ κ`. -/
theorem sum_arrive_le (w : R → ℝ≥0∞) (τ κ : ℝ≥0∞) (hτ : τ * (1 + κ) ≤ κ) (ht : ∀ x, t x ≤ 1)
    (hw1 : ∀ x, w x ≤ 1) (hwy : w y = 0) (hwt : ∀ x, w x ≠ 0 → t x ≤ τ) (a : ℕ) :
    ∑ x, w x * arrive e t y a x ≤ κ := by
  rw [sum_arrive, bsum_eq_back]
  have hts : ∀ x, tStop t y x ≤ 1 := fun x => by
    unfold tStop; split_ifs
    · exact bot_le
    · exact ht x
  have key : ∀ a z, back e t y w a z ≤ w z + κ := by
    intro a
    induction a with
    | zero => intro z; exact bot_le
    | succ a ih =>
        intro z
        simp only [back]
        refine add_le_add le_rfl ?_
        set z' := e.symm z
        by_cases hz : w z' = 0
        · calc tStop t y z' * back e t y w a z' ≤ 1 * (w z' + κ) := mul_le_mul' (hts z') (ih z')
            _ = κ := by rw [hz, zero_add, one_mul]
        · have h1 : tStop t y z' ≤ τ := by
            unfold tStop; split_ifs
            · exact bot_le
            · exact hwt z' hz
          calc tStop t y z' * back e t y w a z' ≤ τ * (1 + κ) :=
                mul_le_mul' h1 (le_trans (ih z') (add_le_add (hw1 z') le_rfl))
            _ ≤ κ := hτ
  have := key a y
  rwa [hwy, zero_add] at this

end Rank

end SphincsFors.Security.Walk
