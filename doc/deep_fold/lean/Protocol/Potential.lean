/-
The potential for points reused across the fold rounds of a level, abstractly: the general form
behind Lemma 4.12 of the paper, for one batch and for a schedule.

Nothing here knows of polynomials. A state `h : H k r` is what the verifier's messages so far
determine, after `k` fold rounds of the level and with `r` rounds to come. A verifier message
`m : M k r` moves a state with `r + 1` rounds to come to `step k r h m`, and `g k r h ≥ 0` is the
cost of the round played from `h` (for one batch, the indicator that the points are exceptional
for the current word). The potential is

  `pot k 0 h = 0`,   `pot k (r + 1) h = g k r h + τ⁻¹ · E_m[pot (k + 1) r (step k r h m)]`,

and `pot_eq_sum` shows that it is the sum of equation (8) of the paper: `∑_j τ^(-j) · (mean cost of
the round played j messages later)`. Prover messages do not occur: the potential is a function of
the state.
-/
import Mathlib

open Finset
open scoped Classical

namespace Protocol

section Mean

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The mean of `f` under the uniform distribution on a finite type. -/
noncomputable def avg (f : α → ℚ) : ℚ := (∑ a, f a) / Fintype.card α

/-- The probability of `p` under the uniform distribution on a finite type. -/
noncomputable def dens (p : α → Prop) : ℚ := ((univ.filter p).card : ℚ) / Fintype.card α

theorem dens_eq_avg (p : α → Prop) : dens p = avg (fun a => if p a then (1 : ℚ) else 0) := by
  simp [dens, avg]

/-- `dens` of membership in a finite set is its cardinality over the size of the type, the form
in which `DeepFold` states its densities. -/
theorem dens_mem (S : Finset α) : dens (fun a => a ∈ S) = (S.card : ℚ) / Fintype.card α := by
  simp [dens]

theorem avg_nonneg {f : α → ℚ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun a _ => hf a) (Nat.cast_nonneg _)

theorem avg_mono {f g : α → ℚ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

theorem avg_add (f g : α → ℚ) : avg (fun a => f a + g a) = avg f + avg g := by
  simp [avg, sum_add_distrib, add_div]

theorem avg_mul_left (c : ℚ) (f : α → ℚ) : avg (fun a => c * f a) = c * avg f := by
  simp [avg, ← mul_sum, mul_div_assoc]

theorem avg_zero : avg (fun _ : α => (0 : ℚ)) = 0 := by
  simp [avg]

theorem avg_const [Nonempty α] (c : ℚ) : avg (fun _ : α => c) = c := by
  have h : (Fintype.card α : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem avg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℚ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  simp only [avg]
  rw [sum_comm, sum_div]

/-- Exchange of two means (Fubini for finite uniform distributions). -/
theorem avg_comm (f : α → β → ℚ) :
    avg (fun a => avg (fun b => f a b)) = avg (fun b => avg (fun a => f a b)) := by
  simp only [avg, ← sum_div]
  rw [sum_comm, div_div, div_div, mul_comm]

/-- The mean over a product is the iterated mean. -/
theorem avg_prod (f : α × β → ℚ) : avg f = avg (fun a => avg (fun b => f (a, b))) := by
  simp only [avg, ← sum_div, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [div_div, mul_comm]

/-- The mean is invariant under a bijection. -/
theorem avg_equiv (e : α ≃ β) (f : β → ℚ) : avg (fun a => f (e a)) = avg f := by
  simp only [avg, Fintype.card_congr e]
  rw [Equiv.sum_comp e f]

theorem dens_nonneg (p : α → Prop) : 0 ≤ dens p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem dens_le_one (p : α → Prop) : dens p ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_univ _

theorem dens_mono {p p' : α → Prop} (h : ∀ a, p a → p' a) : dens p ≤ dens p' := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_le_card (fun a ha => by
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact h a ha)

/-- The union bound. -/
theorem dens_or_le (p p' : α → Prop) : dens (fun a => p a ∨ p' a) ≤ dens p + dens p' := by
  rw [dens_eq_avg, dens_eq_avg, dens_eq_avg, ← avg_add]
  apply avg_mono
  intro a
  by_cases h : p a <;> by_cases h' : p' a <;> simp [h, h']

/-- Markov's inequality at threshold one. -/
theorem dens_le_avg {f : α → ℚ} (hf : ∀ a, 0 ≤ f a) : dens (fun a => 1 ≤ f a) ≤ avg f := by
  rw [dens_eq_avg]
  apply avg_mono
  intro a
  split_ifs with h
  · exact h
  · exact hf a

end Mean

section Potential

variable {H : ℕ → ℕ → Type*} {M : ℕ → ℕ → Type*} [∀ k r, Fintype (M k r)]

/-- The potential of a state with `r` rounds to come, after `k` rounds: zero when no round is
left, and otherwise the cost of the round played now plus `τ⁻¹` times the mean, over the next
verifier message, of the potential of the next state. -/
noncomputable def pot (τ : ℚ) (step : ∀ k r, H k (r + 1) → M k r → H (k + 1) r)
    (g : ∀ k r, H k (r + 1) → ℚ) : ∀ (k r : ℕ), H k r → ℚ
  | _, 0, _ => 0
  | k, r + 1, h => g k r h + τ⁻¹ * avg (fun m => pot τ step g (k + 1) r (step k r h m))

variable {τ : ℚ} {step : ∀ k r, H k (r + 1) → M k r → H (k + 1) r} {g : ∀ k r, H k (r + 1) → ℚ}

@[simp] theorem pot_zero (k : ℕ) (h : H k 0) : pot τ step g k 0 h = 0 := rfl

theorem pot_succ (k r : ℕ) (h : H k (r + 1)) :
    pot τ step g k (r + 1) h =
      g k r h + τ⁻¹ * avg (fun m => pot τ step g (k + 1) r (step k r h m)) := rfl

theorem pot_nonneg (hτ : 0 ≤ τ) (hg : ∀ k r h, 0 ≤ g k r h) :
    ∀ (r k : ℕ) (h : H k r), 0 ≤ pot τ step g k r h
  | 0, _, _ => le_rfl
  | r + 1, k, h => by
      rw [pot_succ]
      exact add_nonneg (hg k r h)
        (mul_nonneg (inv_nonneg.mpr hτ) (avg_nonneg fun m => pot_nonneg hτ hg r (k + 1) _))

/-- The mean of the next potential is `τ` times what the current potential has beyond the cost of
the current round. -/
theorem avg_pot_step (hτ : 0 < τ) (k r : ℕ) (h : H k (r + 1)) :
    avg (fun m => pot τ step g (k + 1) r (step k r h m)) =
      τ * (pot τ step g k (r + 1) h - g k r h) := by
  rw [pot_succ]
  field_simp
  ring

/-- The two uses of a potential below one. The cost of the current round is below one, and the
next verifier message brings the potential to one or more with probability less than `τ`. -/
theorem pot_step (hτ : 0 < τ) (hg : ∀ k r h, 0 ≤ g k r h) {k r : ℕ} {h : H k (r + 1)}
    (hlt : pot τ step g k (r + 1) h < 1) :
    g k r h < 1 ∧ dens (fun m => 1 ≤ pot τ step g (k + 1) r (step k r h m)) < τ := by
  have hnn : ∀ m, 0 ≤ pot τ step g (k + 1) r (step k r h m) :=
    fun m => pot_nonneg hτ.le hg r (k + 1) _
  have havg := avg_pot_step (step := step) (g := g) hτ k r h
  have h0 : 0 ≤ avg (fun m => pot τ step g (k + 1) r (step k r h m)) := avg_nonneg hnn
  have h1 : 0 ≤ pot τ step g k (r + 1) h - g k r h := by
    rw [havg] at h0
    exact nonneg_of_mul_nonneg_right h0 hτ
  refine ⟨by linarith, lt_of_le_of_lt (dens_le_avg hnn) ?_⟩
  rw [havg]
  have h2 : pot τ step g k (r + 1) h - g k r h < 1 := by linarith [hg k r h]
  calc τ * (pot τ step g k (r + 1) h - g k r h) < τ * 1 := mul_lt_mul_of_pos_left h2 hτ
    _ = τ := mul_one τ

/-- The mean cost of the round played `j` verifier messages after the state `h`: the cost of the
current round for `j = 0`, and the mean over the next message of the same quantity for `j - 1`
otherwise. It is zero when fewer than `j + 1` rounds are left. -/
noncomputable def meanCost (step : ∀ k r, H k (r + 1) → M k r → H (k + 1) r)
    (g : ∀ k r, H k (r + 1) → ℚ) : ℕ → ∀ (k r : ℕ), H k r → ℚ
  | _, _, 0, _ => 0
  | 0, k, r + 1, h => g k r h
  | j + 1, k, r + 1, h => avg (fun m => meanCost step g j (k + 1) r (step k r h m))

theorem meanCost_zero (k r : ℕ) (h : H k (r + 1)) : meanCost step g 0 k (r + 1) h = g k r h := rfl

theorem meanCost_succ (j k r : ℕ) (h : H k (r + 1)) :
    meanCost step g (j + 1) k (r + 1) h =
      avg (fun m => meanCost step g j (k + 1) r (step k r h m)) := rfl

/-- The potential as the sum of equation (8) of the paper: `Ψ = ∑_j τ^(-j) · (mean cost of the
round played j messages later)`, the sum over the rounds still to come. -/
theorem pot_eq_sum : ∀ (r k : ℕ) (h : H k r),
    pot τ step g k r h = ∑ j ∈ range r, τ⁻¹ ^ j * meanCost step g j k r h
  | 0, _, _ => by simp
  | r + 1, k, h => by
      rw [pot_succ, sum_range_succ']
      simp only [pow_zero, one_mul, meanCost_zero, meanCost_succ]
      rw [add_comm]
      congr 1
      have hrec : (fun m => pot τ step g (k + 1) r (step k r h m)) =
          fun m => ∑ j ∈ range r, τ⁻¹ ^ j * meanCost step g j (k + 1) r (step k r h m) :=
        funext fun m => pot_eq_sum r (k + 1) _
      rw [hrec, avg_sum, mul_sum]
      refine sum_congr rfl (fun j _ => ?_)
      rw [avg_mul_left, pow_succ]
      ring

end Potential

section LemmaT

variable {A : ℕ → ℕ → Type*} {C : ℕ → ℕ → Type*} [∀ k r, Fintype (C k r)] {Z : Type*}

/-- The potential `Ψ` of Lemma 4.12 of the paper for one batch. `a : A k r` is the committed word
folded by the `k` challenges so far, with `r` rounds to come; `fold` folds it by one challenge;
`z` is the vector of points, fixed before the challenges; and `bad k r a z` says that `z` is
exceptional for the round played from `a` (`z ∈ Exc_{k+1}(a)`). The cost of a round is the
indicator of `bad`. -/
noncomputable def potT (τ : ℚ) (fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r)
    (bad : ∀ k r, A k (r + 1) → Z → Prop) (z : Z) : ∀ (k r : ℕ), A k r → ℚ :=
  pot τ fold (fun k r a => if bad k r a z then 1 else 0)

/-- `π`: the probability, over `j` independent uniform challenges, that `z` is exceptional for
the round played from the word then reached (zero if no such round is left). -/
noncomputable def probBad (fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r)
    (bad : ∀ k r, A k (r + 1) → Z → Prop) (z : Z) : ℕ → ∀ (k r : ℕ), A k r → ℚ :=
  meanCost fold (fun k r a => if bad k r a z then 1 else 0)

variable {τ : ℚ} {fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r}
  {bad : ∀ k r, A k (r + 1) → Z → Prop}

/-- `Ψ_ℓ = 0`: no potential when no round is left. -/
@[simp] theorem potT_zero (z : Z) (k : ℕ) (a : A k 0) : potT τ fold bad z k 0 a = 0 := rfl

theorem potT_succ (z : Z) (k r : ℕ) (a : A k (r + 1)) :
    potT τ fold bad z k (r + 1) a = (if bad k r a z then 1 else 0) +
      τ⁻¹ * avg (fun c => potT τ fold bad z (k + 1) r (fold k r a c)) := rfl

/-- In the last round the potential is the indicator, with no `τ`. -/
theorem potT_one (z : Z) (k : ℕ) (a : A k 1) :
    potT τ fold bad z k 1 a = if bad k 0 a z then 1 else 0 := by
  simp [potT_succ, avg_zero]

theorem potT_nonneg (hτ : 0 ≤ τ) (z : Z) (k r : ℕ) (a : A k r) : 0 ≤ potT τ fold bad z k r a :=
  pot_nonneg hτ (fun _ _ _ => by split_ifs <;> norm_num) r k a

theorem probBad_zero (z : Z) (k r : ℕ) (a : A k (r + 1)) :
    probBad fold bad z 0 k (r + 1) a = if bad k r a z then 1 else 0 := rfl

theorem probBad_succ (z : Z) (j k r : ℕ) (a : A k (r + 1)) :
    probBad fold bad z (j + 1) k (r + 1) a =
      avg (fun c => probBad fold bad z j (k + 1) r (fold k r a c)) := rfl

/-- The sum of equation (8) of the paper: `Ψ_k = ∑_{j} τ^(-j) π_j`, over the rounds still to come,
`π_j` the probability over the next `j` challenges that `z` is exceptional for the word they
lead to. -/
theorem potT_eq_sum (z : Z) (k r : ℕ) (a : A k r) :
    potT τ fold bad z k r a = ∑ j ∈ range r, τ⁻¹ ^ j * probBad fold bad z j k r a :=
  pot_eq_sum r k a

/-- The number of sequences of `j` challenges after which `z` is exceptional for the round
played from the word reached (zero if no such round is left). -/
noncomputable def badSeqs (fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r)
    (bad : ∀ k r, A k (r + 1) → Z → Prop) (z : Z) : ℕ → ∀ (k r : ℕ), A k r → ℕ
  | _, _, 0, _ => 0
  | 0, k, r + 1, a => if bad k r a z then 1 else 0
  | j + 1, k, r + 1, a => ∑ c, badSeqs fold bad z j (k + 1) r (fold k r a c)

/-- `π` as a count: when every challenge space has `Q` elements, `π_j` is the number of
sequences of `j` challenges that lead to a word for which `z` is exceptional, over `Q^j`. So the
iterated mean in `probBad` is the probability over `j` independent uniform challenges. -/
theorem probBad_eq_card {Q : ℕ} (hQ : ∀ k r, Fintype.card (C k r) = Q) (z : Z) :
    ∀ (j k r : ℕ) (a : A k r),
      probBad fold bad z j k r a = (badSeqs fold bad z j k r a : ℚ) / (Q : ℚ) ^ j
  | j, k, 0, a => by
      cases j <;> simp [probBad, meanCost, badSeqs]
  | 0, k, r + 1, a => by
      rw [probBad_zero]
      simp only [badSeqs, pow_zero, div_one]
      split_ifs <;> simp
  | j + 1, k, r + 1, a => by
      have h : ∀ c, probBad fold bad z j (k + 1) r (fold k r a c) =
          (badSeqs fold bad z j (k + 1) r (fold k r a c) : ℚ) / (Q : ℚ) ^ j :=
        fun c => probBad_eq_card hQ z j (k + 1) r _
      rw [probBad_succ, avg, hQ k r]
      simp only [h, badSeqs, ← sum_div, Nat.cast_sum, div_div, pow_succ]

/-- Lemma 4.12(b) of the paper. The points `z` are fixed and the word `a` is the committed word
folded by the challenges so far. If the potential is below one, then `z` is not exceptional for
the current round's word, and the set of next challenges after which the potential is one or more
has density less than `τ`. -/
theorem potT_step (hτ : 0 < τ) {z : Z} {k r : ℕ} {a : A k (r + 1)}
    (h : potT τ fold bad z k (r + 1) a < 1) :
    ¬ bad k r a z ∧ dens (fun c => 1 ≤ potT τ fold bad z (k + 1) r (fold k r a c)) < τ := by
  obtain ⟨h1, h2⟩ := pot_step hτ (fun _ _ _ => by split_ifs <;> norm_num) h
  refine ⟨fun hb => ?_, h2⟩
  simp only [hb, ite_true, lt_self_iff_false] at h1

variable [Fintype Z] [∀ k r, Nonempty (C k r)]

/-- The mean of the potential over the points, when round `(k, r)` is exceptional with
probability at most `e k r` for every word of its shape. -/
theorem avg_potT_le (hτ : 0 ≤ τ) (e : ℕ → ℕ → ℚ)
    (he : ∀ k r (a : A k (r + 1)), dens (fun z => bad k r a z) ≤ e k r) :
    ∀ (r k : ℕ) (a : A k r), avg (fun z => potT τ fold bad z k r a) ≤
      ∑ j ∈ range r, τ⁻¹ ^ j * e (k + j) (r - 1 - j)
  | 0, _, _ => by simp [avg_zero]
  | r + 1, k, a => by
      have hfun : (fun z => potT τ fold bad z k (r + 1) a) = fun z =>
          (if bad k r a z then (1 : ℚ) else 0) +
            τ⁻¹ * avg (fun c => potT τ fold bad z (k + 1) r (fold k r a c)) :=
        funext fun z => potT_succ z k r a
      rw [hfun, avg_add, avg_mul_left, avg_comm, ← dens_eq_avg, sum_range_succ']
      simp only [pow_zero, one_mul, add_zero, Nat.add_sub_cancel, Nat.sub_zero]
      rw [add_comm]
      refine add_le_add ?_ (he k r a)
      have h1 : avg (fun c => avg (fun z => potT τ fold bad z (k + 1) r (fold k r a c))) ≤
          ∑ j ∈ range r, τ⁻¹ ^ j * e (k + 1 + j) (r - 1 - j) :=
        (avg_mono fun c => avg_potT_le hτ e he r (k + 1) (fold k r a c)).trans_eq (avg_const _)
      calc τ⁻¹ * avg (fun c => avg (fun z => potT τ fold bad z (k + 1) r (fold k r a c)))
          ≤ τ⁻¹ * ∑ j ∈ range r, τ⁻¹ ^ j * e (k + 1 + j) (r - 1 - j) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hτ)
        _ = ∑ j ∈ range r, τ⁻¹ ^ (j + 1) * e (k + (j + 1)) (r - (j + 1)) := by
            rw [mul_sum]
            refine sum_congr rfl (fun j _ => ?_)
            rw [show k + 1 + j = k + (j + 1) by omega, show r - 1 - j = r - (j + 1) by omega,
              pow_succ]
            ring

/-- Lemma 4.12(a) of the paper, with a bound per round. If, for every word of the shape of round
`(k, r)`, the points are exceptional with probability at most `e k r`, then the potential of the
committed word is one or more with probability at most `∑_j τ^(-j) e_j` over the points. -/
theorem potT_init (hτ : 0 ≤ τ) (e : ℕ → ℕ → ℚ)
    (he : ∀ k r (a : A k (r + 1)), dens (fun z => bad k r a z) ≤ e k r)
    (k r : ℕ) (a : A k r) :
    dens (fun z => 1 ≤ potT τ fold bad z k r a) ≤
      ∑ j ∈ range r, τ⁻¹ ^ j * e (k + j) (r - 1 - j) :=
  (dens_le_avg fun z => potT_nonneg hτ z k r a).trans (avg_potT_le hτ e he r k a)

/-- Lemma 4.12(a) of the paper: `Pr_z[Ψ_0 ≥ 1] ≤ ε_* ∑_{j < ℓ} τ^(-j)`, when `ε_*` bounds the
probability that the points are exceptional, for every round still to come and every word of the
shape of that round. The rounds to come from `(k, r)` are the `(k', r')` with `k ≤ k'` and
`k' + r' + 1 = k + r`. -/
theorem potT_init_const (hτ : 0 ≤ τ) {ε : ℚ} (k r : ℕ)
    (he : ∀ k' r', k ≤ k' → k' + r' + 1 = k + r → ∀ a : A k' (r' + 1),
      dens (fun z => bad k' r' a z) ≤ ε) (a : A k r) :
    dens (fun z => 1 ≤ potT τ fold bad z k r a) ≤ ε * ∑ j ∈ range r, τ⁻¹ ^ j := by
  have h := potT_init (fold := fold) (bad := bad) hτ
    (fun k' r' => if k ≤ k' ∧ k' + r' + 1 = k + r then ε else 1)
    (fun k' r' a' => by
      split_ifs with hk
      · exact he k' r' hk.1 hk.2 a'
      · exact dens_le_one _) k r a
  refine h.trans_eq ?_
  rw [mul_sum]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' := mem_range.mp hj
  have hc : k ≤ k + j ∧ k + j + (r - 1 - j) + 1 = k + r := ⟨by omega, by omega⟩
  simp only [hc, and_self, ite_true]
  ring

end LemmaT

end Protocol
