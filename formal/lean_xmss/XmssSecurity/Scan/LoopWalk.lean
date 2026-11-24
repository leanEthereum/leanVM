module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

/-!
# The value of the scan loop `R = R0 + i`

A signer that derives one start `R0` per message and tries `R0, R0 + 1, ...` is, for one message and
one state of the digest cache, a walk over positions: a position is `fresh` (digest not queried: it
lands with probability `p`), a cached `miss` (the walk goes on) or a cached `hit` (the walk stops
there). `walk` is the expected payoff of the walk from a start, with a payoff `item x` at a cached
hit `x`, `fr` at a fresh position that lands and `ex` when the attempts are exhausted.

Main results, for a successor `σ` that does not return to a position within the attempt limit:

* `sum_reach_le`: the fresh starts reach a given position with total weight at most `(1 − p)/p`,
  where `reach` is the probability that a start reaches it.
* `sum_fresh_hit_le`: the fresh starts end at a cached hit with total weight at most `(1 − p)/p` per
  hit.

Nothing here mentions hashing.
-/

open ENNReal

namespace XmssSecurity.LoopWalk

/-- The status of a position for one message: digest not queried, queried and rejected, queried and
landing. -/
inductive St
  | fresh
  | miss
  | hit
  deriving DecidableEq

variable {α : Type} (σ : Equiv.Perm α) (p : ℝ≥0∞)

/-- Expected payoff of the scan from a start with a number of attempts. -/
noncomputable def walk (st : α → St) (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) : ℕ → α → ℝ≥0∞
  | 0, _ => ex
  | A + 1, r =>
      match st r with
      | .hit => item r
      | .miss => walk st item fr ex A (σ r)
      | .fresh => p * fr + (1 - p) * walk st item fr ex A (σ r)

variable {σ p}

theorem walk_zero (st : α → St) (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (r : α) :
    walk σ p st item fr ex 0 r = ex := rfl

theorem walk_succ_hit {st : α → St} (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (A : ℕ) {r : α} (h : st r = .hit) :
    walk σ p st item fr ex (A + 1) r = item r := by
  rw [walk, h]

theorem walk_succ_miss {st : α → St} (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (A : ℕ) {r : α} (h : st r = .miss) :
    walk σ p st item fr ex (A + 1) r = walk σ p st item fr ex A (σ r) := by
  rw [walk, h]

theorem walk_succ_fresh {st : α → St} (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (A : ℕ) {r : α} (h : st r = .fresh) :
    walk σ p st item fr ex (A + 1) r = p * fr + (1 - p) * walk σ p st item fr ex A (σ r) := by
  rw [walk, h]

/-- The walk is monotone in its payoffs. -/
theorem walk_mono (st : α → St) {item item' : α → ℝ≥0∞} {fr fr' ex ex' : ℝ≥0∞} (hi : ∀ x, item x ≤ item' x)
    (hf : fr ≤ fr') (he : ex ≤ ex') :
    ∀ (A : ℕ) (r : α), walk σ p st item fr ex A r ≤ walk σ p st item' fr' ex' A r
  | 0, _ => he
  | A + 1, r => by
      cases h : st r with
      | hit =>
          rw [walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ h]
          exact hi r
      | miss =>
          rw [walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ h]
          exact walk_mono st hi hf he A (σ r)
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ h]
          have := walk_mono st hi hf he A (σ r)
          gcongr

/-- Constant payoffs: the walk pays the constant. -/
theorem walk_const (hp : p ≤ 1) (st : α → St) (c : ℝ≥0∞) :
    ∀ (A : ℕ) (r : α), walk σ p st (fun _ => c) c c A r = c
  | 0, _ => rfl
  | A + 1, r => by
      cases h : st r with
      | hit => rw [walk_succ_hit _ _ _ _ h]
      | miss =>
          rw [walk_succ_miss _ _ _ _ h]
          exact walk_const hp st c A (σ r)
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, walk_const hp st c A (σ r), ← add_mul, add_tsub_cancel_of_le hp, one_mul]

/-- Payoffs at most `B`: the walk pays at most `B`. -/
theorem walk_le (hp : p ≤ 1) (st : α → St) {item : α → ℝ≥0∞} {fr ex B : ℝ≥0∞} (hi : ∀ x, item x ≤ B)
    (hf : fr ≤ B) (he : ex ≤ B) (A : ℕ) (r : α) : walk σ p st item fr ex A r ≤ B :=
  (walk_mono st hi hf he A r).trans (le_of_eq (walk_const hp st B A r))

/-! ### Reaching a position -/

variable (σ p) in
/-- Probability that the walk from a start reaches the position `y` (at `y` itself: one). -/
noncomputable def reach [DecidableEq α] (st : α → St) (y : α) : ℕ → α → ℝ≥0∞
  | 0, _ => 0
  | A + 1, r =>
      if r = y then 1 else
        match st r with
        | .hit => 0
        | .miss => reach st y A (σ r)
        | .fresh => (1 - p) * reach st y A (σ r)

section Reach

variable [DecidableEq α]

theorem reach_self (st : α → St) (y : α) (A : ℕ) : reach σ p st y (A + 1) y = 1 := by
  rw [reach, ite_eq_left rfl]

theorem reach_succ_hit {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .hit) :
    reach σ p st y (A + 1) r = 0 := by
  rw [reach, ite_eq_right hr, h]

theorem reach_succ_miss {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .miss) :
    reach σ p st y (A + 1) r = reach σ p st y A (σ r) := by
  rw [reach, ite_eq_right hr, h]

theorem reach_succ_fresh {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .fresh) :
    reach σ p st y (A + 1) r = (1 - p) * reach σ p st y A (σ r) := by
  rw [reach, ite_eq_right hr, h]

theorem reach_le_one (st : α → St) (y : α) : ∀ (A : ℕ) (r : α), reach σ p st y A r ≤ 1
  | 0, _ => zero_le_one
  | A + 1, r => by
      by_cases hr : r = y
      · rw [hr, reach_self]
      · cases h : st r with
        | hit => rw [reach_succ_hit A hr h]; exact zero_le_one
        | miss => rw [reach_succ_miss A hr h]; exact reach_le_one st y A (σ r)
        | fresh =>
            rw [reach_succ_fresh A hr h]
            exact (mul_le_mul' tsub_le_self (reach_le_one st y A (σ r))).trans (by rw [one_mul])

theorem reach_ne_top (st : α → St) (y : α) (A : ℕ) (r : α) : reach σ p st y A r ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top (reach_le_one st y A r)

/-! ### The fresh starts that reach a position -/

/-- Probability of passing the `i` positions before `y` (from the farthest one). -/
noncomputable def pass (σ : Equiv.Perm α) (p : ℝ≥0∞) (st : α → St) (y : α) : ℕ → ℝ≥0∞
  | 0 => 1
  | i + 1 =>
      (match st ((σ⁻¹ ^ (i + 1)) y) with
        | .hit => 0
        | .miss => 1
        | .fresh => 1 - p) * pass σ p st y i

/-- A start that reaches `y` is one of the positions before it. -/
theorem reach_ne_zero (st : α → St) (y : α) :
    ∀ (A : ℕ) (r : α), r ≠ y → reach σ p st y A r ≠ 0 → ∃ i, 0 < i ∧ i < A ∧ r = (σ⁻¹ ^ i) y
  | 0, r, _, h => absurd rfl h
  | A + 1, r, hr, h => by
      have hnext : reach σ p st y A (σ r) ≠ 0 := by
        cases h' : st r with
        | hit => rw [reach_succ_hit A hr h'] at h; exact absurd rfl h
        | miss => rwa [reach_succ_miss A hr h'] at h
        | fresh =>
            rw [reach_succ_fresh A hr h'] at h
            exact fun h0 => h (by rw [h0, mul_zero])
      by_cases hσ : σ r = y
      · refine ⟨1, Nat.one_pos, ?_, ?_⟩
        · rcases A with _ | A
          · exact absurd rfl hnext
          · omega
        · rw [pow_one, ← hσ]; simp
      · obtain ⟨i, h0, hi, hri⟩ := reach_ne_zero st y A (σ r) hσ hnext
        refine ⟨i + 1, Nat.succ_pos i, Nat.succ_lt_succ hi, ?_⟩
        rw [pow_succ', Equiv.Perm.mul_apply, ← hri]
        simp

/-- The `i`-th position before `y` reaches `y` with probability at most `pass i`. -/
theorem reach_le_pass (st : α → St) (y : α) (A : ℕ) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) :
    ∀ (i : ℕ), 0 < i → i < A → ∀ n, reach σ p st y n ((σ⁻¹ ^ i) y) ≤ pass σ p st y i := by
  have hne : ∀ i, 0 < i → i < A → (σ⁻¹ ^ i) y ≠ y := by
    intro i h0 hi heq
    apply hA i h0 hi
    have : (σ ^ i) ((σ⁻¹ ^ i) y) = y := by
      rw [inv_pow]
      simp
    rw [heq] at this
    exact this
  have hstep : ∀ i, σ ((σ⁻¹ ^ (i + 1)) y) = (σ⁻¹ ^ i) y := by
    intro i
    rw [pow_succ', Equiv.Perm.mul_apply]
    simp
  intro i
  induction i with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ i ih =>
      intro _ hi n
      have hr := hne (i + 1) (Nat.succ_pos i) hi
      have hprev : ∀ m, reach σ p st y m ((σ⁻¹ ^ i) y) ≤ pass σ p st y i := by
        intro m
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0
          exact reach_le_one st y m _
        · exact ih h0 (Nat.lt_of_succ_lt hi) m
      rcases n with _ | n
      · exact bot_le
      · rw [pass]
        cases h : st ((σ⁻¹ ^ (i + 1)) y) with
        | hit => rw [reach_succ_hit n hr h]; exact bot_le
        | miss =>
            rw [reach_succ_miss n hr h, hstep, one_mul]
            exact hprev n
        | fresh =>
            rw [reach_succ_fresh n hr h, hstep]
            exact mul_le_mul' le_rfl (hprev n)

/-- The fresh positions among the `j` positions before `y`, weighted by their passing
probabilities. -/
noncomputable def back (σ : Equiv.Perm α) (p : ℝ≥0∞) (st : α → St) (y : α) : ℕ → ℝ≥0∞
  | 0 => 0
  | j + 1 => back σ p st y j + (if st ((σ⁻¹ ^ (j + 1)) y) = .fresh then pass σ p st y (j + 1) else 0)

omit [DecidableEq α] in
/-- The invariant of the backward scan: `p · back + (1 − p) · pass ≤ 1 − p`. -/
theorem back_le (hp : p ≤ 1) (st : α → St) (y : α) :
    ∀ j, p * back σ p st y j + (1 - p) * pass σ p st y j ≤ 1 - p
  | 0 => by simp [back, pass]
  | j + 1 => by
      have ih := back_le hp st y j
      rw [back, pass]
      cases h : st ((σ⁻¹ ^ (j + 1)) y) with
      | hit =>
          simp only [zero_mul, mul_zero, add_zero, reduceCtorEq, ite_false]
          exact le_trans le_self_add ih
      | miss =>
          simp only [one_mul, reduceCtorEq, ite_false, add_zero]
          exact ih
      | fresh =>
          simp only [ite_true]
          set P := pass σ p st y j
          set B := back σ p st y j
          calc p * (B + (1 - p) * P) + (1 - p) * ((1 - p) * P)
              = p * B + (p + (1 - p)) * ((1 - p) * P) := by ring
            _ = p * B + (1 - p) * P := by rw [add_tsub_cancel_of_le hp, one_mul]
            _ ≤ _ := ih

omit [DecidableEq α] in
theorem sum_range_back (st : α → St) (y : α) (h : α → ℝ≥0∞) (hh : ∀ x, h x = if st x = .fresh then 1 else 0) :
    ∀ A, ∑ i ∈ Finset.range A, (if 0 < i then h ((σ⁻¹ ^ i) y) * pass σ p st y i else 0) =
      back σ p st y (A - 1)
  | 0 => rfl
  | 1 => by simp [back]
  | A + 2 => by
      have hb : back σ p st y (A + 1) = back σ p st y A +
          (if st ((σ⁻¹ ^ (A + 1)) y) = .fresh then pass σ p st y (A + 1) else 0) := rfl
      rw [Finset.sum_range_succ, sum_range_back st y h hh (A + 1)]
      simp only [Nat.add_sub_cancel, Nat.succ_pos, ite_true]
      rw [show A + 2 - 1 = A + 1 from rfl, hb, hh]
      split_ifs <;> simp

variable [Fintype α]

/-- **The fresh starts that reach a position** weigh at most `(1 − p)/p`. -/
theorem sum_reach_le (hp : p ≤ 1) (st : α → St) (y : α) (A : ℕ) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) :
    p * ∑ r, (if r ≠ y ∧ st r = .fresh then reach σ p st y A r else 0) ≤ 1 - p := by
  set h : α → ℝ≥0∞ := fun x => if st x = .fresh then 1 else 0 with hdef
  have hpoint : ∀ r, (if r ≠ y ∧ st r = .fresh then reach σ p st y A r else 0) ≤
      ∑ i ∈ Finset.range A, (if (σ⁻¹ ^ i) y = r then
        (if 0 < i then h ((σ⁻¹ ^ i) y) * pass σ p st y i else 0) else 0) := by
    intro r
    split_ifs with hr
    · by_cases h0 : reach σ p st y A r = 0
      · rw [h0]; exact bot_le
      · obtain ⟨i, hi0, hiA, hri⟩ := reach_ne_zero st y A r hr.1 h0
        subst hri
        refine le_trans ?_ (Finset.single_le_sum (f := fun j => if (σ⁻¹ ^ j) y = (σ⁻¹ ^ i) y then
          (if 0 < j then h ((σ⁻¹ ^ j) y) * pass σ p st y j else 0) else 0) (fun _ _ => bot_le)
          (Finset.mem_range.2 hiA))
        have hh : h ((σ⁻¹ ^ i) y) = 1 := ite_eq_left hr.2
        rw [ite_eq_left rfl, ite_eq_left hi0, hh, one_mul]
        exact reach_le_pass st y A hA i hi0 hiA A
    · exact bot_le
  calc p * ∑ r, (if r ≠ y ∧ st r = .fresh then reach σ p st y A r else 0)
      ≤ p * ∑ r, ∑ i ∈ Finset.range A, (if (σ⁻¹ ^ i) y = r then
          (if 0 < i then h ((σ⁻¹ ^ i) y) * pass σ p st y i else 0) else 0) := by
        gcongr with r _
        exact hpoint r
    _ = p * ∑ i ∈ Finset.range A, (if 0 < i then h ((σ⁻¹ ^ i) y) * pass σ p st y i else 0) := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = p * back σ p st y (A - 1) := by rw [sum_range_back st y h (fun _ => rfl)]
    _ ≤ p * back σ p st y (A - 1) + (1 - p) * pass σ p st y (A - 1) := le_self_add
    _ ≤ 1 - p := back_le hp st y _

end Reach

/-! ### The value of a message: all starts -/

section Group

variable [DecidableEq α] [Fintype α]

/-! ### The mass that stays on the identity -/

/-- A walk that ends at a cached hit reached one. -/
theorem hit_le_sum_reach (st : α → St) :
    ∀ (A : ℕ) (r : α), walk σ p st (fun _ => 1) 0 0 A r ≤
      ∑ x, (if st x = .hit then reach σ p st x A r else 0)
  | 0, _ => bot_le
  | A + 1, r => by
      cases h : st r with
      | hit =>
          rw [walk_succ_hit _ _ _ _ h]
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ r))
          rw [ite_eq_left h, reach_self]
      | miss =>
          rw [walk_succ_miss _ _ _ _ h]
          refine le_trans (hit_le_sum_reach st A (σ r)) (Finset.sum_le_sum fun x _ => ?_)
          split_ifs with hx
          · rw [reach_succ_miss A (fun hrx => by rw [hrx, hx] at h; cases h) h]
          · exact le_rfl
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, mul_zero, zero_add]
          refine le_trans (mul_le_mul' le_rfl (hit_le_sum_reach st A (σ r))) ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun x _ => ?_
          split_ifs with hx
          · rw [reach_succ_fresh A (fun hrx => by rw [hrx, hx] at h; cases h) h]
          · rw [mul_zero]

/-- The fresh starts end at a cached hit with total weight at most `(1 − p)/p` per hit. -/
theorem sum_fresh_hit_le (hp : p ≤ 1) (st : α → St) (A : ℕ) (hA : ∀ x j, 0 < j → j < A → (σ ^ j) x ≠ x) :
    p * ∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) ≤
      (Finset.univ.filter fun x => st x = .hit).card * (1 - p) := by
  calc p * ∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0)
      ≤ p * ∑ r, ∑ x, (if st x = .hit then (if r ≠ x ∧ st r = .fresh then reach σ p st x A r else 0) else 0) := by
        gcongr with r _
        split_ifs with hr
        · refine le_trans (hit_le_sum_reach st A r) (Finset.sum_le_sum fun x _ => ?_)
          split_ifs with hx hrx
          · exact le_rfl
          · exact absurd ⟨fun h => (by rw [h, hx] at hr; cases hr), hr⟩ hrx
          · exact le_rfl
        · exact bot_le
    _ = ∑ x, (if st x = .hit then p * ∑ r, (if r ≠ x ∧ st r = .fresh then reach σ p st x A r else 0) else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs
        · rfl
        · simp
    _ ≤ ∑ x, (if st x = .hit then (1 - p) else 0) := by
        refine Finset.sum_le_sum fun x _ => ?_
        split_ifs
        · exact sum_reach_le hp st x A (hA x)
        · exact le_rfl
    _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

end Group

end XmssSecurity.LoopWalk
