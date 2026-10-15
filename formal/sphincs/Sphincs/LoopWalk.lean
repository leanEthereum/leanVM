import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The value of the scan loop `R = R0 + i`

A signer that derives one start `R0` per message and tries `R0, R0 + 1, ...` is, for one message and
one state of the digest cache, a walk over positions: a position is `fresh` (digest not queried: it
lands with probability `p`), a cached `miss` (the walk goes on) or a cached `hit` (the walk stops
there). `walk` is the expected payoff of the walk from a start, with a payoff `item x` at a cached
hit `x`, `fr` at a fresh position that lands and `ex` when the attempts are exhausted.

Main results, for a successor `σ` that does not return to a position within the attempt limit:

* `probe_eq`: one digest query at a fresh position `y`. Averaged over its two outcomes (hit with
  payoff `c`, miss), the walk from any other start changes by `p · reach · (c − fr)`, where `reach`
  is the probability that the start reaches `y`.
* `sum_reach_le`: the fresh starts reach a given position with total weight at most `(1 − p)/p`.
* `creation_le`: with the group value `gv` (fresh payoff `base` for a fresh start, `favg` for a
  cached one: the pending mass of dangling queries), a query raises the value by at most
  `(2 − p) · (favg − base)` in the mean. This is the creation rate of the scan loop: `2 − p` times
  the rate of independent attempts, and it is attained.
* `mass_le`: the starts that do not end at a cached hit weigh at least
  `card − (cached positions) − (cached hits) · (1 − p)/p`.

Nothing here mentions hashing.
-/

open ENNReal

namespace Sphincs.LoopWalk

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

/-- The walk is additive in its payoffs. -/
theorem walk_add (st : α → St) (item item' : α → ℝ≥0∞) (fr fr' ex ex' : ℝ≥0∞) :
    ∀ (A : ℕ) (r : α), walk σ p st (fun x => item x + item' x) (fr + fr') (ex + ex') A r =
      walk σ p st item fr ex A r + walk σ p st item' fr' ex' A r
  | 0, _ => rfl
  | A + 1, r => by
      cases h : st r with
      | hit => rw [walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ h]
      | miss =>
          rw [walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ h]
          exact walk_add st item item' fr fr' ex ex' A (σ r)
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ h,
            walk_add st item item' fr fr' ex ex' A (σ r)]
          ring

/-- The walk is homogeneous in its payoffs. -/
theorem walk_const_mul (st : α → St) (item : α → ℝ≥0∞) (fr ex c : ℝ≥0∞) :
    ∀ (A : ℕ) (r : α), walk σ p st (fun x => c * item x) (c * fr) (c * ex) A r =
      c * walk σ p st item fr ex A r
  | 0, _ => rfl
  | A + 1, r => by
      cases h : st r with
      | hit => rw [walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ h]
      | miss =>
          rw [walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ h]
          exact walk_const_mul st item fr ex c A (σ r)
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ h, walk_const_mul st item fr ex c A (σ r)]
          ring

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

/-- Payoffs at least `c`: the walk pays at least `c`. -/
theorem le_walk (hp : p ≤ 1) (st : α → St) {item : α → ℝ≥0∞} {fr ex c : ℝ≥0∞} (hi : ∀ x, c ≤ item x)
    (hf : c ≤ fr) (he : c ≤ ex) (A : ℕ) (r : α) : c ≤ walk σ p st item fr ex A r :=
  (le_of_eq (walk_const hp st c A r).symm).trans (walk_mono st hi hf he A r)

/-- **A stopped walk is below the walk.** Turning a position into a hit that pays no more than any
other outcome can only lower the payoff. -/
theorem walk_stop_le [DecidableEq α] (hp : p ≤ 1) (st : α → St) {item : α → ℝ≥0∞} {fr ex c : ℝ≥0∞}
    (hi : ∀ x, c ≤ item x) (hf : c ≤ fr) (he : c ≤ ex) (y : α) :
    ∀ (A : ℕ) (r : α), walk σ p (Function.update st y .hit) (Function.update item y c) fr ex A r ≤
      walk σ p st item fr ex A r
  | 0, _ => le_rfl
  | A + 1, r => by
      by_cases hr : r = y
      · subst hr
        rw [walk_succ_hit _ _ _ _ (Function.update_self ..), Function.update_self]
        exact le_walk hp st hi hf he (A + 1) r
      · have hst : Function.update st y St.hit r = st r := Function.update_of_ne hr _ _
        have hit : Function.update item y c r = item r := Function.update_of_ne hr _ _
        have ih := walk_stop_le hp st hi hf he y A (σ r)
        cases h : st r with
        | hit => rw [walk_succ_hit _ _ _ _ (hst.trans h), walk_succ_hit _ _ _ _ h, hit]
        | miss => rw [walk_succ_miss _ _ _ _ (hst.trans h), walk_succ_miss _ _ _ _ h]; exact ih
        | fresh =>
            rw [walk_succ_fresh _ _ _ _ (hst.trans h), walk_succ_fresh _ _ _ _ h]
            gcongr

/-- The walk is affine in the fresh payoff. -/
theorem walk_fr_add (st : α → St) (item : α → ℝ≥0∞) (fr δ ex : ℝ≥0∞) (A : ℕ) (r : α) :
    walk σ p st item (fr + δ) ex A r =
      walk σ p st item fr ex A r + δ * walk σ p st (fun _ => 0) 1 0 A r := by
  have h := walk_add (σ := σ) (p := p) st item (fun _ => δ * 0) fr (δ * 1) ex (δ * 0) A r
  rw [walk_const_mul] at h
  simpa only [mul_zero, add_zero, mul_one] using h

/-- Only the payoffs at cached hits matter. -/
theorem walk_congr_item (st : α → St) {item item' : α → ℝ≥0∞} (fr ex : ℝ≥0∞)
    (h : ∀ x, st x = .hit → item x = item' x) :
    ∀ (A : ℕ) (r : α), walk σ p st item fr ex A r = walk σ p st item' fr ex A r
  | 0, _ => rfl
  | A + 1, r => by
      cases h' : st r with
      | hit => rw [walk_succ_hit _ _ _ _ h', walk_succ_hit _ _ _ _ h', h r h']
      | miss => rw [walk_succ_miss _ _ _ _ h', walk_succ_miss _ _ _ _ h', walk_congr_item st fr ex h A (σ r)]
      | fresh => rw [walk_succ_fresh _ _ _ _ h', walk_succ_fresh _ _ _ _ h', walk_congr_item st fr ex h A (σ r)]

/-- A position that the walk does not visit does not matter. -/
theorem walk_update_of_not_visit [DecidableEq α] (st : α → St) (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (y : α)
    (s : St) (c : ℝ≥0∞) :
    ∀ (A : ℕ) (r : α), (∀ i, i < A → (σ ^ i) r ≠ y) →
      walk σ p (Function.update st y s) (Function.update item y c) fr ex A r = walk σ p st item fr ex A r
  | 0, _, _ => rfl
  | A + 1, r, h => by
      have hr : r ≠ y := by simpa using h 0 (Nat.succ_pos A)
      have hnext : ∀ i, i < A → (σ ^ i) (σ r) ≠ y := fun i hi => by
        have := h (i + 1) (Nat.succ_lt_succ hi)
        rwa [pow_succ, Equiv.Perm.mul_apply] at this
      have hst : Function.update st y s r = st r := Function.update_of_ne hr _ _
      have hit : Function.update item y c r = item r := Function.update_of_ne hr _ _
      have ih := walk_update_of_not_visit st item fr ex y s c A (σ r) hnext
      cases h' : st r with
      | hit => rw [walk_succ_hit _ _ _ _ (hst.trans h'), walk_succ_hit _ _ _ _ h', hit]
      | miss => rw [walk_succ_miss _ _ _ _ (hst.trans h'), walk_succ_miss _ _ _ _ h', ih]
      | fresh => rw [walk_succ_fresh _ _ _ _ (hst.trans h'), walk_succ_fresh _ _ _ _ h', ih]

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
  rw [reach, if_pos rfl]

theorem reach_succ_hit {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .hit) :
    reach σ p st y (A + 1) r = 0 := by
  rw [reach, if_neg hr, h]

theorem reach_succ_miss {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .miss) :
    reach σ p st y (A + 1) r = reach σ p st y A (σ r) := by
  rw [reach, if_neg hr, h]

theorem reach_succ_fresh {st : α → St} {y r : α} (A : ℕ) (hr : r ≠ y) (h : st r = .fresh) :
    reach σ p st y (A + 1) r = (1 - p) * reach σ p st y A (σ r) := by
  rw [reach, if_neg hr, h]

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

/-- **One query, one start.** A fresh position `y` is queried: it becomes a hit with payoff `c` with
probability `p` and a miss otherwise. In the mean the walk from any start gains `p · reach · c` and
loses `p · reach · fr`. -/
theorem probe_eq (hp : p ≤ 1) (st : α → St) (item : α → ℝ≥0∞) (fr ex c : ℝ≥0∞) (y : α)
    (hy : st y = .fresh) :
    ∀ (A : ℕ), (∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) → ∀ r : α,
      p * walk σ p (Function.update st y .hit) (Function.update item y c) fr ex A r +
          (1 - p) * walk σ p (Function.update st y .miss) item fr ex A r +
          p * reach σ p st y A r * fr =
        walk σ p st item fr ex A r + p * reach σ p st y A r * c
  | 0, _, r => by
      simp only [walk_zero, reach, mul_zero, zero_mul, add_zero]
      rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
  | A + 1, hA, r => by
      have hA' : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y := fun j h0 hj => hA j h0 (Nat.lt_succ_of_lt hj)
      by_cases hr : r = y
      · subst hr
        have hmiss : walk σ p (Function.update st r .miss) item fr ex A (σ r) = walk σ p st item fr ex A (σ r) := by
          have h := walk_update_of_not_visit (σ := σ) (p := p) st item fr ex r .miss (item r) A (σ r)
            (fun i hi => by
              have := hA (i + 1) (Nat.succ_pos i) (Nat.succ_lt_succ hi)
              rwa [pow_succ, Equiv.Perm.mul_apply] at this)
          rwa [Function.update_eq_self] at h
        rw [walk_succ_hit _ _ _ _ (Function.update_self ..), walk_succ_miss _ _ _ _ (Function.update_self ..),
          walk_succ_fresh _ _ _ _ hy, reach_self, Function.update_self, hmiss]
        ring
      · have hsth : Function.update st y St.hit r = st r := Function.update_of_ne hr _ _
        have hstm : Function.update st y St.miss r = st r := Function.update_of_ne hr _ _
        have hitem : Function.update item y c r = item r := Function.update_of_ne hr _ _
        have ih := probe_eq hp st item fr ex c y hy A hA' (σ r)
        cases h : st r with
        | hit =>
            rw [walk_succ_hit _ _ _ _ (hsth.trans h), walk_succ_hit _ _ _ _ (hstm.trans h),
              walk_succ_hit _ _ _ _ h, reach_succ_hit A hr h, hitem]
            simp only [mul_zero, zero_mul, add_zero]
            rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
        | miss =>
            rw [walk_succ_miss _ _ _ _ (hsth.trans h), walk_succ_miss _ _ _ _ (hstm.trans h),
              walk_succ_miss _ _ _ _ h, reach_succ_miss A hr h]
            exact ih
        | fresh =>
            rw [walk_succ_fresh _ _ _ _ (hsth.trans h), walk_succ_fresh _ _ _ _ (hstm.trans h),
              walk_succ_fresh _ _ _ _ h, reach_succ_fresh A hr h]
            set W1 := walk σ p (Function.update st y St.hit) (Function.update item y c) fr ex A (σ r)
            set W2 := walk σ p (Function.update st y St.miss) item fr ex A (σ r)
            set W := walk σ p st item fr ex A (σ r)
            set ρ := reach σ p st y A (σ r)
            have hsplit : p * (p * fr) + (1 - p) * (p * fr) = p * fr := by
              rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
            calc p * (p * fr + (1 - p) * W1) + (1 - p) * (p * fr + (1 - p) * W2) + p * ((1 - p) * ρ) * fr
                = (p * (p * fr) + (1 - p) * (p * fr)) + (1 - p) * (p * W1 + (1 - p) * W2 + p * ρ * fr) := by ring
              _ = p * fr + (1 - p) * (W + p * ρ * c) := by rw [hsplit, ih]
              _ = _ := by ring

/-- The hit branch of a query is affine in the payoff of the new hit. -/
theorem walk_update_item (st : α → St) (item : α → ℝ≥0∞) (fr ex c : ℝ≥0∞) (y : α) (hy : st y = .hit) :
    ∀ (A : ℕ), (∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) → ∀ r : α,
      walk σ p st (Function.update item y c) fr ex A r =
        walk σ p st (Function.update item y 0) fr ex A r + reach σ p st y A r * c
  | 0, _, r => by simp [walk_zero, reach]
  | A + 1, hA, r => by
      have hA' : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y := fun j h0 hj => hA j h0 (Nat.lt_succ_of_lt hj)
      by_cases hr : r = y
      · subst hr
        rw [walk_succ_hit _ _ _ _ hy, walk_succ_hit _ _ _ _ hy, reach_self, Function.update_self,
          Function.update_self, zero_add, one_mul]
      · have ih := walk_update_item st item fr ex c y hy A hA' (σ r)
        cases h : st r with
        | hit =>
            rw [walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ h, reach_succ_hit A hr h,
              Function.update_of_ne hr, Function.update_of_ne hr, zero_mul, add_zero]
        | miss =>
            rw [walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ h, reach_succ_miss A hr h]
            exact ih
        | fresh =>
            rw [walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ h, reach_succ_fresh A hr h, ih]
            ring

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
theorem pass_le_one (st : α → St) (y : α) : ∀ i, pass σ p st y i ≤ 1
  | 0 => le_rfl
  | i + 1 => by
      rw [pass]
      refine (mul_le_mul' ?_ (pass_le_one st y i)).trans (by rw [one_mul])
      cases st ((σ⁻¹ ^ (i + 1)) y) with
      | hit => exact zero_le_one
      | miss => exact le_rfl
      | fresh => exact tsub_le_self

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
          simp only [zero_mul, mul_zero, add_zero, reduceCtorEq, if_false]
          exact le_trans le_self_add ih
      | miss =>
          simp only [one_mul, reduceCtorEq, if_false, add_zero]
          exact ih
      | fresh =>
          simp only [if_true]
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
      simp only [Nat.add_sub_cancel, Nat.succ_pos, if_true]
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
        have hh : h ((σ⁻¹ ^ i) y) = 1 := if_pos hr.2
        rw [if_pos rfl, if_pos hi0, hh, one_mul]
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

variable (σ p) in
/-- **The group value** of one message, up to the factor `1 / card`: the sum over the starts of the
walk payoffs, where a fresh position that lands pays `base` to a fresh start (the view of that
signature is fresh: nothing beyond the slot) and `favg` to a cached start (pending mass of a
dangling query). Exhausted attempts pay `base`. -/
noncomputable def gv (st : α → St) (item : α → ℝ≥0∞) (base favg : ℝ≥0∞) (A : ℕ) : ℝ≥0∞ :=
  ∑ r, walk σ p st item (if st r = .fresh then base else favg) base A r

omit [DecidableEq α] in
theorem gv_add (st : α → St) (item item' : α → ℝ≥0∞) (base base' favg favg' : ℝ≥0∞) (A : ℕ) :
    gv σ p st (fun x => item x + item' x) (base + base') (favg + favg') A =
      gv σ p st item base favg A + gv σ p st item' base' favg' A := by
  unfold gv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← walk_add]
  congr 1
  split_ifs <;> rfl

omit [DecidableEq α] in
theorem gv_const_mul (st : α → St) (item : α → ℝ≥0∞) (base favg c : ℝ≥0∞) (A : ℕ) :
    gv σ p st (fun x => c * item x) (c * base) (c * favg) A = c * gv σ p st item base favg A := by
  unfold gv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← walk_const_mul]
  congr 1
  split_ifs <;> rfl

omit [DecidableEq α] in
theorem gv_mono (st : α → St) {item item' : α → ℝ≥0∞} {base base' favg favg' : ℝ≥0∞}
    (hi : ∀ x, item x ≤ item' x) (hb : base ≤ base') (hf : favg ≤ favg') (A : ℕ) :
    gv σ p st item base favg A ≤ gv σ p st item' base' favg' A := by
  unfold gv
  refine Finset.sum_le_sum fun r _ => walk_mono st hi ?_ hb A r
  split_ifs
  · exact hb
  · exact hf

omit [DecidableEq α] in
/-- Constant payoffs: every start pays the constant. -/
theorem gv_const (hp : p ≤ 1) (st : α → St) (c : ℝ≥0∞) (A : ℕ) :
    gv σ p st (fun _ => c) c c A = Fintype.card α * c := by
  unfold gv
  simp only [ite_self, walk_const hp st c A, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq α] in
theorem gv_congr_item (st : α → St) {item item' : α → ℝ≥0∞} (base favg : ℝ≥0∞)
    (h : ∀ x, st x = .hit → item x = item' x) (A : ℕ) :
    gv σ p st item base favg A = gv σ p st item' base favg A := by
  unfold gv
  exact Finset.sum_congr rfl fun r _ => walk_congr_item st _ _ h A r

omit [DecidableEq α] in
theorem gv_zero (st : α → St) (A : ℕ) : gv σ p st (fun _ => 0) 0 0 A = 0 := by
  have h := gv_const_mul (σ := σ) (p := p) st (fun _ => 0) 0 0 0 A
  simpa using h

omit [DecidableEq α] in
/-- The group value is additive over finite sums of payoffs. -/
theorem gv_sum {ι : Type} [DecidableEq ι] (T : Finset ι) (st : α → St) (f : ι → α → ℝ≥0∞) (b fa : ι → ℝ≥0∞)
    (A : ℕ) :
    gv σ p st (fun x => ∑ t ∈ T, f t x) (∑ t ∈ T, b t) (∑ t ∈ T, fa t) A =
      ∑ t ∈ T, gv σ p st (f t) (b t) (fa t) A := by
  induction T using Finset.induction_on with
  | empty => simp [gv_zero]
  | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      rw [gv_add, ih]

omit [DecidableEq α] in
/-- No cached position: every start pays `base`. -/
theorem gv_fresh (hp : p ≤ 1) (st : α → St) (hst : ∀ r, st r = .fresh) (item : α → ℝ≥0∞) (base favg : ℝ≥0∞)
    (A : ℕ) : gv σ p st item base favg A = Fintype.card α * base := by
  have hw : ∀ (A : ℕ) (r : α), walk σ p st item base base A r = base := by
    intro A
    induction A with
    | zero => intro r; rfl
    | succ A ih =>
        intro r
        rw [walk_succ_fresh _ _ _ _ (hst r), ih, ← add_mul, add_tsub_cancel_of_le hp, one_mul]
  unfold gv
  simp only [hst, if_true, hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A group value with one more hit that pays the base value is below the group value. -/
theorem gv_stop_le (hp : p ≤ 1) (st : α → St) {item : α → ℝ≥0∞} {base favg : ℝ≥0∞} (hi : ∀ x, base ≤ item x)
    (hf : base ≤ favg) (y : α) (hy : st y = .fresh) (A : ℕ) :
    gv σ p (Function.update st y .hit) (Function.update item y base) base favg A ≤ gv σ p st item base favg A := by
  unfold gv
  refine Finset.sum_le_sum fun r _ => ?_
  by_cases hr : r = y
  · subst hr
    rw [if_neg (by rw [Function.update_self]; simp), if_pos hy]
    rcases A with _ | A
    · exact le_rfl
    · rw [walk_succ_hit _ _ _ _ (Function.update_self ..), Function.update_self]
      exact le_walk hp st hi le_rfl le_rfl (A + 1) r
  · rw [Function.update_of_ne hr]
    refine walk_stop_le hp st hi ?_ le_rfl y A r
    split_ifs
    · exact le_rfl
    · exact hf

/-- The group value as an explicit linear form in its payoffs. -/
theorem gv_decomp (st : α → St) (item : α → ℝ≥0∞) (base favg : ℝ≥0∞) (A : ℕ) :
    gv σ p st item base favg A =
      ∑ z, item z * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A +
        base * gv σ p st (fun _ => 0) 1 0 A + favg * gv σ p st (fun _ => 0) 0 1 A := by
  have hitem : gv σ p st item 0 0 A = ∑ z, item z * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A := by
    have hz : ∀ z, gv σ p st (fun x => item z * (if x = z then 1 else 0)) 0 0 A =
        item z * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A := by
      intro z
      have h := gv_const_mul (σ := σ) (p := p) st (fun x => if x = z then 1 else 0) 0 0 (item z) A
      simpa using h
    have h := gv_sum (σ := σ) (p := p) Finset.univ st (fun z x => item z * (if x = z then 1 else 0))
      (fun _ => 0) (fun _ => 0) A
    simp only [Finset.sum_const_zero, hz] at h
    rw [← h]
    congr 1
    funext x
    simp
  calc gv σ p st item base favg A
      = gv σ p st (fun x => (item x + base * 0) + favg * 0) ((0 + base * 1) + favg * 0) ((0 + base * 0) + favg * 1) A := by
        simp
    _ = _ := by
        rw [gv_add st (fun x => item x + base * 0) (fun _ => favg * 0), gv_add st item (fun _ => base * 0),
          gv_const_mul, gv_const_mul, hitem]

omit [Fintype α] in
/-- One query, one start: the mean payoff after a query at the fresh position `y` (hit with payoff
`favg = base + δ`, or miss). -/
theorem start_le (hp : p ≤ 1) (st : α → St) (item : α → ℝ≥0∞) (base δ : ℝ≥0∞) (hbase : base ≠ ⊤)
    (hδ : δ ≠ ⊤) (y : α) (hy : st y = .fresh) (A : ℕ) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) (r : α) :
    p * walk σ p (Function.update st y .hit) (Function.update item y (base + δ))
          (if Function.update st y St.hit r = .fresh then base else base + δ) base A r +
        (1 - p) * walk σ p (Function.update st y .miss) item
          (if Function.update st y St.miss r = .fresh then base else base + δ) base A r ≤
      walk σ p st item (if st r = .fresh then base else base + δ) base A r +
        (if r ≠ y ∧ st r = .fresh then p * reach σ p st y A r * δ else 0) + (if r = y then δ else 0) := by
  by_cases hr : r = y
  · subst hr
    rw [Function.update_self, Function.update_self, if_neg (by simp), if_neg (by simp), if_pos hy,
      if_neg (by simp), if_pos rfl, add_zero]
    rcases A with _ | A
    · simp only [walk_zero]
      rw [← add_mul, add_tsub_cancel_of_le hp, one_mul]
      exact le_self_add
    · have hmiss : walk σ p (Function.update st r .miss) item (base + δ) base A (σ r) =
          walk σ p st item (base + δ) base A (σ r) := by
        have h := walk_update_of_not_visit (σ := σ) (p := p) st item (base + δ) base r .miss (item r) A (σ r)
          (fun i hi => by
            have := hA (i + 1) (Nat.succ_pos i) (Nat.succ_lt_succ hi)
            rwa [pow_succ, Equiv.Perm.mul_apply] at this)
        rwa [Function.update_eq_self] at h
      rw [walk_succ_hit _ _ _ _ (Function.update_self ..), walk_succ_miss _ _ _ _ (Function.update_self ..),
        walk_succ_fresh _ _ _ _ hy, Function.update_self, hmiss, walk_fr_add]
      set X := walk σ p st item base base A (σ r)
      set F := walk σ p st (fun _ => 0) 1 0 A (σ r)
      have hF : F ≤ 1 := walk_le hp st (fun _ => zero_le_one) le_rfl zero_le_one A (σ r)
      calc p * (base + δ) + (1 - p) * (X + δ * F)
          ≤ p * (base + δ) + (1 - p) * (X + δ * 1) := by gcongr
        _ = p * base + (1 - p) * X + (p + (1 - p)) * δ := by ring
        _ = p * base + (1 - p) * X + δ := by rw [add_tsub_cancel_of_le hp, one_mul]
  · have hsth : Function.update st y St.hit r = st r := Function.update_of_ne hr _ _
    have hstm : Function.update st y St.miss r = st r := Function.update_of_ne hr _ _
    rw [hsth, hstm, if_neg hr, add_zero]
    have hρ : p * reach σ p st y A r ≠ ⊤ :=
      ENNReal.mul_ne_top (ne_top_of_le_ne_top one_ne_top hp) (reach_ne_top st y A r)
    by_cases hfr : st r = .fresh
    · rw [if_pos hfr, if_pos ⟨hr, hfr⟩]
      have h := probe_eq hp st item base base (base + δ) y hy A hA r
      have h2 : p * walk σ p (Function.update st y .hit) (Function.update item y (base + δ)) base base A r +
          (1 - p) * walk σ p (Function.update st y .miss) item base base A r + p * reach σ p st y A r * base =
          (walk σ p st item base base A r + p * reach σ p st y A r * δ) + p * reach σ p st y A r * base := by
        rw [h]; ring
      exact le_of_eq ((ENNReal.add_left_inj (ENNReal.mul_ne_top hρ hbase)).1 h2)
    · rw [if_neg hfr, if_neg (fun h => hfr h.2), add_zero]
      have h := probe_eq hp st item (base + δ) base (base + δ) y hy A hA r
      exact le_of_eq ((ENNReal.add_left_inj (ENNReal.mul_ne_top hρ (ENNReal.add_ne_top.2 ⟨hbase, hδ⟩))).1 h)

/-- **The creation rate of the scan loop.** A query at a fresh position raises the group value by at
most `(2 − p) δ` in the mean, `δ = favg − base` the gain of a fresh uniform view. -/
theorem creation_le (hp : p ≤ 1) (st : α → St) (item : α → ℝ≥0∞) (base δ : ℝ≥0∞) (hbase : base ≠ ⊤)
    (hδ : δ ≠ ⊤) (y : α) (hy : st y = .fresh) (A : ℕ) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) :
    p * gv σ p (Function.update st y .hit) (Function.update item y (base + δ)) base (base + δ) A +
        (1 - p) * gv σ p (Function.update st y .miss) item base (base + δ) A ≤
      gv σ p st item base (base + δ) A + (1 - p) * δ + δ := by
  unfold gv
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine le_trans (Finset.sum_le_sum fun r _ => start_le hp st item base δ hbase hδ y hy A hA r) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ y (fun _ => δ),
    if_pos (Finset.mem_univ y)]
  gcongr
  have h := sum_reach_le hp st y A hA
  calc ∑ r, (if r ≠ y ∧ st r = .fresh then p * reach σ p st y A r * δ else 0)
      = (p * ∑ r, (if r ≠ y ∧ st r = .fresh then reach σ p st y A r else 0)) * δ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        split_ifs <;> simp
    _ ≤ (1 - p) * δ := mul_le_mul' h le_rfl

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
          rw [if_pos h, reach_self]
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

/-- **The mass on the identity.** The starts whose walk leaves the disclosures unchanged (a fresh
start that ends at a fresh position, or exhausted attempts) weigh at least the number of positions
minus the cached ones and `(1 − p)/p` per cached hit. -/
theorem mass_le (hp : p ≤ 1) (st : α → St) (A : ℕ) (hA : ∀ x j, 0 < j → j < A → (σ ^ j) x ≠ x) :
    p * (Fintype.card α : ℝ≥0∞) ≤
      p * gv σ p st (fun _ => 0) 1 0 A + p * (Finset.univ.filter fun r => st r ≠ .fresh).card +
        (Finset.univ.filter fun x => st x = .hit).card * (1 - p) := by
  have hone : ∀ r, (1 : ℝ≥0∞) = walk σ p st (fun _ => 0) (if st r = .fresh then 1 else 0) 1 A r +
      walk σ p st (fun _ => 1) (if st r = .fresh then 0 else 1) 0 A r := by
    intro r
    rw [← walk_add]
    have h := walk_const (σ := σ) hp st (1 : ℝ≥0∞) A r
    convert h.symm using 2
    · simp
    · split_ifs <;> simp
    · simp
  have hoth : ∀ r, walk σ p st (fun _ => 1) (if st r = .fresh then 0 else 1) 0 A r ≤
      (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) + (if st r ≠ .fresh then 1 else 0) := by
    intro r
    by_cases hr : st r = .fresh
    · simp [hr]
    · rw [if_neg hr, if_neg hr, zero_add, if_pos hr]
      exact walk_le hp st (fun _ => le_rfl) le_rfl zero_le_one A r
  have hcard : (Fintype.card α : ℝ≥0∞) ≤ gv σ p st (fun _ => 0) 1 0 A +
      (∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) +
        (Finset.univ.filter fun r => st r ≠ .fresh).card) := by
    calc (Fintype.card α : ℝ≥0∞) = ∑ _r : α, (1 : ℝ≥0∞) := by simp
      _ = ∑ r, (walk σ p st (fun _ => 0) (if st r = .fresh then 1 else 0) 1 A r +
            walk σ p st (fun _ => 1) (if st r = .fresh then 0 else 1) 0 A r) :=
          Finset.sum_congr rfl fun r _ => hone r
      _ ≤ ∑ r, (walk σ p st (fun _ => 0) (if st r = .fresh then 1 else 0) 1 A r +
            ((if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) + (if st r ≠ .fresh then 1 else 0))) :=
          Finset.sum_le_sum fun r _ => add_le_add le_rfl (hoth r)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          congr 2
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc p * (Fintype.card α : ℝ≥0∞) ≤ p * (gv σ p st (fun _ => 0) 1 0 A +
        (∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) +
          (Finset.univ.filter fun r => st r ≠ .fresh).card)) := mul_le_mul' le_rfl hcard
    _ = p * gv σ p st (fun _ => 0) 1 0 A + p * (Finset.univ.filter fun r => st r ≠ .fresh).card +
          p * ∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) := by ring
    _ ≤ _ := add_le_add le_rfl (sum_fresh_hit_le hp st A hA)

omit [DecidableEq α] in
/-- A payoff that is at least `c` on the identity outcomes: the group value is at least `c` times
the mass on the identity. -/
theorem gv_ge (st : α → St) (item : α → ℝ≥0∞) (c favg : ℝ≥0∞) (A : ℕ) :
    c * gv σ p st (fun _ => 0) 1 0 A ≤ gv σ p st item c favg A := by
  rw [← gv_const_mul]
  refine gv_mono st (fun _ => by simp) (by simp) (by simp) A

end Group

end Sphincs.LoopWalk
