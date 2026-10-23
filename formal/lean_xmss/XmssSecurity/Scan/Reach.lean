import XmssSecurity.Scan.LoopWalk

/-!
# Reaching positions under one more query

* `reach_update_self`: the reach to `x` ignores the status of `x`.
* `reach_probe`: a query at a fresh position is a martingale for the reach to any position.
* `hitReach`: the probability that the walk stops at a cached hit. It equals the walk paying one at
  a hit (`hitReach_eq_walk`), so it is at most one and a new hit does not lower it.
* `mass_hit_le`: the starts weigh at most `card (cached) + card (hits) · (1 − p)/p` on the hits.
-/

open ENNReal

namespace XmssSecurity.LoopWalk

variable {α : Type} {σ : Equiv.Perm α} {p : ℝ≥0∞} [DecidableEq α]

/-- The reach to `x` does not depend on the status of `x`. -/
theorem reach_update_self (st : α → St) (x : α) (s : St) :
    ∀ (A : ℕ) (r : α), reach σ p (Function.update st x s) x A r = reach σ p st x A r
  | 0, _ => rfl
  | A + 1, r => by
      by_cases hr : r = x
      · rw [hr, reach_self, reach_self]
      · have hst : Function.update st x s r = st r := Function.update_of_ne hr _ _
        have ih := reach_update_self st x s A (σ r)
        cases h : st r with
        | hit => rw [reach_succ_hit A hr (hst.trans h), reach_succ_hit A hr h]
        | miss => rw [reach_succ_miss A hr (hst.trans h), reach_succ_miss A hr h, ih]
        | fresh => rw [reach_succ_fresh A hr (hst.trans h), reach_succ_fresh A hr h, ih]

/-- A position that the walk does not visit does not matter to the reach. -/
theorem reach_update_of_not_visit (st : α → St) (y x : α) (s : St) :
    ∀ (A : ℕ) (r : α), (∀ i, i < A → (σ ^ i) r ≠ x) →
      reach σ p (Function.update st x s) y A r = reach σ p st y A r
  | 0, _, _ => rfl
  | A + 1, r, h => by
      have hrx : r ≠ x := by simpa using h 0 (Nat.succ_pos A)
      have hnext : ∀ i, i < A → (σ ^ i) (σ r) ≠ x := fun i hi => by
        have := h (i + 1) (Nat.succ_lt_succ hi)
        rwa [pow_succ, Equiv.Perm.mul_apply] at this
      have hst : Function.update st x s r = st r := Function.update_of_ne hrx _ _
      have ih := reach_update_of_not_visit st y x s A (σ r) hnext
      by_cases hr : r = y
      · rw [hr, reach_self, reach_self]
      · cases h' : st r with
        | hit => rw [reach_succ_hit A hr (hst.trans h'), reach_succ_hit A hr h']
        | miss => rw [reach_succ_miss A hr (hst.trans h'), reach_succ_miss A hr h', ih]
        | fresh => rw [reach_succ_fresh A hr (hst.trans h'), reach_succ_fresh A hr h', ih]

/-- **One query is a martingale for the reach.** A query at the fresh position `x` (hit w.p. `p`,
miss otherwise) leaves the mean reach to any position unchanged. -/
theorem reach_probe (hp : p ≤ 1) (st : α → St) {x : α} (hx : st x = .fresh) (y : α) :
    ∀ (A : ℕ), (∀ j, 0 < j → j < A → (σ ^ j) x ≠ x) → ∀ r : α,
      p * reach σ p (Function.update st x .hit) y A r + (1 - p) * reach σ p (Function.update st x .miss) y A r =
        reach σ p st y A r
  | 0, _, r => by simp [reach]
  | A + 1, hA, r => by
      by_cases hry : r = y
      · rw [hry, reach_self, reach_self, reach_self, mul_one, mul_one, add_tsub_cancel_of_le hp]
      · by_cases hrx : r = x
        · rw [hrx] at hry ⊢
          have hmiss : reach σ p (Function.update st x .miss) y A (σ x) = reach σ p st y A (σ x) :=
            reach_update_of_not_visit st y x .miss A (σ x) (fun i hi => by
              have := hA (i + 1) (Nat.succ_pos i) (Nat.succ_lt_succ hi)
              rwa [pow_succ, Equiv.Perm.mul_apply] at this)
          rw [reach_succ_hit A hry (Function.update_self ..), reach_succ_miss A hry (Function.update_self ..),
            reach_succ_fresh A hry hx, hmiss, mul_zero, zero_add]
        · have hsth : Function.update st x St.hit r = st r := Function.update_of_ne hrx _ _
          have hstm : Function.update st x St.miss r = st r := Function.update_of_ne hrx _ _
          have ih := reach_probe hp st hx y A (fun j h0 hj => hA j h0 (Nat.lt_succ_of_lt hj)) (σ r)
          cases h : st r with
          | hit =>
              rw [reach_succ_hit A hry (hsth.trans h), reach_succ_hit A hry (hstm.trans h),
                reach_succ_hit A hry h, mul_zero, mul_zero, add_zero]
          | miss =>
              rw [reach_succ_miss A hry (hsth.trans h), reach_succ_miss A hry (hstm.trans h),
                reach_succ_miss A hry h, ih]
          | fresh =>
              rw [reach_succ_fresh A hry (hsth.trans h), reach_succ_fresh A hry (hstm.trans h),
                reach_succ_fresh A hry h, ← ih]
              ring

/-- The martingale for a set of targets. -/
theorem sum_reach_probe (hp : p ≤ 1) (st : α → St) {x : α} (hx : st x = .fresh) (P : Finset α) (A : ℕ)
    (hA : ∀ j, 0 < j → j < A → (σ ^ j) x ≠ x) (r : α) :
    p * ∑ y ∈ P, reach σ p (Function.update st x .hit) y A r +
        (1 - p) * ∑ y ∈ P, reach σ p (Function.update st x .miss) y A r =
      ∑ y ∈ P, reach σ p st y A r := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => reach_probe hp st hx y A hA r

variable [Fintype α]

/-- The martingale for a set of targets, summed over the starts. -/
theorem sum_sum_reach_probe (hp : p ≤ 1) (st : α → St) {x : α} (hx : st x = .fresh) (P : Finset α) (A : ℕ)
    (hA : ∀ j, 0 < j → j < A → (σ ^ j) x ≠ x) :
    p * ∑ r, ∑ y ∈ P, reach σ p (Function.update st x .hit) y A r +
        (1 - p) * ∑ r, ∑ y ∈ P, reach σ p (Function.update st x .miss) y A r =
      ∑ r, ∑ y ∈ P, reach σ p st y A r := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => sum_reach_probe hp st hx P A hA r

variable (σ p) in
/-- Probability that the walk from `r` stops at a cached hit. -/
noncomputable def hitReach (st : α → St) (A : ℕ) (r : α) : ℝ≥0∞ :=
  ∑ z, if st z = .hit then reach σ p st z A r else 0

/-- The hits reached are the walk that pays one at a hit. -/
theorem hitReach_eq_walk (st : α → St) :
    ∀ (A : ℕ) (r : α), hitReach σ p st A r = walk σ p st (fun _ => 1) 0 0 A r
  | 0, r => by simp [hitReach, reach, walk_zero]
  | A + 1, r => by
      cases h : st r with
      | hit =>
          rw [walk_succ_hit _ _ _ _ h, hitReach, Finset.sum_eq_single r]
          · rw [ite_eq_left h, reach_self]
          · intro z _ hz
            split_ifs
            · exact reach_succ_hit A (Ne.symm hz) h
            · rfl
          · simp
      | miss =>
          rw [walk_succ_miss _ _ _ _ h, ← hitReach_eq_walk st A (σ r), hitReach, hitReach]
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs with hz
          · exact reach_succ_miss A (fun hrz => by rw [hrz, hz] at h; cases h) h
          · rfl
      | fresh =>
          rw [walk_succ_fresh _ _ _ _ h, mul_zero, zero_add, ← hitReach_eq_walk st A (σ r), hitReach, hitReach,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          split_ifs with hz
          · exact reach_succ_fresh A (fun hrz => by rw [hrz, hz] at h; cases h) h
          · rw [mul_zero]

/-- The walk stops at a cached hit with probability at most one. -/
theorem hitReach_le_one (hp : p ≤ 1) (st : α → St) (A : ℕ) (r : α) : hitReach σ p st A r ≤ 1 := by
  rw [hitReach_eq_walk]
  exact walk_le hp st (fun _ => le_rfl) zero_le_one zero_le_one A r

omit [Fintype α] in
/-- A new hit, paying the most, does not lower the walk that pays one at a hit. -/
theorem walk_one_le_update (hp : p ≤ 1) (st : α → St) (x : α) :
    ∀ (A : ℕ) (r : α),
      walk σ p st (fun _ => 1) 0 0 A r ≤ walk σ p (Function.update st x .hit) (fun _ => 1) 0 0 A r
  | 0, _ => le_rfl
  | A + 1, r => by
      by_cases hr : r = x
      · rw [hr, walk_succ_hit _ _ _ _ (Function.update_self ..)]
        exact walk_le hp st (fun _ => le_rfl) zero_le_one zero_le_one _ x
      · have hst : Function.update st x St.hit r = st r := Function.update_of_ne hr _ _
        have ih := walk_one_le_update hp st x A (σ r)
        cases h : st r with
        | hit => rw [walk_succ_hit _ _ _ _ h, walk_succ_hit _ _ _ _ (hst.trans h)]
        | miss => rw [walk_succ_miss _ _ _ _ h, walk_succ_miss _ _ _ _ (hst.trans h)]; exact ih
        | fresh =>
            rw [walk_succ_fresh _ _ _ _ h, walk_succ_fresh _ _ _ _ (hst.trans h)]
            gcongr

/-- **Landing never lowers the hit mass.** -/
theorem hitReach_le_update (hp : p ≤ 1) (st : α → St) (x : α) (A : ℕ) (r : α) :
    hitReach σ p st A r ≤ hitReach σ p (Function.update st x .hit) A r := by
  rw [hitReach_eq_walk, hitReach_eq_walk]
  exact walk_one_le_update hp st x A r

/-- **The mass on the hits.** The starts reach the cached hits with total weight at most the number
of cached positions plus `(1 − p)/p` per cached hit. -/
theorem mass_hit_le (hp : p ≤ 1) (st : α → St) (A : ℕ) (hA : ∀ x j, 0 < j → j < A → (σ ^ j) x ≠ x) :
    p * ∑ z, (if st z = .hit then ∑ r, reach σ p st z A r else 0) ≤
      p * (Finset.univ.filter fun r => st r ≠ .fresh).card +
        (Finset.univ.filter fun z => st z = .hit).card * (1 - p) := by
  have hswap : ∑ z, (if st z = .hit then ∑ r, reach σ p st z A r else 0) = ∑ r, hitReach σ p st A r := by
    simp only [hitReach]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs <;> simp
  have hsplit : ∀ r, hitReach σ p st A r ≤
      (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) + (if st r ≠ .fresh then 1 else 0) := by
    intro r
    by_cases hr : st r = .fresh
    · rw [ite_eq_left hr, ite_eq_right (not_not.2 hr), add_zero, hitReach_eq_walk]
    · rw [ite_eq_right hr, ite_eq_left hr, zero_add]
      exact hitReach_le_one hp st A r
  have hcard : ∑ r, (if st r ≠ .fresh then (1 : ℝ≥0∞) else 0) = (Finset.univ.filter fun r => st r ≠ .fresh).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hswap]
  calc p * ∑ r, hitReach σ p st A r
      ≤ p * ∑ r, ((if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) +
          (if st r ≠ .fresh then 1 else 0)) := by
        gcongr with r _
        exact hsplit r
    _ = p * (Finset.univ.filter fun r => st r ≠ .fresh).card +
          p * ∑ r, (if st r = .fresh then walk σ p st (fun _ => 1) 0 0 A r else 0) := by
        rw [Finset.sum_add_distrib, hcard]; ring
    _ ≤ _ := add_le_add le_rfl (sum_fresh_hit_le hp st A hA)

end XmssSecurity.LoopWalk
