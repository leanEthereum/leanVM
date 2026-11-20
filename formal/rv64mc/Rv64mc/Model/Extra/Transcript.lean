/-
  Rv64mc.Model.Extra.Transcript

  `Model.Sponge`'s values in the forms the compiled code computes them: a challenge's limbs are the two lanes it
  is made of.
-/

import Rv64mc.Model.Transcript

namespace Rv64mc.Model

theorem limbs_ofLimbsW (w : Limbs) : limbs (ofLimbsW w) = w := by
  rw [ofLimbsW, limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

/-- The challenge's limbs: lanes `0` and `1`. -/
theorem limbs_challengeRust (s : List (BitVec 64)) : limbs (challengeRust s) = (s.getD 0 0, s.getD 1 0) := by
  rw [challengeRust, limbs_ofLimbsW]

/-! ## The lanes of a duplex, one at a time (`Model.Sponge`'s own lemmas are private) -/

open LeanVM.Parameters

private theorem x_length_foldl_of {α β : Type} (step : List α → β → List α)
    (h : ∀ s k, (step s k).length = s.length) (L : List β) (s : List α) :
    (L.foldl step s).length = s.length := by
  induction L generalizing s with
  | nil => rfl
  | cons a L ih => rw [List.foldl_cons, ih, h]

private theorem x_getD_foldl_set_range (o n : ℕ) (f : ℕ → BitVec 64) (s : List (BitVec 64)) (j : ℕ) :
    ((List.range n).foldl (fun s i ↦ s.set (o + i) (f i)) s).getD j 0 =
      if o ≤ j ∧ j < o + n ∧ j < s.length then f (j - o) else s.getD j 0 := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_set, ih,
      x_length_foldl_of _ (fun _ _ ↦ List.length_set ..)]
    by_cases h1 : o + n = j
    · subst h1
      by_cases h2 : o + n < s.length <;> simp [h2]
    · by_cases h3 : o ≤ j ∧ j < o + n ∧ j < s.length
      · simp [h1, h3, show j < o + (n + 1) by omega]
      · have h4 : ¬ (o ≤ j ∧ j < o + (n + 1) ∧ j < s.length) := by omega
        simp [h1, h3, h4]

private theorem x_getD_fillRate (s : List (BitVec 64)) (j : ℕ) :
    (fillRate s).getD j 0 = if j < 16 ∧ j < s.length then 0 else s.getD j 0 := by
  have e : fillRate s = (List.range 16).foldl (fun s i ↦ s.set (0 + i) ((fun _ ↦ 0#64) i)) s := by
    simp only [fillRate, Nat.zero_add]
  rw [e, x_getD_foldl_set_range]
  simp only [Nat.zero_le, true_and, Nat.zero_add]
  rfl

private theorem x_length_fillRate (s : List (BitVec 64)) : (fillRate s).length = s.length :=
  x_length_foldl_of _ (fun _ _ ↦ List.length_set ..) _ _

private theorem x_length_writeLanes (s : List (BitVec 64)) (i : ℕ) (w : List (BitVec 64)) :
    (writeLanes s i w).length = s.length :=
  x_length_foldl_of _ (fun _ _ ↦ List.length_set ..) _ _

private theorem x_getD_writeLanes (s : List (BitVec 64)) (i : ℕ) (w : List (BitVec 64)) (j : ℕ) :
    (writeLanes s i w).getD j 0 =
      if 4 * i ≤ j ∧ j < 4 * i + 4 ∧ j < s.length then w.getD (j - 4 * i) 0 else s.getD j 0 := by
  rw [writeLanes, x_getD_foldl_set_range]
  rfl

/-- The writes of the waiting scalars `ps`, the `k`-th at slot `n + k`. -/
private theorem x_getD_writes (ps : List (E × BitVec 64)) (n : ℕ) (s : List (BitVec 64))
    (hs : s.length = 25) (hn : 4 * (n + ps.length) ≤ 16) (j : ℕ) :
    ((ps.zipIdx n).foldl (fun s pi ↦ writeLanes s pi.2 (pendingWords pi.1)) s).getD j 0 =
      if 4 * n ≤ j ∧ j < 4 * (n + ps.length) then
        (pendingWords (ps.getD ((j - 4 * n) / 4) (0, 0#64))).getD (j % 4) 0
      else s.getD j 0 := by
  induction ps generalizing n s with
  | nil => simp
  | cons p ps ih =>
    simp only [List.length_cons] at hn
    rw [List.zipIdx_cons, List.foldl_cons, ih (n + 1) _ (by rw [x_length_writeLanes, hs])
      (by omega), x_getD_writeLanes, hs]
    simp only [List.length_cons]
    by_cases h1 : 4 * (n + 1) ≤ j ∧ j < 4 * (n + 1 + ps.length)
    · rw [ite_eq_left h1, ite_eq_left ⟨by omega, by omega⟩]
      rw [show (j - 4 * n) / 4 = (j - 4 * (n + 1)) / 4 + 1 by omega, List.getD_cons_succ]
    · rw [ite_eq_right h1]
      by_cases h2 : 4 * n ≤ j ∧ j < 4 * n + 4
      · rw [ite_eq_left ⟨h2.1, h2.2, by omega⟩, ite_eq_left ⟨h2.1, by omega⟩,
          show (j - 4 * n) / 4 = 0 by omega, List.getD_cons_zero]
        congr 1
        omega
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem x_length_writes (ps : List (E × BitVec 64)) (n : ℕ) (s : List (BitVec 64)) :
    ((ps.zipIdx n).foldl (fun s pi ↦ writeLanes s pi.2 (pendingWords pi.1)) s).length =
      s.length := by
  induction ps generalizing n s with
  | nil => rfl
  | cons p ps ih => rw [List.zipIdx_cons, List.foldl_cons, ih, x_length_writeLanes]

private theorem x_length_duplexLanes (r : SpongeRust) : (duplexLanes r).length = r.state.length := by
  rw [duplexLanes, x_length_writes, x_length_fillRate]

theorem duplexLanes_length (r : SpongeRust) : (duplexLanes r).length = r.state.length :=
  x_length_duplexLanes r

/-- **Lane `j` of `Sponge::duplex`'s input**: the waiting scalars' lanes, then zeros up to the rate, then the
    state's capacity. -/
theorem duplexLanes_getD (r : SpongeRust) (h : r.Inv) (j : ℕ) :
    (duplexLanes r).getD j 0 =
      if j < 4 * r.nPending then
        (pendingWords ((r.pending.take r.nPending).getD (j / 4) (0, 0#64))).getD (j % 4) 0
      else if j < 16 then 0 else r.state.getD j 0 := by
  obtain ⟨hs, hp, hn⟩ := h
  have htake : (r.pending.take r.nPending).length = r.nPending := by simp [hp]; omega
  rw [duplexLanes, x_getD_writes _ 0 _ (by rw [x_length_fillRate, hs]) (by omega), x_getD_fillRate, htake]
  simp only [Nat.mul_zero, Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero]
  by_cases h1 : j < 4 * r.nPending
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : j < 16
    · by_cases h3 : j < r.state.length
      · simp [h2, h3]
      · simp [h2, h3]
    · simp [h2]

end Rv64mc.Model
