/-
  LeanVM.Guest.B1.KeccakGkr.VkOpen

  `verify_keccak`'s openings' lane weights (`keccak_slot_lanes`, G:3064-3078) and dot products.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkFirst

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

variable {C : CallRel} {rd : Reader} {σ : Val}

/-- **A dot product of values with loaded words.** -/
theorem dotLoadsT_holds {xs : List ℕ} {p : V} {off b : ℕ} {P : ℕ → E}
    (hP : ∀ k < xs.length, ∀ v, LoadHolds rd (σ p) (off + k) v → v = P k)
    (h2 : 2 ≤ xs.length) {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (dotLoadsT xs p off b) next kret) :
    σ (.n (dotLoadsV b xs.length)) = ∑ k ∈ range xs.length, σ (.n (xs.getD k 0)) * P k ∧ next := by
  rw [dotLoadsT, holdsList_range_flatten _ _ (fun k ↦ by split <;> rfl)] at h
  obtain ⟨hall, hn⟩ := h
  have acc : ∀ k, 1 ≤ k → k < xs.length →
      σ (.n (b + 3 * k + 1)) = ∑ j ∈ range (k + 1), σ (.n (xs.getD j 0)) * P j := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro _ hk
      have hb := hall (k + 1) hk
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
        and_true] at hb
      obtain ⟨l1, m, a⟩ := hb
      rw [a, m, hP (k + 1) hk _ l1, Finset.sum_range_succ _ (k + 1)]
      congr 1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have h0 := hall 0 (by omega)
        simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at h0
        obtain ⟨l1', m'⟩ := h0
        simp only [↓reduceIte, zero_add, Finset.sum_range_one]
        have e0 := hP 0 (by omega) _ (by simpa using l1')
        rw [m', e0]
      · simp only [show ¬ (k + 1 = 1) by omega, ↓reduceIte]
        rw [show b + 3 * (k + 1) - 2 = b + 3 * k + 1 by omega]
        exact ih (by omega) (by omega)
  refine ⟨?_, hn⟩
  simp only [dotLoadsV, show ¬ (xs.length = 1) by omega, ↓reduceIte]
  rw [show b + 3 * (xs.length - 1) + 1 = b + 3 * (xs.length - 1) + 1 from rfl,
    acc (xs.length - 1) (by omega) (by omega),
    show xs.length - 1 + 1 = xs.length by omega]

/-- **An opening's lane weights** (`keccak_slot_lanes`): the slot point's six words at `slot`,
the segment coordinate at `segp`, and per lane the segments' slot weights. -/
theorem slotLanesT_holds {slot segp b first count : ℕ} (hc : count = 1 ∨ count = 2)
    (hfc : first + count ≤ 2)
    {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsList C rd σ (slotLanesT slot segp b first count) next kret) :
    ∃ rs : List E, rs.length = 6 ∧ (∀ t (ht : t < rs.length), LoadHolds rd (σ (.n slot)) t rs[t]) ∧
      ∃ r : E, LoadHolds rd (σ (.n segp)) 0 r ∧
      (∀ lane < 25, σ (.n (slotLaneV b count lane)) =
        ∑ m ∈ range count, eqAt [r] m * eqAt rs (25 * (first + m) + lane)) ∧ next := by
  rw [slotLanesT, holdsList_append, holdsList_append] at h
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, h⟩ := eqfT_holds (by omega) (by omega) (by decide) (by decide) h
  obtain ⟨⟨lr, hseg⟩, h⟩ := eqfLevel0T_holds h
  rw [holdsList_range_flatten _ _ (fun k ↦ by split <;> rfl)] at h
  obtain ⟨hall, hn⟩ := h
  refine ⟨rs, hrsL, fun t ht ↦ by simpa using hrs t ht, σ (.n (b + 129)), lr, fun lane hl ↦ ?_, hn⟩
  have hw : ∀ m < 2, σ (.n (b + 129 + 2 + m)) = eqAt [σ (.n (b + 129))] m := hseg
  rcases hc with rfl | rfl
  · have hb := hall lane hl
    simp only [↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨e1, e2⟩ := hb
    simp only [slotLaneV, ↓reduceIte, Finset.sum_range_one, Nat.add_zero]
    rw [e2, e1, show b + 131 = b + 129 + 2 + 0 by omega, hw 0 (by omega),
      hent _ (by omega)]
  · have hb := hall lane hl
    simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds,
      and_true] at hb
    obtain ⟨e1, e2, e3, e4⟩ := hb
    simp only [slotLaneV, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.add_zero]
    rw [e4, e3, e1, e2, show b + 131 = b + 129 + 2 + 0 by omega,
      show b + 132 = b + 129 + 2 + 1 by omega, hw 0 (by omega), hw 1 (by omega),
      hent _ (by omega), hent _ (by omega)]

end
end LeanVM.Guest.B1.VerifySub
