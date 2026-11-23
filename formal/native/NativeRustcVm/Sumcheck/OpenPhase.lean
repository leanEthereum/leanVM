module

public import NativeVm.Model.Transcript

/-!
# `open_phase` as `transcript.rs` checks it

The model's `openPhase root height width positions phase` asks every opening for `width` leaf
words and `height` siblings, the leaf indices to be the positions, and every path to climb to the
root. The decoded proof gives all of a phase's openings one width `w` and one height `h`, so the
Rust checks the shape once (`count == 0 || (w == width && h == height)`), the count against the
positions', then the positions one by one, then the climbs one by one (`openPhase_eq`).
-/

namespace NativeRustcVm.Sumcheck

open NativeVm.Model LeanVM.Protocol

@[expose] public section

/-- The positions check: opening `j`'s leaf index is position `j`, for every `j < n`. -/
def PositionsOk (ph : Array OpeningW) (positions : Array UInt64) (n : Nat) : Prop :=
  ∀ j (h₁ : j < ph.size) (h₂ : j < positions.size), j < n → ph[j].leafIndex = positions[j]

/-- The climbs check: opening `j`'s path climbs from its hashed leaf to `root`, for every
`j < n`. -/
def ClimbsOk (root : Digest) (ph : Array OpeningW) (n : Nat) : Prop :=
  ∀ j (h : j < ph.size), j < n → climb (hashWords ph[j].leaf) ph[j].leafIndex ph[j].path = root

instance (ph : Array OpeningW) (positions : Array UInt64) (n : Nat) :
    Decidable (PositionsOk ph positions n) := by
  unfold PositionsOk; infer_instance

instance (root : Digest) (ph : Array OpeningW) (n : Nat) : Decidable (ClimbsOk root ph n) := by
  unfold ClimbsOk; infer_instance

/-- **`openPhase` as the Rust checks it**, for a phase whose openings all have `w` leaf words and
`h` siblings. -/
theorem openPhase_eq {root : Digest} {height width : Nat} {positions : Array UInt64}
    {ph : Array OpeningW} {h w : Nat}
    (hshape : ∀ j (hj : j < ph.size), ph[j].leaf.size = w ∧ ph[j].path.size = h) :
    openPhase root height width positions ph =
      if (ph.size = 0 ∨ (w = width ∧ h = height)) ∧ ph.size = positions.size ∧
          PositionsOk ph positions ph.size then
        if ClimbsOk root ph ph.size then some (ph.map (·.leaf)) else none
      else none := by
  have hall : (ph.all fun o ↦ o.leaf.size == width && o.path.size == height) = true ↔
      (ph.size = 0 ∨ (w = width ∧ h = height)) := by
    rw [Array.all_eq_true]
    constructor
    · intro H
      by_cases h0 : ph.size = 0
      · exact Or.inl h0
      · have := H 0 (by omega)
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        obtain ⟨h1, h2⟩ := hshape 0 (by omega)
        exact Or.inr ⟨h1 ▸ this.1, h2 ▸ this.2⟩
    · rintro (H | ⟨rfl, rfl⟩) i hi
      · omega
      · simp [hshape i hi]
  have hmap : (ph.map (·.leafIndex) == positions) = true ↔
      ph.size = positions.size ∧ PositionsOk ph positions ph.size := by
    rw [beq_iff_eq, Array.ext_iff]
    simp only [Array.size_map, Array.getElem_map, PositionsOk]
    constructor
    · rintro ⟨hs, H⟩
      exact ⟨hs, fun j h₁ h₂ _ ↦ H j h₁ h₂⟩
    · rintro ⟨hs, H⟩
      exact ⟨hs, fun j h₁ h₂ ↦ H j h₁ h₂ h₁⟩
  have hclimb : (ph.all fun o ↦ climb (hashWords o.leaf) o.leafIndex o.path == root) = true ↔
      ClimbsOk root ph ph.size := by
    rw [Array.all_eq_true]
    simp only [beq_iff_eq, ClimbsOk]
    exact ⟨fun H j h _ ↦ H j h, fun H j h ↦ H j h h⟩
  unfold openPhase
  by_cases h1 : (ph.size = 0 ∨ (w = width ∧ h = height)) ∧ ph.size = positions.size ∧
      PositionsOk ph positions ph.size
  · have : ((ph.all fun o ↦ o.leaf.size == width && o.path.size == height) &&
        ph.map (·.leafIndex) == positions) = true := by
      rw [Bool.and_eq_true, hall, hmap]; exact ⟨h1.1, h1.2⟩
    rw [ite_eq_left (this), ite_eq_left (h1)]
    by_cases h2 : ClimbsOk root ph ph.size
    · rw [ite_eq_left ((hclimb.mpr h2)), ite_eq_left (h2)]
    · rw [ite_eq_right ((fun h ↦ h2 (hclimb.mp h))), ite_eq_right (h2)]
  · have : ¬ ((ph.all fun o ↦ o.leaf.size == width && o.path.size == height) &&
        ph.map (·.leafIndex) == positions) = true := by
      rw [Bool.and_eq_true, hall, hmap]; exact fun h ↦ h1 ⟨h.1, h.2⟩
    rw [ite_eq_right (this), ite_eq_right (h1)]

/-- The positions check one more. -/
theorem positionsOk_succ {ph : Array OpeningW} {positions : Array UInt64} {n : Nat}
    (hn₁ : n < ph.size) (hn₂ : n < positions.size) :
    PositionsOk ph positions (n + 1) ↔
      PositionsOk ph positions n ∧ ph[n].leafIndex = positions[n] := by
  constructor
  · intro H
    exact ⟨fun j h₁ h₂ hj ↦ H j h₁ h₂ (by omega), H n hn₁ hn₂ (by omega)⟩
  · rintro ⟨H, hn⟩ j h₁ h₂ hj
    by_cases hjn : j = n
    · subst hjn; exact hn
    · exact H j h₁ h₂ (by omega)

/-- The climbs check one more. -/
theorem climbsOk_succ {root : Digest} {ph : Array OpeningW} {n : Nat} (hn : n < ph.size) :
    ClimbsOk root ph (n + 1) ↔
      ClimbsOk root ph n ∧ climb (hashWords ph[n].leaf) ph[n].leafIndex ph[n].path = root := by
  constructor
  · intro H
    exact ⟨fun j h hj ↦ H j h (by omega), H n hn (by omega)⟩
  · rintro ⟨H, hn'⟩ j h hj
    by_cases hjn : j = n
    · subst hjn; exact hn'
    · exact H j h (by omega)

theorem positionsOk_zero (ph : Array OpeningW) (positions : Array UInt64) :
    PositionsOk ph positions 0 := fun _ _ _ h ↦ absurd h (Nat.not_lt_zero _)

theorem climbsOk_zero (root : Digest) (ph : Array OpeningW) : ClimbsOk root ph 0 :=
  fun _ _ h ↦ absurd h (Nat.not_lt_zero _)

end

end NativeRustcVm.Sumcheck
