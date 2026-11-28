module

public import LeanVM.Guest.Coverage
public import Statement.LeanVmGuestProver

/-!
# The two coverage plans agree

`Statement/LeanVmGuestProver.lean`'s `Prover.coveragePlan` (what `honestPushes` lays out) and
`Coverage.coveragePlan` (what `B1/Main/Plan.lean` reasons about) are the same definition, written
twice: `coveragePlan_eq` gives their three fields equal.
-/

namespace LeanVM.Guest.Complete

@[expose] public section

variable {α : Type} [BEq α] (D : List α)

theorem takeSlot_eq (st : List Bool × List α) (c : α) : Prover.takeSlot D st c = Coverage.takeSlot D st c := by
  unfold Prover.takeSlot Coverage.takeSlot
  split <;> rename_i h <;> simp only [h]

theorem takeSlots_eq : ∀ (st : List Bool × List α) (cs : List α),
    Prover.takeSlots D st cs = Coverage.takeSlots D st cs
  | st, [] => by simp [Prover.takeSlots, Coverage.takeSlots]
  | st, c :: cs => by
    rw [Prover.takeSlots, Coverage.takeSlots, takeSlot_eq]
    generalize Coverage.takeSlot D st c = p
    obtain ⟨j, st'⟩ := p
    dsimp only
    rw [takeSlots_eq st' cs]

theorem takeSlotsAll_eq : ∀ (st : List Bool × List α) (cs : List (List α)),
    Prover.takeSlotsAll D st cs = Coverage.takeSlotsAll D st cs
  | st, [] => by simp [Prover.takeSlotsAll, Coverage.takeSlotsAll]
  | st, c :: cs => by
    rw [Prover.takeSlotsAll, Coverage.takeSlotsAll, takeSlots_eq]
    generalize Coverage.takeSlots D st c = p
    obtain ⟨j, st'⟩ := p
    dsimp only
    rw [takeSlotsAll_eq st' cs]

/-- **The two coverage plans agree**, field by field. -/
theorem coveragePlan_eq (R : List α) (Cs : List (List α)) :
    (Prover.coveragePlan D R Cs).duplicates = (Coverage.coveragePlan D R Cs).duplicates ∧
      (Prover.coveragePlan D R Cs).directSlots = (Coverage.coveragePlan D R Cs).directSlots ∧
      (Prover.coveragePlan D R Cs).childSlots = (Coverage.coveragePlan D R Cs).childSlots := by
  unfold Prover.coveragePlan Coverage.coveragePlan
  rw [takeSlots_eq]
  generalize Coverage.takeSlots D (D.map fun _ => false, []) R = p
  obtain ⟨raw, st⟩ := p
  dsimp only
  rw [takeSlotsAll_eq]
  generalize Coverage.takeSlotsAll D st Cs = q
  obtain ⟨ch, st'⟩ := q
  exact ⟨rfl, rfl, rfl⟩

end
end LeanVM.Guest.Complete
