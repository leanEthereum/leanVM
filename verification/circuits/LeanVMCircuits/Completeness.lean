module

public import LeanVMCircuits.Export

@[expose] public section

namespace LeanVMCircuits.Flock

/-- All variable references precede the product they help generate. -/
def Affine.bounded (affine : Affine) (limit : ℕ) : Bool :=
  match affine with
  | .zero | .one => true
  | .var index => decide (index < limit)
  | .xor left right => left.bounded limit && right.bounded limit

def AgreeBelow (limit : ℕ) (before after : ℕ → Bit) : Prop :=
  ∀ index, index < limit → after index = before index

theorem Affine.eval_agree (affine : Affine) (limit : ℕ) (before after : ℕ → Bit)
    (hbound : affine.bounded limit = true) (hagree : AgreeBelow limit before after) :
    affine.eval after = affine.eval before := by
  induction affine with
  | zero => rfl
  | one => rfl
  | var index => exact hagree index (by simpa [Affine.bounded] using hbound)
  | xor left right ihLeft ihRight =>
    simp only [Affine.bounded, Bool.and_eq_true] at hbound
    exact congrArg₂ (· + ·) (ihLeft hbound.1) (ihRight hbound.2)

def wellFormed (next : ℕ) : List Row → Bool
  | [] => true
  | row :: rest => row.output == next && row.left.bounded next && row.right.bounded next &&
      wellFormed (next + 1) rest

/-- Every input assignment extends to a satisfying assignment, not just a conditional witness premise. -/
theorem witness_exists (rows : List Row) (next : ℕ) (assignment : ℕ → Bit)
    (hwell : wellFormed next rows = true) :
    ∃ final, AgreeBelow next assignment final ∧ rows.Forall (Row.Holds final) := by
  induction rows generalizing next assignment with
  | nil => exact ⟨assignment, fun _ _ => rfl, by simp⟩
  | cons row rest ih =>
    simp only [wellFormed, Bool.and_eq_true, Nat.beq_eq_true_eq] at hwell
    rcases hwell with ⟨⟨⟨houtput, hleft⟩, hright⟩, hrest⟩
    let updated := Function.update assignment next (row.left.eval assignment * row.right.eval assignment)
    obtain ⟨final, hagree, htail⟩ := ih (next + 1) updated hrest
    have htotal : AgreeBelow next assignment final := by
      intro index hindex
      rw [hagree index (by omega)]
      exact Function.update_of_ne (by omega) _ _
    refine ⟨final, htotal, ?_⟩
    simp only [List.forall_cons]
    refine ⟨?_, htail⟩
    change final row.output = row.left.eval final * row.right.eval final
    rw [Affine.eval_agree row.left next assignment final hleft htotal,
      Affine.eval_agree row.right next assignment final hright htotal, houtput,
      hagree next (by omega)]
    simp [updated]

theorem adder64_wellFormed : wellFormed 128 adder64.rows = true := by decide +kernel

theorem adder64_complete (inputs : ℕ → Bit) :
    ∃ assignment, AgreeBelow 128 inputs assignment ∧ adder64.rows.Forall (Row.Holds assignment) :=
  witness_exists adder64.rows 128 inputs adder64_wellFormed

end LeanVMCircuits.Flock
