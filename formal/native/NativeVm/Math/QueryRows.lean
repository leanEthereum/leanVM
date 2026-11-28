module

public import NativeVm.Model.Transcript

/-!
# An opened phase's rows
-/

@[expose] public section

namespace NativeVm.Math

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol

/-- An opened phase's rows: its leaves, one per position, each `width` words. -/
theorem openPhase_some {root : Digest} {height width : Nat} {ps : Array UInt64}
    {ph : Array OpeningW} {rows : Array (Array UInt64)}
    (h : Model.openPhase root height width ps ph = some rows) :
    rows = ph.map (·.leaf) ∧ rows.size = ps.size ∧ ∀ j (hj : j < rows.size), rows[j].size = width := by
  unfold Model.openPhase at h
  split at h
  · rename_i hshape
    split at h
    · obtain rfl := Option.some.inj h
      rw [Bool.and_eq_true] at hshape
      obtain ⟨hall, hmap⟩ := hshape
      refine ⟨rfl, ?_, fun j hj ↦ ?_⟩
      · have := congrArg Array.size (beq_iff_eq.mp hmap)
        simpa using this
      · have := Array.all_eq_true.mp hall j (by simpa using hj)
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        simpa using this.1
    · cases h
  · cases h

end NativeVm.Math
