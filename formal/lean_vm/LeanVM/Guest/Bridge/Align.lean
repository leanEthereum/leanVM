/-
  LeanVM.Guest.Bridge.Align

  What the alignment check gives: a function passing it is at its body at offset `0`, the start the tree track against the run needs.
-/

module

public import LeanVM.Guest.Bridge.AlignDefs

/-!
# The alignment check's facts

`alignAt_zero`: on a function passing `alignOk`, the body position at offset `0` is the body, so `refOk_init` applies with the alignment `alignAt` (by name). `posOf_nil`: a cursor at the top level names the body's rest.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest.Core

public section

theorem posOf_nil (body : List Stmt) (k : ℕ) : posOf body [] k = body.drop k := rfl

/-- **Offset `0` is the body.** -/
theorem alignAt_zero {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (h : alignOk X body code d = true) :
    alignAt X body code d 0 = some body := by
  simp only [alignOk, Bool.and_eq_true] at h
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp h.2
  have key : ∃ l', l = (0, ([], 0)) :: l' := by
    cases code with
    | nil => simp [alignRun, alignGo] at hl
    | cons ins code =>
      simp only [alignRun, alignGo, List.filter_nil, List.all_nil, Bool.cond_true] at hl
      split at hl
      · obtain ⟨l', -, h2⟩ := Option.map_eq_some_iff.mp hl
        exact ⟨l', h2.symm⟩
      · cases hl
  obtain ⟨l', rfl⟩ := key
  simp [alignAt, hl, posOf_nil]

end

end LeanVM.Guest.Bridge
