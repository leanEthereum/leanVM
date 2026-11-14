/-
  LeanVM.Guest.Memory.GuestHints

  Every function of the guest's core IR passes the heap hint check (`hintsAll`): the functions
  other than `main` and the three loop helpers writing into its buffers form a closed set passing
  it.
-/

module

public import LeanVM.Guest.Memory.GuestHints.Part0
public import LeanVM.Guest.Memory.GuestHints.Part1
public import LeanVM.Guest.Memory.GuestHints.Part2
public import LeanVM.Guest.Memory.GuestHints.Part3
public import LeanVM.Guest.Memory.GuestHints.Part4
public import LeanVM.Guest.Memory.GuestHints.Part5
public import LeanVM.Guest.Memory.GuestHints.Part6
public import LeanVM.Guest.Memory.HintsLocal

/-!
# The guest's heap hints

`hintsAll`: the ranges of `GuestHints/Part*` join into the whole core IR. `chkH_find`: a function
found by name passes `chkH`. `coreProgram_hintsClosed`: the functions other than `main` and
`hintsX` pass the check and call only each other.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- **Every function of the guest passes the heap hint check.** -/
theorem hintsAll : RangeOk chkH 0 coreProgram.length := by
  have h := (((((hintsRange_0.append (m := 264) hintsRange_36).append (m := 47) hintsRange_300).append
    (m := 213) hintsRange_347).append (m := 520) hintsRange_560).append (m := 260) hintsRange_1080).append
    (m := 261) hintsRange_1340
  rw [coreProgram_length]; exact h

/-- A function found by name passes the check. -/
theorem chkH_find {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn) :
    fn.name = f ∧ chkH 0 fn = true := by
  have hn : fn.name = f := by simpa using List.find?_some hf
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hf)
  exact ⟨hn, by simpa [chkH] using hintsAll.all hj⟩

/-- The functions but `main` and the loop helpers writing into its buffers. -/
def HintsS (g : String) : Prop := g ∉ hintsX ∧ g ≠ "main"

theorem not_mem_hintsX {c : String} (h : (!hintsX.contains c) = true) : c ∉ hintsX := fun hm => by
  rw [List.contains_iff_mem.mpr hm] at h; exact absurd h Bool.false_ne_true

/-- What the check says of a function's callees. -/
theorem chkH_callees {fn : Fn} (hc : chkH 0 fn = true) : ∀ c ∈ Stmt.blockCallees fn.body,
    c ≠ "main" ∧ (fn.name = "main" ∨ c = fn.name ∨ c ∉ hintsX) := by
  have hcs : ∀ c ∈ Stmt.blockCallees fn.body, calleeOk fn c = true := by
    unfold chkH at hc
    split at hc
    · exact calleesR_sound _ hc
    · simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
      rcases hc with hc | hc
      · exact (quickR_sound _ hc).2
      · exact calleesR_sound _ hc.2
  intro c hc'
  have h := hcs c hc'
  simp only [calleeOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  exact ⟨h.1, h.2.elim (fun h => h.imp id Or.inl) fun h => Or.inr (Or.inr (not_mem_hintsX h))⟩

theorem chkH_body {fn : Fn} (hc : chkH 0 fn = true) (hx : fn.name ∉ hintsX) : hintsOkL [] fn.body = true := by
  have hx' : hintsX.contains fn.name = false := by
    cases h : hintsX.contains fn.name
    · rfl
    · exact absurd (List.contains_iff_mem.mp h) hx
  unfold chkH at hc
  simp only [hx', Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at hc
  rcases hc with hc | hc
  · exact (quickR_sound _ hc).1 []
  · exact hc.1

/-- **The functions but `main` and `hintsX` pass the check and call only each other.** -/
theorem coreProgram_hintsClosed : HintsClosed coreProgram HintsS := by
  rintro g ⟨hx, hm⟩ fn hf
  obtain ⟨hn, hc⟩ := chkH_find hf
  subst hn
  refine ⟨chkH_body hc hx, fun c hc' => ?_⟩
  obtain ⟨hcm, h | h | h⟩ := chkH_callees hc c hc'
  · exact absurd h hm
  · subst h; exact ⟨hx, hm⟩
  · exact ⟨h, hcm⟩

/-- **A loop helper writing into `main`'s buffers calls only itself and the closed set.** -/
theorem hintsX_callees {f : String} (hfx : f ∈ hintsX) {fn : Fn} (hf : coreProgram.find? f = some fn) :
    ∀ c ∈ Stmt.blockCallees fn.body, c = f ∨ HintsS c := by
  obtain ⟨hn, hc⟩ := chkH_find hf
  have hm : f ≠ "main" := by
    simp only [hintsX, List.mem_cons, List.not_mem_nil, or_false] at hfx
    rcases hfx with rfl | rfl | rfl <;> decide
  subst hn
  intro c hc'
  obtain ⟨hcm, h | h | h⟩ := chkH_callees hc c hc'
  · exact absurd h hm
  · exact Or.inl h
  · exact Or.inr ⟨h, hcm⟩

/-- **`main`'s callees**: the closed set, or the loop helpers writing into its buffers. -/
theorem main_callees {fn : Fn} (hf : coreProgram.find? "main" = some fn) :
    ∀ c ∈ Stmt.blockCallees fn.body, c ∈ hintsX ∨ HintsS c := by
  obtain ⟨-, hc⟩ := chkH_find hf
  intro c hc'
  by_cases hx : c ∈ hintsX
  · exact Or.inl hx
  · exact Or.inr ⟨hx, (chkH_callees hc c hc').1⟩

/-- **`main` passes the check.** -/
theorem main_hintsOk {fn : Fn} (hf : coreProgram.find? "main" = some fn) : hintsOkL [] fn.body = true := by
  obtain ⟨hn, hc⟩ := chkH_find hf
  exact chkH_body hc (by rw [hn]; decide)

end
end LeanVM.Guest.Memory
