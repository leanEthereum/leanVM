/-
  LeanVM.Guest.B2C.Cells

  The frames' cells `C`: one candidate per cell, within the frame, so they fit and agree for any
  instances; and what a core function's name gives by index.
-/

module

public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.CheckSound

/-!
# The frames' cells

`C I` keeps one candidate per cell (`frameE`, by `dedupC`): the first, within the frame. So its
cells fit and agree for any instances (`cellsOk_C`). `fn_of_idx`: a function's index gives its
core function, frame size and cells.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## One candidate per cell -/

section Dedup

theorem mem_dedupC : ∀ {L : List (ℕ × E)} {q : ℕ × E}, q ∈ dedupC L → q ∈ L
  | [], _, h => by simp [dedupC] at h
  | x :: L, q, h => by
    simp only [dedupC, List.mem_cons, List.mem_filter] at h
    rcases h with rfl | ⟨h, -⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_dedupC h)

theorem dedupC_key : ∀ {L : List (ℕ × E)} {q q' : ℕ × E}, q ∈ dedupC L → q' ∈ dedupC L →
    q.1 = q'.1 → q = q'
  | [], _, _, h, _, _ => by simp [dedupC] at h
  | x :: L, q, q', h, h', he => by
    simp only [dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] at h h'
    rcases h with rfl | ⟨h, hx⟩ <;> rcases h' with rfl | ⟨h', hx'⟩
    · rfl
    · exact absurd he.symm hx'
    · exact absurd he hx
    · exact dedupC_key h h' he

/-- The candidate kept at a cell is the first at that cell. -/
theorem dedupC_first : ∀ {L1 L2 : List (ℕ × E)} {q : ℕ × E}, q ∈ dedupC (L1 ++ L2) →
    (∃ x ∈ L1, x.1 = q.1) → q ∈ L1
  | [], _, _, _, ⟨_, h, _⟩ => by simp at h
  | x :: L1, L2, q, h, ⟨y, hy, he⟩ => by
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at h
    rcases h with rfl | ⟨h, hx⟩
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact absurd he.symm hx
      · exact List.mem_cons_of_mem _ (dedupC_first h ⟨y, hy, he⟩)

/-- A candidate before which every candidate at its cell is itself is kept. -/
theorem dedupC_mem : ∀ {L1 L2 : List (ℕ × E)} {q : ℕ × E}, q ∈ L1 → (∀ x ∈ L1, x.1 = q.1 → x = q) →
    q ∈ dedupC (L1 ++ L2)
  | [], _, _, h, _ => by simp at h
  | x :: L1, L2, q, h, hx => by
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq]
    by_cases hxq : x = q
    · exact Or.inl hxq.symm
    · right
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hxq
      · refine ⟨dedupC_mem h fun y hy ↦ hx y (List.mem_cons_of_mem _ hy), fun he ↦ hxq ?_⟩
        exact hx x List.mem_cons_self he.symm

/-- Candidates with the same cells first keep the same candidates at the other cells. -/
theorem dedupC_swap : ∀ {A A' R : List (ℕ × E)} {q : ℕ × E}, A.map Prod.fst = A'.map Prod.fst →
    q ∈ dedupC (A' ++ R) → q.1 ∉ A'.map Prod.fst → q ∈ dedupC (A ++ R)
  | [], [], _, _, _, h, _ => h
  | [], _ :: _, _, _, he, _, _ => by simp at he
  | _ :: _, [], _, _, he, _, _ => by simp at he
  | a :: A, a' :: A', R, q, he, h, hn => by
    simp only [List.map_cons, List.cons.injEq] at he
    simp only [List.cons_append, dedupC, List.mem_cons, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at h ⊢
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rcases h with rfl | ⟨h, hx⟩
    · exact absurd rfl hn.1
    · exact Or.inr ⟨dedupC_swap he.2 h hn.2, by rw [he.1]; exact hx⟩

theorem frameE_append (n : ℕ) (L1 L2 : List (ℕ × E)) :
    frameE n (L1 ++ L2) = dedupC ((L1.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n) ++
      (L2.filter fun q ↦ Nat.ble 2 q.1 && Nat.blt q.1 n)) := by
  rw [frameE, List.filter_append]

theorem mem_frameE {n : ℕ} {L : List (ℕ × E)} {q : ℕ × E} (h : q ∈ frameE n L) :
    q ∈ L ∧ 2 ≤ q.1 ∧ q.1 < n := by
  have := mem_dedupC h
  simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at this
  exact ⟨this.1, this.2⟩

end Dedup

/-! ## Functions by name -/

section Lookup

theorem indexOf?_spec {f : String} {i : ℕ} (h : coreProgram.indexOf? f = some i) :
    ∃ hi : i < coreProgram.length, coreProgram[i].name = f := by
  unfold Program.indexOf? at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, he, -⟩ := h
  exact ⟨hi, by simpa using he⟩

theorem find?_none {f : String} (h : coreProgram.indexOf? f = none) : coreProgram.find? f = none := by
  unfold Program.indexOf? at h
  unfold Program.find?
  rw [List.findIdx?_eq_none_iff] at h
  rw [List.find?_eq_none]
  exact fun x hx ↦ by simpa using h x hx

/-- The values' cells in compiled function `j`, the certificate's. -/
noncomputable def cellJ (j : ℕ) (v : V) : ℕ := (certOf j).locs.getD v.idx 0

/-- What the name of core function `i` gives: its compiled function `i + 1`, its frame size, its
cells. -/
theorem fn_of_idx {f : String} {j : ℕ} (h : idxOf f = some j) :
    ∃ i, j = i + 1 ∧ ∃ hi : i < coreProgram.length, coreProgram[i].name = f ∧
      coreProgram.find? f = some coreProgram[i] ∧ coreOf j = coreProgram[i] ∧ fs f = fsN j ∧
      (∀ v, cert f v = (certOf j).locs.getD v.idx 0) ∧ 1 ≤ j ∧ j < nFns := by
  unfold idxOf at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hn⟩ := indexOf?_spec hi
  refine ⟨i, rfl, hlt, hn, by rw [← hn]; exact coreProgram_find_getElem hlt, ?_, ?_, fun v ↦ ?_,
    by omega, by have : coreProgram.length + 1 = nFns := (by rw [coreProgram_length]; rfl); omega⟩
  · unfold coreOf; simp only [Nat.add_sub_cancel]; exact nth_eq hlt
  · unfold fs fsN
    rw [hi]
    cases i with
    | zero => rfl
    | succ i => simp
  · unfold cert idxOf; rw [hi]; rfl

end Lookup

/-! ## The frames' cells -/

section Cells

theorem two_le_fs (f : String) : 2 ≤ fs f := by
  unfold fs
  split
  · decide
  · omega
  · exact le_rfl

theorem C_node {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {j : ℕ}
    (ht : I.t = .node f σ bufs kids) (hj : idxOf f = some j) : C I = frameE (fs f) (nodeE j f σ I) := by
  unfold C
  rw [ht]
  simp only [Tree.name, hj]

theorem C_phantom {I : Inst} {f : String} {σ : Val} {j : ℕ} (ht : I.t = .phantom f σ)
    (hj : idxOf f = some j) : C I = frameE (fs f) (phantomE j f σ I) := by
  unfold C
  rw [ht]
  simp only [Tree.name, hj]

/-- Every frame's cells are some list's candidates, in the frame. -/
theorem C_shape (I : Inst) : ∃ L, C I = frameE (fs I.t.name) L ∨ C I = [] := by
  unfold C
  cases ht : I.t with
  | node f σ bufs kids =>
    cases hj : idxOf f with
    | none => exact ⟨[], Or.inr (by simp [Tree.name, hj])⟩
    | some j => exact ⟨nodeE j f σ I, Or.inl (by simp [Tree.name, hj])⟩
  | phantom f σ =>
    cases hj : idxOf f with
    | none => exact ⟨[], Or.inr (by simp [Tree.name, hj])⟩
    | some j => exact ⟨phantomE j f σ I, Or.inl (by simp [Tree.name, hj])⟩

/-- **The cells fit their frames and agree**, for any instances. -/
theorem cellsOk_C (Is : List Inst) : CellsOk fs C Is where
  two_le I _ := two_le_fs I.t.name
  off I _ q hq := by
    obtain ⟨L, h | h⟩ := C_shape I <;> rw [h] at hq
    · exact (mem_frameE hq).2
    · cases hq
  agree I _ q hq q' hq' he := by
    obtain ⟨L, h | h⟩ := C_shape I <;> rw [h] at hq hq'
    · rw [dedupC_key hq hq' he]
    · cases hq

end Cells

end
end LeanVM.Guest.B2C
