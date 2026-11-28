/-
  LeanVM.Guest.Bridge.AllocIdx

  Where a hint at an offset sits among a function's hints: the hints before its offset, its own
  offset's, and after; its index among the buffer hints, and what `bufsFirst` says around it.
-/

module

public import LeanVM.Guest.Bridge.AllocCur

/-!
# A hint among the function's hints

For a function's advice `d` with pcs increasing from its entry (`HintsUp`), the hints of offset
`off`, `hs`, split the function's hints (`hintsOff_split`): those before (offsets below `off`), `hs`
at `off`, those after (offsets above). So the `i`-th of `hs`, a buffer hint, is the buffer hint of
index `nbAt off` plus the buffer hints before it in `hs` (`bufsOf_idx`). Restored in part from the tag.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

public section

variable {X : AlignCtx} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}

theorem lookup_key {β : Type} : ∀ {l : List (ℕ × β)} {k : ℕ} {v : β}, l.lookup k = some v → ∃ q ∈ l, q.1 = k
  | [], _, _, h => by simp at h
  | ⟨a, b⟩ :: l, k, v, h => by
    rw [List.lookup_cons] at h
    by_cases he : k = a
    · exact ⟨⟨a, b⟩, List.mem_cons_self, he.symm⟩
    · rw [show (k == a) = false by simp [he]] at h
      obtain ⟨q, hq, hq'⟩ := lookup_key h
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

theorem split_aux (entry off : ℕ) {hs : List Prover.Exec.Hint} :
    ∀ (l : List (ℕ × List Prover.Exec.Hint)), pcsUp l = true → (∀ q ∈ l, entry ≤ q.1) →
      l.lookup (entry + off) = some hs →
      ∃ P S : List (ℕ × Prover.Exec.Hint), (l.flatMap fun q ↦ q.2.map fun h ↦ (q.1 - entry, h)) = P ++ hs.map (fun h ↦ (off, h)) ++ S ∧
        (∀ q ∈ P, q.1 < off) ∧ ∀ q ∈ S, off < q.1
  | [], _, _, hl => by simp at hl
  | ⟨a1, a2⟩ :: l, hu, hge, hl => by
    have ha := hge _ List.mem_cons_self
    simp only at ha
    rw [List.lookup_cons] at hl
    have hlt : ∀ q ∈ l, a1 < q.1 := pcsUp_lt hu
    by_cases he : entry + off = a1
    · rw [show (entry + off == a1) = true by simp [he]] at hl
      obtain rfl := Option.some.inj hl
      refine ⟨[], l.flatMap fun q ↦ q.2.map fun h ↦ (q.1 - entry, h), ?_, by simp, fun q hq ↦ ?_⟩
      · rw [List.flatMap_cons]
        simp [show a1 - entry = off by omega]
      · obtain ⟨q', hq', hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨h, -, rfl⟩ := List.mem_map.mp hq
        have := hlt q' hq'
        simp only
        omega
    · rw [show (entry + off == a1) = false by simp; omega] at hl
      obtain ⟨P, S, he', hP, hS⟩ := split_aux entry off l (pcsUp_tail hu)
        (fun q hq ↦ hge q (List.mem_cons_of_mem _ hq)) hl
      obtain ⟨q0, hq0, hq0e⟩ := lookup_key hl
      have := hlt q0 hq0
      refine ⟨a2.map (fun h ↦ (a1 - entry, h)) ++ P, S, ?_, fun q hq ↦ ?_, hS⟩
      · rw [List.flatMap_cons, he']; simp
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨h, -, rfl⟩ := List.mem_map.mp hq
          simp only
          omega
        · exact hP q hq

/-- **A function's hints split at an offset**: those before it, its own, those after. -/
theorem hintsOff_split {entry off : ℕ} (hU : HintsUp d entry) {hs : List Prover.Exec.Hint}
    (hl : d.2.2.lookup (entry + off) = some hs) :
    ∃ P S : List (ℕ × Prover.Exec.Hint), hintsOff d = P ++ hs.map (fun h ↦ (off, h)) ++ S ∧ (∀ q ∈ P, q.1 < off) ∧ ∀ q ∈ S, off < q.1 := by
  obtain ⟨h1, h2, h3⟩ := hU
  unfold hintsOff
  rw [h1]
  exact split_aux entry off d.2.2 h2 h3 hl

theorem bufsOf_eq : bufsOf X d = (hintsOff d).filter fun q ↦ isBuf X q.2 := by
  unfold bufsOf allocHints
  rw [List.filter_filter]
  apply List.filter_congr
  intro q _
  cases hb : isBuf X q.2
  · simp
  · simp [isBuf_ptr hb]

theorem filter_take_idx {α : Type} (p : α → Bool) : ∀ (l : List α) (i : ℕ) {x : α}, l[i]? = some x → p x = true →
    (l.filter p)[(l.take i).countP p]? = some x
  | [], _, _, h, _ => by simp at h
  | a :: l, 0, x, h, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp [hp]
  | a :: l, i + 1, x, h, hp => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.take_succ_cons, List.countP_cons, List.filter_cons]
    have := filter_take_idx p l i h hp
    cases ha : p a
    · simpa using this
    · simpa using this

/-- **The buffer hint at index `i` of an offset's hints** is the buffer hint of index `nbAt` plus the
buffer hints before it there. -/
theorem bufsOf_idx {entry off : ℕ} (hU : HintsUp d entry) {i : ℕ} {h : Prover.Exec.Hint}
    (hi : (hintsAtD d entry off)[i]? = some h) (hb : isBuf X h = true) :
    (bufsOf X d)[nbAt X d off + ((hintsAtD d entry off).take i).countP (isBuf X)]? = some (off, h) := by
  have hl : d.2.2.lookup (entry + off) = some (hintsAtD d entry off) := by
    unfold hintsAtD at hi ⊢
    cases hlk : d.2.2.lookup (entry + off) with
    | none => rw [hlk] at hi; simp at hi
    | some _ => rfl
  obtain ⟨P, S, he, hP, hS⟩ := hintsOff_split hU hl
  set hs := hintsAtD d entry off
  have hnb : nbAt X d off = (P.filter fun q ↦ isBuf X q.2).length := by
    rw [nbAt_eq, bufsOf_eq, he, List.filter_append, List.filter_append, List.countP_append, List.countP_append]
    have h1 : (P.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = (P.filter fun q ↦ isBuf X q.2).length :=
      List.countP_eq_length.mpr fun q hq ↦ by simpa using hP q (List.mem_filter.mp hq).1
    have h2 : ((hs.map fun h ↦ (off, h)).filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        obtain ⟨h', -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hq).1
        simp
    have h3 : (S.filter fun q ↦ isBuf X q.2).countP (fun q ↦ decide (q.1 < off)) = 0 :=
      List.countP_eq_zero.mpr fun q hq ↦ by
        have := hS q (List.mem_filter.mp hq).1
        simp only [decide_eq_true_eq]
        omega
    rw [h1, h2, h3]; rfl
  rw [hnb, bufsOf_eq, he, List.filter_append, List.filter_append, List.append_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have hmi : (hs.map fun h ↦ (off, h))[i]? = some (off, h) := by rw [List.getElem?_map, hi]; rfl
  have := filter_take_idx (fun q : ℕ × Prover.Exec.Hint ↦ isBuf X q.2) _ i hmi hb
  have hc : ((hs.map fun h ↦ (off, h)).take i).countP (fun q ↦ isBuf X q.2) = (hs.take i).countP (isBuf X) := by
    rw [← List.map_take, List.countP_map]; rfl
  rw [hc] at this
  rw [List.getElem?_append_left]
  · exact this
  · exact (List.getElem?_eq_some_iff.mp this).1

end

end LeanVM.Guest.Bridge
