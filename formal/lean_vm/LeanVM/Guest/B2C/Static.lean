/-
  LeanVM.Guest.B2C.Static

  The certificate's lists of temporaries and frame runs, and a body's atoms.
-/

module

public import LeanVM.Guest.B2C.ShareOk
public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.TrieFacts

/-!
# The certificate's lists

What `listed`, `listedT` and `pairsOk` say (`listed_spec`, `listedT_spec`, `pairsOk_spec`); an
atom's values are its statement's (`uses_of_lAtoms`); a temporary of a function is one of its
body's (`temps_of`); a frame run's entries (`mem_runsE`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Exec LeanVM.Guest.Check

@[expose] public section

/-! ## The certificate's lists -/

section Lists

theorem listed_spec {l : List (ℕ × ℕ)} {v : V} {c : ℕ} (h : listed l v c = true) :
    v = V.n v.idx ∧ (v.idx, c) ∈ l := by
  simp only [listed, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, nbeq_iff] at h
  obtain ⟨h1, p, hp, h2, h3⟩ := h
  refine ⟨h1, ?_⟩
  rw [← h2, ← h3]; exact hp

theorem getF_byCell : ∀ (l : List (ℕ × ℕ)) (t : Exec.Trie ℕ) {c v : ℕ},
    getF (l.foldl (fun t p ↦ setF p.1 envDepth t p.2) t) c = some v → (∃ p ∈ l, p.2 = c ∧ p.1 = v) ∨
      getF t c = some v
  | [], _, _, _, h => Or.inr h
  | p :: l, t, c, v, h => by
    rcases getF_byCell l _ h with ⟨q, hq, h1, h2⟩ | h
    · exact Or.inl ⟨q, List.mem_cons_of_mem _ hq, h1, h2⟩
    · rcases Check.getF_setF h with ⟨rfl, rfl⟩ | h
      · exact Or.inl ⟨p, List.mem_cons_self, rfl, rfl⟩
      · exact Or.inr h

theorem listedT_spec {l : List (ℕ × ℕ)} {v : V} {c : ℕ} (h : listedT (byCell l) v c = true) :
    v = V.n v.idx ∧ (v.idx, c) ∈ l := by
  simp only [listedT, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  rcases getF_byCell l .nil h.2 with ⟨p, hp, h1, h2⟩ | h'
  · rw [← h1, ← h2]; exact hp
  · simp [getF_eq] at h'

theorem pairsOk_spec {l : List (ℕ × ℕ)} {n : ℕ} (h : pairsOk l n = true) :
    (∀ p ∈ l, 2 ≤ p.2 ∧ p.2 < n) ∧ ∀ p ∈ l, ∀ q ∈ l, p.2 = q.2 → p.1 = q.1 := by
  simp only [pairsOk, Exec.Trie.seq_eq, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq,
    Nat.blt_eq] at h
  refine ⟨fun p hp ↦ ⟨(h p hp).1.2, (h p hp).2⟩, fun p hp q hq he ↦ ?_⟩
  have h1 := (h p hp).1.1
  have h2 := (h q hq).1.1
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

end Lists

/-! ## Atoms -/

section Atoms

theorem lAtoms_append : ∀ (a b : List Stmt), lAtoms (a ++ b) = lAtoms a ++ lAtoms b
  | [], b => by simp [lAtoms]
  | s :: a, b => by simp only [List.cons_append, lAtoms, lAtoms_append a b, List.append_assoc]

mutual
/-- An atom's values are its statement's. -/
theorem uses_of_sAtoms : ∀ (s : Stmt) {a : Core.Atom}, a ∈ sAtoms s → ∀ v ∈ atomUses a, v ∈ Stmt.uses s
  | .atom a', a, h, v, hv => by
      simp only [sAtoms, List.mem_singleton] at h; subst h; exact hv
  | .ite c z n, a, h, v, hv => by
      simp only [sAtoms, List.mem_append] at h
      simp only [Stmt.uses, List.mem_cons, List.mem_append]
      rcases h with h | h
      · exact Or.inr (Or.inl (uses_of_lAtoms z h v hv))
      · exact Or.inr (Or.inr (uses_of_lAtoms n h v hv))
  | .match_ x arms, a, h, v, hv => by
      simp only [sAtoms] at h
      simp only [Stmt.uses, List.mem_cons]
      exact Or.inr (uses_of_aAtoms arms h v hv)
  | .call .., _, h, _, _ => by simp [sAtoms] at h
  | .callIf .., _, h, _, _ => by simp [sAtoms] at h
  | .dispatch .., _, h, _, _ => by simp [sAtoms] at h
  | .ret _, _, h, _, _ => by simp [sAtoms] at h

theorem uses_of_lAtoms : ∀ (ss : List Stmt) {a : Core.Atom}, a ∈ lAtoms ss → ∀ v ∈ atomUses a,
    v ∈ Stmt.usesList ss
  | [], _, h, _, _ => by simp [lAtoms] at h
  | s :: ss, a, h, v, hv => by
      simp only [lAtoms, List.mem_append] at h
      simp only [Stmt.usesList, List.mem_append]
      rcases h with h | h
      · exact Or.inl (uses_of_sAtoms s h v hv)
      · exact Or.inr (uses_of_lAtoms ss h v hv)

theorem uses_of_aAtoms : ∀ (arms : List (List Stmt)) {a : Core.Atom}, a ∈ aAtoms arms → ∀ v ∈ atomUses a,
    v ∈ Stmt.usesArms arms
  | [], _, h, _, _ => by simp [aAtoms] at h
  | b :: as, a, h, v, hv => by
      simp only [aAtoms, List.mem_append] at h
      simp only [Stmt.usesArms, List.mem_append]
      rcases h with h | h
      · exact Or.inl (uses_of_lAtoms b h v hv)
      · exact Or.inr (uses_of_aAtoms as h v hv)
end

end Atoms

section Static

theorem temps_of {f : String} {t : V} (ht : t ∈ coreProgram.temps f) :
    ∃ j, idxOf f = some j ∧ t ∈ Stmt.tmpsList (coreOf j).body := by
  unfold Program.temps at ht
  cases hj : idxOf f with
  | none =>
    have : coreProgram.indexOf? f = none := by
      unfold idxOf at hj; exact Option.map_eq_none_iff.mp hj
    rw [find?_none this] at ht; cases ht
  | some j =>
    obtain ⟨i, rfl, hi, -, hf, hc, -⟩ := fn_of_idx hj
    rw [hf] at ht
    exact ⟨i + 1, rfl, by rw [hc]; exact ht⟩

theorem mem_runsE {f : String} {σ : Val} {es : List Ev} {x : ℕ × E} (h : x ∈ runsE f σ es) :
    ∃ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ es ∧ ∃ k, ∃ hk : k < (r :: rs).length,
      x = (cert f r + k, σ (r :: rs)[k]) := by
  simp only [runsE, List.mem_flatMap] at h
  obtain ⟨e, he, hx⟩ := h
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨p, _ | ⟨r, rs⟩⟩ | _ | _⟩ | _ | _ | _ <;>
    simp only [List.not_mem_nil] at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hx
  exact ⟨p, r, rs, he, k, hk, rfl⟩

end Static

end
end LeanVM.Guest.B2C
