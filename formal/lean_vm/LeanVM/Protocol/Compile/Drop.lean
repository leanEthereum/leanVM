/-
  LeanVM.Protocol.Compile.Drop

  Histories past a prefix without commitments: reachability, boundaries and escape probabilities
  read off the node at the prefix.
-/

module

public import LeanVM.Protocol.Compile.Rom.Sound

/-!
# Histories past a prefix

A seed puts a program at a root history (`RootOk`), and a sub-program at a later node. These
lemmas read the run past a prefix `h₀` without commitments as a run of the node at `h₀`:
reachability (`reachable_drop`), the openings' answers (`answer_append`), boundaries
(`boundary_drop`) and escape probabilities (`esc_drop`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Protocol.Compile.Rom

@[expose] public section

section Transport

variable {P p : VerifierProgram Bool} {h₀ : List Ev}

theorem answer_append (hc : commits h₀ = []) (h : List Ev) (i : ℕ) (ps : List ℕ) :
    answer (h₀ ++ h) i ps = answer h i ps := by
  simp [answer, Compile.commits_append, hc]

/-- A reachable history past a prefix without commitments is a reachable history of the node
at the prefix. -/
theorem reachable_drop (ha : P.after h₀ = some p) (hc : commits h₀ = []) :
    ∀ {h : List Ev}, P.Reachable h → ∀ h', h = h₀ ++ h' → p.Reachable h' := by
  intro h hr
  induction hr with
  | nil =>
    intro h' he
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact VerifierProgram.Reachable.nil
  | @read h k x hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.read (k := k) x (ih h'' rfl) ?_
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
  | @sample h k c hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.sample (k := k) c (ih h'' rfl) ?_
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
  | @grind h b k hr hk ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.grind (k := k) (ih h'' rfl) ?_
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
  | @commit h ht w k word hr hk hw ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.commit (k := k) word (ih h'' rfl) ?_ hw
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
  | @query h i ps k rows hr hk hans ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.query (i := i) (ps := ps) (k := k) (ih h'' rfl) ?_ ?_
      · rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
      · rwa [answer_append hc] at hans
  | @readPacked h n k xs hr hk hn ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.readPacked (k := k) xs (ih h'' rfl) ?_ hn
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk
  | @samplePacked h n k cs hr hk hn ih =>
    intro h' he
    rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
    · exact VerifierProgram.Reachable.nil
    · rw [List.concat_eq_append, ← List.append_assoc] at he
      rw [List.concat_eq_append]
      obtain ⟨rfl, he2⟩ := List.append_inj' he rfl
      obtain rfl := List.singleton_inj.mp he2
      refine VerifierProgram.Reachable.samplePacked (k := k) cs (ih h'' rfl) ?_ hn
      rwa [VerifierProgram.after_append, ha, Option.bind_some] at hk

theorem after_drop (ha : P.after h₀ = some p) (h' : List Ev) :
    P.after (h₀ ++ h') = p.after h' := by
  rw [VerifierProgram.after_append, ha, Option.bind_some]

/-- Escape probabilities past a prefix without commitments, for doom predicates that agree
past it. -/
theorem esc_drop (hc : commits h₀ = []) {D D' : List Ev → Prop}
    (hD : ∀ h', D (h₀ ++ h') ↔ D' h') :
    ∀ (h' : List Ev) (q : VerifierProgram Bool), esc D (h₀ ++ h') q = esc D' h' q
  | h', .sample k => by
    rw [esc_sample, esc_sample]
    congr 1
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [List.append_assoc]
    exact esc_drop hc hD _ _
  | h', .query i ps k => by
    rw [esc_query, esc_query, answer_append hc]
    split
    · rw [List.append_assoc]; exact esc_drop hc hD _ _
    · rfl
  | h', .ret true => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .ret false => rfl
  | h', .fail => rfl
  | h', .read k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .readPacked n k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .samplePacked n k => by
    simp only [esc]
    refine avgPk_congr fun cs _ ↦ ?_
    rw [List.append_assoc]
    exact esc_drop hc hD _ _
  | h', .grind b k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]
  | h', .commit ht w k => by
    simp only [esc]
    by_cases hd : D' h'
    · simp [hd, (hD h').mpr hd]
    · simp [hd, mt (hD h').mp hd]

/-- A boundary history ending in one more event. -/
theorem boundary_append_of {h h' : List Ev} {e : Ev} (hb : Boundary (h ++ [e])) :
    Boundary (h' ++ [e]) := by
  cases e with
  | read x => exact boundary_append_read _ _
  | grind b => exact boundary_append_grind _ _
  | commit ht w W => exact boundary_append_commit _ _ _ _
  | sample c => exact absurd hb (not_boundary_append_sample _ _)
  | query rows => exact absurd hb (not_boundary_append_query _ _)
  | readPacked xs => exact boundary_append_readPacked _ _
  | samplePacked cs => exact absurd hb (not_boundary_append_samplePacked _ _)

/-- A boundary past a prefix is a boundary of the rest. -/
theorem boundary_drop {h' : List Ev} (hb : Boundary (h₀ ++ h')) : Boundary h' := by
  rcases List.eq_nil_or_concat h' with rfl | ⟨h'', e, rfl⟩
  · trivial
  · rw [List.concat_eq_append] at hb ⊢
    rw [← List.append_assoc] at hb
    exact boundary_append_of hb

end Transport

theorem boundary_map_read {l : List E} (hl : l ≠ []) : Boundary (l.map Ev.read) := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', e, rfl⟩
  · exact absurd rfl hl
  · rw [List.concat_eq_append, List.map_append, List.map_singleton]
    exact boundary_append_read _ _

theorem grindBits_map_read (l : List E) : grindBits (l.map Ev.read) = 0 := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', e, rfl⟩
  · rfl
  · rw [List.concat_eq_append, List.map_append, List.map_singleton]
    exact grindBits_append_read _ _

/-- The commitments of reads. -/
theorem commits_map_read (xs : List E) : commits (xs.map Ev.read) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [commits] using ih

end
end LeanVM.Protocol.Compile
