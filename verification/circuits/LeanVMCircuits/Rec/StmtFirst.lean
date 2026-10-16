module

public import LeanVMCircuits.Rec.Contracts

@[expose] public section

/-!
The public table in the Rust circuit's order.

The model keeps the public rows in building order (`State.pub`), while `Builder::finish` puts the statement's rows first, in statement order, then the constants' in building order (`Builder::statement_first`), so that the statement's words sit on the public table's first rows. The Rust verifier evaluates the public table's value and `Next` columns in that order, so a child's committed witness, keys and bus roots are the reordered circuit's (`stmtFirst`). `checkrec` compares the reordered model with the Rust circuit (`pubFirst`), and the reordering keeps satisfaction, since `Sat` reads the public rows as a set (`sat_stmtFirst`).
-/

namespace LeanVMCircuits.Rec.Model

/-- `Builder::statement_first`'s order of public rows: the statement's, sorted by statement index, then the constants', in order. -/
def pubFirst (rows : List (ℕ × PubSource)) : List (ℕ × PubSource) :=
  ((rows.filterMap fun r => match r.2 with
    | .statement j => some (j, r)
    | .const _ => none).mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2) ++
  rows.filter fun r => match r.2 with
    | .const _ => true
    | .statement _ => false

/-- The circuit with its public rows in `Builder::statement_first`'s order. -/
def stmtFirst (s : State) : State := { s with pub := (pubFirst s.pub.toList).toArray }

theorem mem_pubFirst {rows : List (ℕ × PubSource)} {p : ℕ × PubSource} : p ∈ pubFirst rows ↔ p ∈ rows := by
  simp only [pubFirst, List.mem_append, List.mem_map, List.mem_filter]
  constructor
  · rintro (⟨q, hq, rfl⟩ | ⟨hp, -⟩)
    · have hq' := (List.mergeSort_perm _ _).mem_iff.mp hq
      obtain ⟨r, hr, hf⟩ := List.mem_filterMap.mp hq'
      rcases r with ⟨w, src⟩
      cases src with
      | const v => simp at hf
      | statement j => simp only [Option.some.injEq] at hf; rw [← hf]; exact hr
    · exact hp
  · intro hp
    rcases p with ⟨w, src⟩
    cases src with
    | const v => exact Or.inr ⟨hp, rfl⟩
    | statement j =>
      exact Or.inl ⟨(j, (w, .statement j)), (List.mergeSort_perm _ _).mem_iff.mpr
        (List.mem_filterMap.mpr ⟨(w, .statement j), hp, rfl⟩), rfl⟩

theorem length_pubFirst (rows : List (ℕ × PubSource)) : (pubFirst rows).length = rows.length := by
  simp only [pubFirst, List.length_append, List.length_map, List.length_mergeSort]
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨w, src⟩
    cases src with
    | const v => simp; omega
    | statement j => simp; omega

theorem mem_stmtFirst_pub {s : State} {p : ℕ × PubSource} : p ∈ (stmtFirst s).pub ↔ p ∈ s.pub := by
  simp only [stmtFirst, List.mem_toArray, mem_pubFirst, Array.mem_toList_iff]

theorem size_stmtFirst_pub (s : State) : (stmtFirst s).pub.size = s.pub.size := by
  simp only [stmtFirst, List.size_toArray, length_pubFirst, Array.length_toList]

/-- Reordering the public rows keeps satisfaction: `Sat` reads them as a set. -/
theorem sat_stmtFirst {st : ℕ → Fin 4 → K} {s : State} {val : Val} : Sat st (stmtFirst s) val ↔ Sat st s val :=
  ⟨fun h => ⟨h.unions, h.emul, h.exk, h.hash, h.split, h.cast, fun w src hm => h.pub w src (mem_stmtFirst_pub.mpr hm)⟩,
    fun h => ⟨h.unions, h.emul, h.exk, h.hash, h.split, h.cast, fun w src hm => h.pub w src (mem_stmtFirst_pub.mp hm)⟩⟩

/-- Non-vacuity: a statement row made after a constant comes first. -/
example : pubFirst [(5, .const []), (7, .statement 0)] = [(7, .statement 0), (5, .const [])] := by
  simp [pubFirst, List.mergeSort_singleton]

end LeanVMCircuits.Rec.Model
