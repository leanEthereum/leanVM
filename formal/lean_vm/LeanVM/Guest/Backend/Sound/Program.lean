/-
  LeanVM.Guest.Backend.Sound.Program

  What a compiled program is made of: the checks its compilation passed, each function's
  placement, and where its code lies in the assembled program.
-/

module

public import LeanVM.Guest.Backend.Sound.Fn

/-!
# The parts of a compiled program
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## A body that holds reaches a `return` -/

section

variable {C : CallRel} {rd : Reader} {σ : Val}

mutual
theorem holds_reach : ∀ (s : Stmt) {next : Prop} {kret : List E → Prop},
    Stmt.Holds C rd σ s next kret → next ∨ ∃ rs, kret rs
  | .atom _, _, _, h => Or.inl h.2
  | .ite c z n, _, _, h => by
      by_cases hc : σ c = 0
      · exact holdsList_reach z (h.2.1 hc)
      · exact holdsList_reach n (h.2.2 hc)
  | .match_ x arms, _, _, h => holdsArms_reach x arms 0 h
  | .call .., _, _, h => Or.inl h.2
  | .callIf .., _, _, h => Or.inl h.2.2
  | .dispatch .., _, _, h => Or.inl h.2
  | .ret _, _, _, h => Or.inr ⟨_, h⟩

theorem holdsList_reach : ∀ (ss : List Stmt) {next : Prop} {kret : List E → Prop},
    Stmt.HoldsList C rd σ ss next kret → next ∨ ∃ rs, kret rs
  | [], _, _, h => Or.inl h
  | s :: ss, _, _, h => (holds_reach s h).elim (holdsList_reach ss) Or.inr

theorem holdsArms_reach (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {next : Prop}
    {kret : List E → Prop}, Stmt.HoldsArms C rd σ x j arms next kret → next ∨ ∃ rs, kret rs
  | [], _, _, _, h => h.elim
  | a :: as, j, _, _, h => h.elim (fun h => holdsList_reach a h.2) (holdsArms_reach x as (j + 1))
end

end

/-! ## Signatures -/

theorem sigTable_fold : ∀ (p : List TracedFn) (m : Std.HashMap String (ℕ × ℕ)) (g : String)
    (s : ℕ × ℕ), (p.foldl (fun m tf => m.insert tf.core.name (sigOf tf)) m)[g]? = some s →
      m[g]? = some s ∨ ∃ tf ∈ p, tf.core.name = g ∧ sigOf tf = s
  | [], _, _, _, h => Or.inl h
  | tf :: p, m, g, s, h => by
      rcases sigTable_fold p _ g s h with h' | ⟨tf', hm, hn, hs⟩
      · rw [Std.HashMap.getElem?_insert] at h'
        split at h'
        · next heq =>
          exact Or.inr ⟨tf, List.mem_cons_self, eq_of_beq heq, Option.some.inj h'⟩
        · exact Or.inl h'
      · exact Or.inr ⟨tf', List.mem_cons_of_mem _ hm, hn, hs⟩

/-- A name with a signature is a function of the program, of that signature. -/
theorem sigTable_get {p : List TracedFn} {g : String} {s : ℕ × ℕ} (h : (sigTable p)[g]? = some s) :
    ∃ tf ∈ p, tf.core.name = g ∧ sigOf tf = s := by
  rcases sigTable_fold p {} g s h with h' | h'
  · simp at h'
  · exact h'

/-- A callee is a function of the program other than `main`, of the call's arity. -/
theorem isCallee_get {p : List TracedFn} {g : String} {a r : ℕ}
    (h : isCallee (sigTable p) a r g = true) :
    g ≠ "main" ∧ ∃ tf ∈ p, tf.core.name = g ∧ sigOf tf = (a, r) := by
  simp only [isCallee, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1, sigTable_get h.2⟩

/-! ## The functions' placements -/

/-- Each function was placed, from some state of the jump tables whose shared tables are among
the program's. -/
theorem placeFns_spec {loops : Loops} {sigs : Std.HashMap String (ℕ × ℕ)} :
    ∀ (l : List TracedFn) (t : Tables) {pls : List Placed} {t' : Tables},
      placeFns loops sigs l t = .ok (pls, t') → TablesLe t t' ∧
        List.Forall₂ (fun tf pf => ∃ ti ti', placeFn loops sigs ti tf = .ok (pf, ti') ∧
          TablesLe ti' t') l pls
  | [], t, pls, t', h => by
      rw [placeFns] at h
      cases h
      exact ⟨TablesLe.refl _, .nil⟩
  | tf :: rest, t, pls, t', h => by
      rw [placeFns] at h
      split at h
      · cases h
      · next pf t1 hpf =>
        split at h
        · cases h
        · next hsuf =>
          split at h
          · cases h
          · next pfs t2 hrest =>
            cases h
            obtain ⟨hle, hall⟩ := placeFns_spec rest t1 hrest
            have h01 : TablesLe t t1 := by
              have hs : t.shared <:+ t1.shared := by
                rw [← List.isSuffixOf_iff_suffix]
                simpa using hsuf
              exact ⟨fun p hp => hs.subset hp⟩
            exact ⟨h01.trans hle, .cons ⟨t, t1, hpf, hle⟩ hall⟩

theorem placeProgram_ok {p : List TracedFn} {placed : List Placed} {tables : Tables}
    (h : placeProgram p = .ok (placed, tables)) :
    (p.map (·.core.name)).head? = some "main" ∧ "__jump_tables" ∉ p.map (·.core.name) ∧
      (p.map (·.core.name)).Nodup ∧ placeFns (loopTable p) (sigTable p) p {} = .ok (placed, tables) := by
  unfold placeProgram at h
  split at h
  · cases h
  · next h1 =>
    split at h
    · cases h
    · next h2 =>
      split at h
      · cases h
      · next h3 =>
        exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, h⟩

theorem slotsHold_spec {slots : Array KVal} {fills : List Fill}
    {shared : List (List String × ℕ)} (h : slotsHold slots fills shared = true) :
    FillsIn slots fills ∧ ∀ p ∈ shared, ∀ j (hj : j < p.1.length),
      slots[p.2 + j]? = some (.entry p.1[j]) := by
  simp only [slotsHold, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, fun p hp j hj => ?_⟩
  exact h.2 p hp (p.1[j], j) (List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩)

theorem lowerProgram_ok {p : List TracedFn} {fns : List Lowered} {slots : Array KVal}
    (h : lowerProgram p = .ok (fns, slots)) :
    ∃ placed tables, placeProgram p = .ok (placed, tables) ∧
      fns = placed.map (fun pf => (emitFn pf.fn).1) ∧ FillsIn slots (fillsOf placed) ∧
      SharedIn slots tables := by
  unfold lowerProgram at h
  split at h
  · cases h
  · next placed tables hp =>
    by_cases hs : slotsHold (tableSlots tables.len (fillsOf placed).toArray tables.entries)
        (fillsOf placed) tables.shared = true
    · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨placed, tables, hp, rfl, (slotsHold_spec hs).1, (slotsHold_spec hs).2⟩
    · simp [hs] at h

end
end LeanVM.Guest.Backend
