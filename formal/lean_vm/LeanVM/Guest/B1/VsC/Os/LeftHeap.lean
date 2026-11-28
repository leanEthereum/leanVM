/-
  LeanVM.Guest.B1.VsC.Os.LeftHeap

  `open_stacked`'s body: its loads and heap hints, from its statements.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftBody
public import LeanVM.Guest.Memory.HintsCheck
public import LeanVM.Guest.Memory.HintsIn

/-!
# The body's loads and heap hints

`loadAddrs_flatD`: a flat body's loads are its top-level `load` atoms' (a `match` arm loads
nothing). `Stmt.noHeapD`: a statement whose atoms, its `match` arms' included, write no heap word by
a hint; `heapHintAddrs_flatD`: such a body's path writes none. `noHeap_all`: every arm of
`open_stacked`'s body is such (one `decide +kernel` an arm).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem stmtLoad_eq_loadS : Memory.stmtLoad? = Stmt.loadS := by
  funext s
  cases s with
  | atom a => cases a <;> rfl
  | _ => rfl

/-- **A flat body's loads** are its top-level `load` atoms'. -/
theorem loadAddrs_flatD (σ : Val) (pre : List Stmt) (h : pre.all Stmt.flatD = true) :
    loadAddrs σ (pre.flatMap (fdEvs σ)) =
      (pre.filterMap Stmt.loadS).map fun q => (σ q.1).limb 0 * addressOfIndex q.2 := by
  have gL : (pre.filter Stmt.straight).filterMap Memory.stmtLoad? = pre.filterMap Memory.stmtLoad? :=
    filterMap_filter_straightD (fun _ _ => rfl) (fun _ _ _ _ => rfl) pre h
  rw [loadAddrs, filterMap_fdEvs (quietF_loadAddr σ) (fun _ _ _ => rfl) σ pre h, ← loadAddrs,
    Memory.loadAddrs_straight σ _ (straight_filter pre), gL, stmtLoad_eq_loadS]

/-- An atom writing no heap word by a hint. -/
def atomNoHeap (a : Atom) : Bool := (atomHeapDest? a).isNone

/-- A statement whose atoms, its `match` arms' included, write no heap word by a hint. -/
def _root_.LeanVM.Guest.Core.Stmt.noHeapD : Stmt → Bool
  | .atom a => atomNoHeap a
  | .match_ _ arms => arms.all fun arm => arm.all fun s => match s with
    | .atom a => atomNoHeap a
    | _ => true
  | _ => true

theorem hintAddrs_atom_nil (σ : Val) {a : Atom} (h : atomNoHeap a = true) : Ev.hintAddrs σ (.atom a) = [] := by
  cases a with
  | hint hk =>
    simp only [atomNoHeap, atomHeapDest?, Option.isNone_iff_eq_none] at h
    simp [Ev.hintAddrs, h]
  | _ => rfl

theorem fdEvs_noHeap (σ : Val) : ∀ s : Stmt, s.noHeapD = true → ∀ e ∈ fdEvs σ s, Ev.hintAddrs σ e = []
  | .atom a, h, e, he => by
    change e ∈ [Ev.atom a] at he
    rw [List.mem_singleton] at he
    subst he
    exact hintAddrs_atom_nil σ h
  | .call f a r, _, e, he => by
    change e ∈ [Ev.call f a r] at he
    rw [List.mem_singleton] at he
    subst he; rfl
  | .callIf c f a, _, e, he => by
    change e ∈ [Ev.inK c, if σ c = 0 then .skip f a else .call f a []] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rfl
    · split <;> rfl
  | .dispatch x fs a r, _, e, he => by
    simp only [fdEvs, List.mem_singleton] at he
    subst he; rfl
  | .match_ x arms, h, e, he => by
    change e ∈ armEvs (arms.getD (logG (σ x)) []) at he
    obtain ⟨s, hs, hse⟩ := List.mem_filterMap.mp he
    cases s with
    | atom a =>
      simp only [Option.some.injEq] at hse
      subst hse
      refine hintAddrs_atom_nil σ ?_
      have hh : arms.all (fun arm => arm.all fun s => match s with
        | .atom a => atomNoHeap a
        | _ => true) = true := h
      rw [List.getD_eq_getElem?_getD] at hs
      cases harm : arms[logG (σ x)]? with
      | none => rw [harm] at hs; exact absurd hs List.not_mem_nil
      | some arm =>
        rw [harm, Option.getD_some] at hs
        exact List.all_eq_true.mp (List.all_eq_true.mp hh arm (List.mem_of_getElem? harm)) _ hs
    | _ => simp at hse
  | .ite .., _, e, he => by simp [fdEvs] at he
  | .ret _, _, e, he => by simp [fdEvs] at he

/-- **A body without heap hints writes no heap word.** -/
theorem heapHintAddrs_flatD (σ : Val) {ss : List Stmt} (h : ss.all Stmt.noHeapD = true) :
    ∀ A ∈ heapHintAddrs σ (ss.flatMap (fdEvs σ)), False := by
  intro A hA
  obtain ⟨e, he, hA⟩ := List.mem_flatMap.mp hA
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp he
  rw [fdEvs_noHeap σ s (List.all_eq_true.mp h s hs) e he] at hA
  exact absurd hA List.not_mem_nil

set_option maxRecDepth 100000 in
theorem noHeap_0 : (osBodyA (osCfg 0)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_1 : (osBodyA (osCfg 1)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_2 : (osBodyA (osCfg 2)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_3 : (osBodyA (osCfg 3)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_4 : (osBodyA (osCfg 4)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_5 : (osBodyA (osCfg 5)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_6 : (osBodyA (osCfg 6)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_7 : (osBodyA (osCfg 7)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_8 : (osBodyA (osCfg 8)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_9 : (osBodyA (osCfg 9)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_10 : (osBodyA (osCfg 10)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_11 : (osBodyA (osCfg 11)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_12 : (osBodyA (osCfg 12)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_13 : (osBodyA (osCfg 13)).all Stmt.noHeapD = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noHeap_14 : (osBodyA (osCfg 14)).all Stmt.noHeapD = true := by decide +kernel

/-- **No arm's body writes a heap word by a hint.** -/
theorem noHeap_all (m : ℕ) (hm : m < 15) : (osBodyA (osCfg m)).all Stmt.noHeapD = true := by
  interval_cases m
  · exact noHeap_0
  · exact noHeap_1
  · exact noHeap_2
  · exact noHeap_3
  · exact noHeap_4
  · exact noHeap_5
  · exact noHeap_6
  · exact noHeap_7
  · exact noHeap_8
  · exact noHeap_9
  · exact noHeap_10
  · exact noHeap_11
  · exact noHeap_12
  · exact noHeap_13
  · exact noHeap_14

end
end LeanVM.Guest.B1
