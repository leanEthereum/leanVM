/-
  LeanVM.Guest.B1.VsC.Os.LeftQx

  `open_stacked`'s body: its atoms pop nothing and are exact but for its window hints.
-/

module

public import LeanVM.Guest.B1.VsC.Os.WalkArms
public import LeanVM.Guest.B1.VsC.Os.WinEx
public import LeanVM.Guest.B1.VsC.Fwd
public import LeanVM.Guest.Exact.Free

/-!
# The body's atoms

`atomQx`: an atom with no witness hint whose hint, if computed, is a window hint. `stmtAtomsD p`: a
statement whose atoms, its `match` arms' included, satisfy `p`; `fdEvs_atomIn`: an atom event of a
flat statement is one of those atoms. `qx_all`: every arm of `open_stacked`'s body has only `atomQx`
atoms (one `decide +kernel` an arm), so its path pops nothing itself and, its window hints exact
(`WinEx`), is exact (`osEvs_exact`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- An atom popping nothing whose hint, if computed, is a window hint. -/
def atomQx (a : Atom) : Bool := atomQuiet a && (!isComputed a || !a.noWin)

/-- A statement whose atoms, its `match` arms' included, satisfy `p`. -/
def stmtAtomsD (p : Atom → Bool) : Stmt → Bool
  | .atom a => p a
  | .match_ _ arms => arms.all fun arm => arm.all fun s => match s with
    | .atom a => p a
    | _ => true
  | _ => true

/-- `a` is the statement or an atom of one of its `match` arms. -/
def AtomIn (s : Stmt) (a : Atom) : Prop :=
  s = .atom a ∨ ∃ x arms, s = .match_ x arms ∧ ∃ arm ∈ arms, Stmt.atom a ∈ arm

theorem stmtAtomsD_of {p : Atom → Bool} {s : Stmt} {a : Atom} (h : stmtAtomsD p s = true) (ha : AtomIn s a) :
    p a = true := by
  rcases ha with rfl | ⟨x, arms, rfl, arm, harm, hs⟩
  · exact h
  · have hh : arms.all (fun arm => arm.all fun s => match s with
      | .atom a => p a
      | _ => true) = true := h
    exact List.all_eq_true.mp (List.all_eq_true.mp hh arm harm) _ hs

theorem winA_of_atomIn {σ : Val} {s : Stmt} {a : Atom} (h : s.WinOk σ) (ha : AtomIn s a) : WinA σ a := by
  rcases ha with rfl | ⟨x, arms, rfl, arm, harm, hs⟩
  · exact h
  · exact h arm harm a hs

/-- **An atom event of a flat statement is one of its atoms.** -/
theorem fdEvs_atomIn {σ : Val} : ∀ (s : Stmt) (a : Atom), Ev.atom a ∈ fdEvs σ s → AtomIn s a
  | .atom b, a, he => by
    change Ev.atom a ∈ [Ev.atom b] at he
    rw [List.mem_singleton] at he
    cases he
    exact Or.inl rfl
  | .call f a r, _, he => by
    change _ ∈ [Ev.call f a r] at he
    rw [List.mem_singleton] at he
    cases he
  | .callIf c f a, _, he => by
    change _ ∈ [Ev.inK c, if σ c = 0 then .skip f a else .call f a []] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h
    · cases h
    · split at h <;> cases h
  | .dispatch x fs a r, _, he => by
    simp only [fdEvs, List.mem_singleton] at he
    cases he
  | .match_ x arms, a, he => by
    change Ev.atom a ∈ armEvs (arms.getD (logG (σ x)) []) at he
    obtain ⟨s, hs, hse⟩ := List.mem_filterMap.mp he
    cases s with
    | atom b =>
      simp only [Option.some.injEq] at hse
      cases hse
      refine Or.inr ⟨x, arms, rfl, ?_⟩
      rw [List.getD_eq_getElem?_getD] at hs
      cases harm : arms[logG (σ x)]? with
      | none => rw [harm] at hs; exact absurd hs List.not_mem_nil
      | some arm =>
        rw [harm, Option.getD_some] at hs
        exact ⟨arm, List.mem_of_getElem? harm, hs⟩
    | _ => simp at hse
  | .ite .., _, he => by simp [fdEvs] at he
  | .ret _, _, he => by simp [fdEvs] at he

set_option maxRecDepth 100000 in
theorem qx_0 : (osBodyA (osCfg 0)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_1 : (osBodyA (osCfg 1)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_2 : (osBodyA (osCfg 2)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_3 : (osBodyA (osCfg 3)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_4 : (osBodyA (osCfg 4)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_5 : (osBodyA (osCfg 5)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_6 : (osBodyA (osCfg 6)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_7 : (osBodyA (osCfg 7)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_8 : (osBodyA (osCfg 8)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_9 : (osBodyA (osCfg 9)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_10 : (osBodyA (osCfg 10)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_11 : (osBodyA (osCfg 11)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_12 : (osBodyA (osCfg 12)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_13 : (osBodyA (osCfg 13)).all (stmtAtomsD atomQx) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem qx_14 : (osBodyA (osCfg 14)).all (stmtAtomsD atomQx) = true := by decide +kernel

/-- **Every arm's atoms pop nothing, their computed hints window hints.** -/
theorem qx_all (m : ℕ) (hm : m < 15) : (osBodyA (osCfg m)).all (stmtAtomsD atomQx) = true := by
  interval_cases m
  · exact qx_0
  · exact qx_1
  · exact qx_2
  · exact qx_3
  · exact qx_4
  · exact qx_5
  · exact qx_6
  · exact qx_7
  · exact qx_8
  · exact qx_9
  · exact qx_10
  · exact qx_11
  · exact qx_12
  · exact qx_13
  · exact qx_14

/-- An atom of the body's path is one of an `atomQx` statement's atoms. -/
theorem osEvs_atom {m ri : ℕ} (hm : m < 15) {σ : Val} {a : Atom}
    (ha : Ev.atom a ∈ (osBodyA (osCfgR m ri)).flatMap (fdEvs σ)) :
    ∃ s ∈ osBodyA (osCfgR m ri), AtomIn s a ∧ atomQx a = true := by
  obtain ⟨s, hs, he⟩ := List.mem_flatMap.mp ha
  have hq := qx_all m hm
  rw [osBodyA_rate m ri] at hq
  have hin := fdEvs_atomIn s a he
  exact ⟨s, hs, hin, stmtAtomsD_of (List.all_eq_true.mp hq s hs) hin⟩

/-- **The body's path pops nothing itself.** -/
theorem osEvs_quiet {m ri : ℕ} (hm : m < 15) {σ : Val} :
    ∀ a, Ev.atom a ∈ (osBodyA (osCfgR m ri)).flatMap (fdEvs σ) → atomQuiet a = true := by
  intro a ha
  obtain ⟨-, -, -, hq⟩ := osEvs_atom hm ha
  simp only [atomQx, Bool.and_eq_true] at hq
  exact hq.1

/-- **The body's path is exact** where its window hints are. -/
theorem osEvs_exact {m ri : ℕ} (hm : m < 15) {σ : Val} (hw : WinEx (osBodyA (osCfgR m ri)) σ) (rd : Reader) :
    ∀ e ∈ (osBodyA (osCfgR m ri)).flatMap (fdEvs σ), e.Exact rd σ := by
  intro e he
  cases e with
  | atom a =>
    obtain ⟨s, hs, hin, hq⟩ := osEvs_atom hm he
    simp only [atomQx, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hq
    cases hn : a.noWin with
    | false => exact winA_of_atomIn (hw s hs) hin hn rd
    | true =>
      rcases hq.2 with hc | hc
      · exact exact_of_not_computed hc
      · rw [hn] at hc; exact absurd hc (by decide)
  | _ => trivial

end
end LeanVM.Guest.B1.VsC
