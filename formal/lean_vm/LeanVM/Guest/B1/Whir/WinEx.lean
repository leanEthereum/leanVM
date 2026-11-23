/-
  LeanVM.Guest.B1.Whir.WinEx

  A block's window hints exact at a valuation, on every memory: what the inlined grind checks' blocks carry to the body's
  honest valuation.
-/

module

public import LeanVM.Guest.Exact.Defs

/-!
# Window hints exact

The inlined grind checks (`gcInlineT`) write their windows with `windowsExp` hints that no next atom pins, so the arms'
exactness (`Arm.armExact_every`) takes them from the honest valuation: `WinEx ss σ`, every window hint of the block `ss`
(its `match` arms' included) exact at `σ` on every memory. A block without window hints has it at every valuation
(`winEx_of_noWin`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- No `windowsExp` hint. -/
def _root_.LeanVM.Guest.Core.Atom.noWin : Atom → Bool
  | .hint (.windowsExp ..) => false
  | _ => true

/-- A window hint is exact at `σ` on every memory. -/
def WinA (σ : Val) (a : Atom) : Prop := a.noWin = false → ∀ rd, a.Exact rd σ

/-- A statement's window hints, its `match` arms' atoms included, exact at `σ`. -/
def _root_.LeanVM.Guest.Core.Stmt.WinOk (σ : Val) : Stmt → Prop
  | .atom a => WinA σ a
  | .match_ _ arms => ∀ arm ∈ arms, ∀ a, Stmt.atom a ∈ arm → WinA σ a
  | _ => True

/-- **A block's window hints are exact** at `σ` on every memory. -/
def WinEx (ss : List Stmt) (σ : Val) : Prop := ∀ s ∈ ss, s.WinOk σ

/-- A statement without window hints, its `match` arms' atoms included. -/
def _root_.LeanVM.Guest.Core.Stmt.noWin : Stmt → Bool
  | .atom a => a.noWin
  | .match_ _ arms => arms.all fun arm => arm.all fun s => match s with
    | .atom a => a.noWin
    | _ => true
  | _ => true

theorem winA_of_noWin {σ : Val} {a : Atom} (h : a.noWin = true) : WinA σ a :=
  fun h' => absurd (h.symm.trans h') (by decide)

theorem winOk_of_noWin {σ : Val} {s : Stmt} (h : s.noWin = true) : s.WinOk σ := by
  cases s with
  | atom a => exact winA_of_noWin h
  | match_ x arms =>
    intro arm harm a ha
    have h0 : arms.all (fun arm => arm.all fun s => match s with
      | .atom a => a.noWin
      | _ => true) = true := h
    have h1 : a.noWin = true := List.all_eq_true.mp (List.all_eq_true.mp h0 arm harm) _ ha
    exact winA_of_noWin h1
  | _ => trivial

/-- **A block without window hints** has them exact at every valuation. -/
theorem winEx_of_noWin {σ : Val} {ss : List Stmt} (h : ss.all Stmt.noWin = true) : WinEx ss σ :=
  fun s hs => winOk_of_noWin (List.all_eq_true.mp h s hs)

theorem winEx_nil {σ : Val} : WinEx [] σ := fun _ h => absurd h List.not_mem_nil

theorem winEx_append {σ : Val} {ss ts : List Stmt} : WinEx (ss ++ ts) σ ↔ WinEx ss σ ∧ WinEx ts σ := by
  simp only [WinEx, List.mem_append]
  exact ⟨fun h => ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩,
    fun h s hs => hs.elim (h.1 s) (h.2 s)⟩

theorem noWin_cons {s : Stmt} {ss : List Stmt} (h1 : s.noWin = true) (h2 : ss.all Stmt.noWin = true) :
    (s :: ss).all Stmt.noWin = true := by
  rw [List.all_cons, h1, h2]; rfl

theorem noWin_map {α : Type} {l : List α} {f : α → Stmt} (h : ∀ x, (f x).noWin = true) :
    (l.map f).all Stmt.noWin = true :=
  List.all_eq_true.mpr fun s hs => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hs
    exact h x

theorem noWin_flatten {L : List (List Stmt)} (h : ∀ l ∈ L, l.all Stmt.noWin = true) :
    L.flatten.all Stmt.noWin = true :=
  List.all_eq_true.mpr fun s hs => by
    obtain ⟨l, hl, hs⟩ := List.mem_flatten.mp hs
    exact List.all_eq_true.mp (h l hl) s hs

theorem noWin_flatten_map {α : Type} {l : List α} {f : α → List Stmt} (h : ∀ x, (f x).all Stmt.noWin = true) :
    (l.map f).flatten.all Stmt.noWin = true :=
  noWin_flatten fun _ hl => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
    exact h x

/-- A `match` whose arms have no window hints. -/
theorem noWin_match {x : V} {arms : List (List Stmt)} (h : ∀ arm ∈ arms, arm.all Stmt.noWin = true) :
    (Stmt.match_ x arms).noWin = true := by
  show arms.all (fun arm => arm.all fun s => match s with
    | .atom a => a.noWin
    | _ => true) = true
  refine List.all_eq_true.mpr fun arm harm => List.all_eq_true.mpr fun s hs => ?_
  have h1 := List.all_eq_true.mp (h arm harm) s hs
  cases s <;> first | exact h1 | rfl

end
end LeanVM.Guest.B1.Whir
