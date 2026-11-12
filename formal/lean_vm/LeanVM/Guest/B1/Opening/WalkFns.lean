/-
  LeanVM.Guest.B1.Opening.WalkFns

  Every deployed `walk_path` specialization is its template (`WalkFn`).
-/

module

public import LeanVM.Guest.B1.Opening.WalkPath
public import LeanVM.Guest.B1.Opening.WalkBody0
public import LeanVM.Guest.B1.Opening.WalkBody1
public import LeanVM.Guest.B1.Opening.WalkBody2

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L6` is its template. -/
theorem wpFn_L6_L6 : WalkFn "walk_path__L6_L6" 6 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1599) (by decide +kernel) rfl, rfl, wpBody_L6_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L7` is its template. -/
theorem wpFn_L6_L7 : WalkFn "walk_path__L6_L7" 6 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1598) (by decide +kernel) rfl, rfl, wpBody_L6_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L2` is its template. -/
theorem wpFn_L12_L2 : WalkFn "walk_path__L12_L2" 12 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1597) (by decide +kernel) rfl, rfl, wpBody_L12_L2⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L3` is its template. -/
theorem wpFn_L12_L3 : WalkFn "walk_path__L12_L3" 12 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1507) (by decide +kernel) rfl, rfl, wpBody_L12_L3⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4` is its template. -/
theorem wpFn_L12_L4 : WalkFn "walk_path__L12_L4" 12 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1509) (by decide +kernel) rfl, rfl, wpBody_L12_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5` is its template. -/
theorem wpFn_L12_L5 : WalkFn "walk_path__L12_L5" 12 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1511) (by decide +kernel) rfl, rfl, wpBody_L12_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6` is its template. -/
theorem wpFn_L12_L6 : WalkFn "walk_path__L12_L6" 12 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1513) (by decide +kernel) rfl, rfl, wpBody_L12_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7` is its template. -/
theorem wpFn_L12_L7 : WalkFn "walk_path__L12_L7" 12 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1525) (by decide +kernel) rfl, rfl, wpBody_L12_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8` is its template. -/
theorem wpFn_L12_L8 : WalkFn "walk_path__L12_L8" 12 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1600) (by decide +kernel) rfl, rfl, wpBody_L12_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L2` is its template. -/
theorem wpFn_L18_L2 : WalkFn "walk_path__L18_L2" 18 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1533) (by decide +kernel) rfl, rfl, wpBody_L18_L2⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L3` is its template. -/
theorem wpFn_L18_L3 : WalkFn "walk_path__L18_L3" 18 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1541) (by decide +kernel) rfl, rfl, wpBody_L18_L3⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4` is its template. -/
theorem wpFn_L18_L4 : WalkFn "walk_path__L18_L4" 18 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1549) (by decide +kernel) rfl, rfl, wpBody_L18_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5` is its template. -/
theorem wpFn_L18_L5 : WalkFn "walk_path__L18_L5" 18 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1556) (by decide +kernel) rfl, rfl, wpBody_L18_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6` is its template. -/
theorem wpFn_L18_L6 : WalkFn "walk_path__L18_L6" 18 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1563) (by decide +kernel) rfl, rfl, wpBody_L18_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7` is its template. -/
theorem wpFn_L18_L7 : WalkFn "walk_path__L18_L7" 18 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1570) (by decide +kernel) rfl, rfl, wpBody_L18_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L2` is its template. -/
theorem wpFn_L24_L2 : WalkFn "walk_path__L24_L2" 24 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1577) (by decide +kernel) rfl, rfl, wpBody_L24_L2⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L3` is its template. -/
theorem wpFn_L24_L3 : WalkFn "walk_path__L24_L3" 24 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1584) (by decide +kernel) rfl, rfl, wpBody_L24_L3⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L4` is its template. -/
theorem wpFn_L24_L4 : WalkFn "walk_path__L24_L4" 24 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1591) (by decide +kernel) rfl, rfl, wpBody_L24_L4⟩

/-- **Every deployed `walk_path` is its template.** -/
theorem walkFn_all : ∀ p ∈ walkPathNames, WalkFn p.2.2 p.1 p.2.1 := by
  intro p hp
  simp only [walkPathNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [wpFn_L12_L3, wpFn_L12_L4, wpFn_L12_L5, wpFn_L12_L6, wpFn_L12_L7, wpFn_L18_L2, wpFn_L18_L3, wpFn_L18_L4, wpFn_L18_L5, wpFn_L18_L6, wpFn_L18_L7, wpFn_L24_L2, wpFn_L24_L3, wpFn_L24_L4, wpFn_L12_L2, wpFn_L6_L7, wpFn_L6_L6, wpFn_L12_L8]

end
end LeanVM.Guest.B1
