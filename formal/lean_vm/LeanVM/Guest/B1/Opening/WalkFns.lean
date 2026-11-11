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
theorem wpFn_1749 : WalkFn "walk_path__L6_L6" 6 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1533) (by decide +kernel) rfl, rfl, wpBody_1749⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L6_L7` is its template. -/
theorem wpFn_1748 : WalkFn "walk_path__L6_L7" 6 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1532) (by decide +kernel) rfl, rfl, wpBody_1748⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L2` is its template. -/
theorem wpFn_1747 : WalkFn "walk_path__L12_L2" 12 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1531) (by decide +kernel) rfl, rfl, wpBody_1747⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L3` is its template. -/
theorem wpFn_1642 : WalkFn "walk_path__L12_L3" 12 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1438) (by decide +kernel) rfl, rfl, wpBody_1642⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4` is its template. -/
theorem wpFn_1662 : WalkFn "walk_path__L12_L4" 12 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1458) (by decide +kernel) rfl, rfl, wpBody_1662⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5` is its template. -/
theorem wpFn_1645 : WalkFn "walk_path__L12_L5" 12 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1441) (by decide +kernel) rfl, rfl, wpBody_1645⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6` is its template. -/
theorem wpFn_1665 : WalkFn "walk_path__L12_L6" 12 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1461) (by decide +kernel) rfl, rfl, wpBody_1665⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7` is its template. -/
theorem wpFn_1674 : WalkFn "walk_path__L12_L7" 12 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1470) (by decide +kernel) rfl, rfl, wpBody_1674⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8` is its template. -/
theorem wpFn_1750 : WalkFn "walk_path__L12_L8" 12 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1534) (by decide +kernel) rfl, rfl, wpBody_1750⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L2` is its template. -/
theorem wpFn_1683 : WalkFn "walk_path__L18_L2" 18 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1479) (by decide +kernel) rfl, rfl, wpBody_1683⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L3` is its template. -/
theorem wpFn_1692 : WalkFn "walk_path__L18_L3" 18 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1488) (by decide +kernel) rfl, rfl, wpBody_1692⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4` is its template. -/
theorem wpFn_1700 : WalkFn "walk_path__L18_L4" 18 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1496) (by decide +kernel) rfl, rfl, wpBody_1700⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5` is its template. -/
theorem wpFn_1706 : WalkFn "walk_path__L18_L5" 18 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1502) (by decide +kernel) rfl, rfl, wpBody_1706⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6` is its template. -/
theorem wpFn_1712 : WalkFn "walk_path__L18_L6" 18 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1508) (by decide +kernel) rfl, rfl, wpBody_1712⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7` is its template. -/
theorem wpFn_1718 : WalkFn "walk_path__L18_L7" 18 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1514) (by decide +kernel) rfl, rfl, wpBody_1718⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L2` is its template. -/
theorem wpFn_1724 : WalkFn "walk_path__L24_L2" 24 2 :=
  ⟨_, Program.find?_of_indexOf? (j := 1520) (by decide +kernel) rfl, rfl, wpBody_1724⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L3` is its template. -/
theorem wpFn_1726 : WalkFn "walk_path__L24_L3" 24 3 :=
  ⟨_, Program.find?_of_indexOf? (j := 1522) (by decide +kernel) rfl, rfl, wpBody_1726⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L24_L4` is its template. -/
theorem wpFn_1731 : WalkFn "walk_path__L24_L4" 24 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1527) (by decide +kernel) rfl, rfl, wpBody_1731⟩

end
end LeanVM.Guest.B1
