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
/-- `walk_path__L9_L5` is its template. -/
theorem wpFn_L9_L5 : WalkFn "walk_path__L9_L5" 9 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1012) (by decide +kernel) rfl, rfl, wpBody_L9_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L8` is its template. -/
theorem wpFn_L9_L8 : WalkFn "walk_path__L9_L8" 9 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1009) (by decide +kernel) rfl, rfl, wpBody_L9_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L5` is its template. -/
theorem wpFn_L10_L5 : WalkFn "walk_path__L10_L5" 10 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1011) (by decide +kernel) rfl, rfl, wpBody_L10_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L6` is its template. -/
theorem wpFn_L10_L6 : WalkFn "walk_path__L10_L6" 10 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1010) (by decide +kernel) rfl, rfl, wpBody_L10_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L8` is its template. -/
theorem wpFn_L10_L8 : WalkFn "walk_path__L10_L8" 10 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1013) (by decide +kernel) rfl, rfl, wpBody_L10_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L5` is its template. -/
theorem wpFn_L11_L5 : WalkFn "walk_path__L11_L5" 11 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1015) (by decide +kernel) rfl, rfl, wpBody_L11_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L6` is its template. -/
theorem wpFn_L11_L6 : WalkFn "walk_path__L11_L6" 11 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1014) (by decide +kernel) rfl, rfl, wpBody_L11_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L7` is its template. -/
theorem wpFn_L11_L7 : WalkFn "walk_path__L11_L7" 11 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 949) (by decide +kernel) rfl, rfl, wpBody_L11_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L8` is its template. -/
theorem wpFn_L11_L8 : WalkFn "walk_path__L11_L8" 11 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1016) (by decide +kernel) rfl, rfl, wpBody_L11_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5` is its template. -/
theorem wpFn_L12_L5 : WalkFn "walk_path__L12_L5" 12 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1018) (by decide +kernel) rfl, rfl, wpBody_L12_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6` is its template. -/
theorem wpFn_L12_L6 : WalkFn "walk_path__L12_L6" 12 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1017) (by decide +kernel) rfl, rfl, wpBody_L12_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7` is its template. -/
theorem wpFn_L12_L7 : WalkFn "walk_path__L12_L7" 12 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 952) (by decide +kernel) rfl, rfl, wpBody_L12_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8` is its template. -/
theorem wpFn_L12_L8 : WalkFn "walk_path__L12_L8" 12 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1019) (by decide +kernel) rfl, rfl, wpBody_L12_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L5` is its template. -/
theorem wpFn_L13_L5 : WalkFn "walk_path__L13_L5" 13 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1021) (by decide +kernel) rfl, rfl, wpBody_L13_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L6` is its template. -/
theorem wpFn_L13_L6 : WalkFn "walk_path__L13_L6" 13 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1020) (by decide +kernel) rfl, rfl, wpBody_L13_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L7` is its template. -/
theorem wpFn_L13_L7 : WalkFn "walk_path__L13_L7" 13 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 955) (by decide +kernel) rfl, rfl, wpBody_L13_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L8` is its template. -/
theorem wpFn_L13_L8 : WalkFn "walk_path__L13_L8" 13 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1022) (by decide +kernel) rfl, rfl, wpBody_L13_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L4` is its template. -/
theorem wpFn_L14_L4 : WalkFn "walk_path__L14_L4" 14 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1028) (by decide +kernel) rfl, rfl, wpBody_L14_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L5` is its template. -/
theorem wpFn_L14_L5 : WalkFn "walk_path__L14_L5" 14 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1023) (by decide +kernel) rfl, rfl, wpBody_L14_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L6` is its template. -/
theorem wpFn_L14_L6 : WalkFn "walk_path__L14_L6" 14 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 985) (by decide +kernel) rfl, rfl, wpBody_L14_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L7` is its template. -/
theorem wpFn_L14_L7 : WalkFn "walk_path__L14_L7" 14 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 958) (by decide +kernel) rfl, rfl, wpBody_L14_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L8` is its template. -/
theorem wpFn_L14_L8 : WalkFn "walk_path__L14_L8" 14 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1024) (by decide +kernel) rfl, rfl, wpBody_L14_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L4` is its template. -/
theorem wpFn_L15_L4 : WalkFn "walk_path__L15_L4" 15 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1031) (by decide +kernel) rfl, rfl, wpBody_L15_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L5` is its template. -/
theorem wpFn_L15_L5 : WalkFn "walk_path__L15_L5" 15 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1025) (by decide +kernel) rfl, rfl, wpBody_L15_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L6` is its template. -/
theorem wpFn_L15_L6 : WalkFn "walk_path__L15_L6" 15 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 988) (by decide +kernel) rfl, rfl, wpBody_L15_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L7` is its template. -/
theorem wpFn_L15_L7 : WalkFn "walk_path__L15_L7" 15 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 961) (by decide +kernel) rfl, rfl, wpBody_L15_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L8` is its template. -/
theorem wpFn_L15_L8 : WalkFn "walk_path__L15_L8" 15 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1026) (by decide +kernel) rfl, rfl, wpBody_L15_L8⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L4` is its template. -/
theorem wpFn_L16_L4 : WalkFn "walk_path__L16_L4" 16 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1030) (by decide +kernel) rfl, rfl, wpBody_L16_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L5` is its template. -/
theorem wpFn_L16_L5 : WalkFn "walk_path__L16_L5" 16 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1027) (by decide +kernel) rfl, rfl, wpBody_L16_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L6` is its template. -/
theorem wpFn_L16_L6 : WalkFn "walk_path__L16_L6" 16 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 991) (by decide +kernel) rfl, rfl, wpBody_L16_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L7` is its template. -/
theorem wpFn_L16_L7 : WalkFn "walk_path__L16_L7" 16 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 964) (by decide +kernel) rfl, rfl, wpBody_L16_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L4` is its template. -/
theorem wpFn_L17_L4 : WalkFn "walk_path__L17_L4" 17 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1033) (by decide +kernel) rfl, rfl, wpBody_L17_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L5` is its template. -/
theorem wpFn_L17_L5 : WalkFn "walk_path__L17_L5" 17 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1029) (by decide +kernel) rfl, rfl, wpBody_L17_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L6` is its template. -/
theorem wpFn_L17_L6 : WalkFn "walk_path__L17_L6" 17 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 994) (by decide +kernel) rfl, rfl, wpBody_L17_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L7` is its template. -/
theorem wpFn_L17_L7 : WalkFn "walk_path__L17_L7" 17 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 967) (by decide +kernel) rfl, rfl, wpBody_L17_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4` is its template. -/
theorem wpFn_L18_L4 : WalkFn "walk_path__L18_L4" 18 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1036) (by decide +kernel) rfl, rfl, wpBody_L18_L4⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5` is its template. -/
theorem wpFn_L18_L5 : WalkFn "walk_path__L18_L5" 18 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1032) (by decide +kernel) rfl, rfl, wpBody_L18_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6` is its template. -/
theorem wpFn_L18_L6 : WalkFn "walk_path__L18_L6" 18 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 997) (by decide +kernel) rfl, rfl, wpBody_L18_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7` is its template. -/
theorem wpFn_L18_L7 : WalkFn "walk_path__L18_L7" 18 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 979) (by decide +kernel) rfl, rfl, wpBody_L18_L7⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L5` is its template. -/
theorem wpFn_L19_L5 : WalkFn "walk_path__L19_L5" 19 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1034) (by decide +kernel) rfl, rfl, wpBody_L19_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L6` is its template. -/
theorem wpFn_L19_L6 : WalkFn "walk_path__L19_L6" 19 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1000) (by decide +kernel) rfl, rfl, wpBody_L19_L6⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L5` is its template. -/
theorem wpFn_L20_L5 : WalkFn "walk_path__L20_L5" 20 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1035) (by decide +kernel) rfl, rfl, wpBody_L20_L5⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L6` is its template. -/
theorem wpFn_L20_L6 : WalkFn "walk_path__L20_L6" 20 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1004) (by decide +kernel) rfl, rfl, wpBody_L20_L6⟩

/-- **Every deployed `walk_path` is its template.** -/
theorem walkFn_all : ∀ p ∈ walkPathNames, WalkFn p.2.2 p.1 p.2.1 := by
  intro p hp
  simp only [walkPathNames, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [wpFn_L14_L4, wpFn_L15_L4, wpFn_L16_L4, wpFn_L17_L4, wpFn_L18_L4, wpFn_L10_L5, wpFn_L11_L5, wpFn_L12_L5, wpFn_L13_L5, wpFn_L14_L5, wpFn_L15_L5, wpFn_L16_L5, wpFn_L17_L5, wpFn_L18_L5, wpFn_L19_L5, wpFn_L20_L5, wpFn_L9_L5, wpFn_L10_L6, wpFn_L11_L6, wpFn_L12_L6, wpFn_L13_L6, wpFn_L14_L6, wpFn_L15_L6, wpFn_L16_L6, wpFn_L17_L6, wpFn_L18_L6, wpFn_L19_L6, wpFn_L20_L6, wpFn_L11_L7, wpFn_L12_L7, wpFn_L13_L7, wpFn_L14_L7, wpFn_L15_L7, wpFn_L16_L7, wpFn_L17_L7, wpFn_L18_L7, wpFn_L10_L8, wpFn_L11_L8, wpFn_L12_L8, wpFn_L13_L8, wpFn_L14_L8, wpFn_L15_L8, wpFn_L9_L8]

end
end LeanVM.Guest.B1
