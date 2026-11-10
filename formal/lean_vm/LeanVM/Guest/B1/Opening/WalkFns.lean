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
/-- `walk_path__L14_L8` is its template. -/
theorem wpFn_878 : WalkFn "walk_path__L14_L8" 14 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 878) (by decide +kernel) rfl, rfl, wpBody_878⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L8` is its template. -/
theorem wpFn_885 : WalkFn "walk_path__L15_L8" 15 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 885) (by decide +kernel) rfl, rfl, wpBody_885⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L7` is its template. -/
theorem wpFn_919 : WalkFn "walk_path__L12_L7" 12 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1728) (by decide +kernel) rfl, rfl, wpBody_919⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L7` is its template. -/
theorem wpFn_921 : WalkFn "walk_path__L13_L7" 13 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 921) (by decide +kernel) rfl, rfl, wpBody_921⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L7` is its template. -/
theorem wpFn_923 : WalkFn "walk_path__L14_L7" 14 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 923) (by decide +kernel) rfl, rfl, wpBody_923⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L7` is its template. -/
theorem wpFn_925 : WalkFn "walk_path__L15_L7" 15 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 925) (by decide +kernel) rfl, rfl, wpBody_925⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L7` is its template. -/
theorem wpFn_927 : WalkFn "walk_path__L16_L7" 16 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 927) (by decide +kernel) rfl, rfl, wpBody_927⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L7` is its template. -/
theorem wpFn_929 : WalkFn "walk_path__L17_L7" 17 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 929) (by decide +kernel) rfl, rfl, wpBody_929⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L7` is its template. -/
theorem wpFn_932 : WalkFn "walk_path__L18_L7" 18 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 1769) (by decide +kernel) rfl, rfl, wpBody_932⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L8` is its template. -/
theorem wpFn_955 : WalkFn "walk_path__L9_L8" 9 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 955) (by decide +kernel) rfl, rfl, wpBody_955⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L6` is its template. -/
theorem wpFn_956 : WalkFn "walk_path__L10_L6" 10 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 956) (by decide +kernel) rfl, rfl, wpBody_956⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L5` is its template. -/
theorem wpFn_957 : WalkFn "walk_path__L10_L5" 10 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 957) (by decide +kernel) rfl, rfl, wpBody_957⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L9_L5` is its template. -/
theorem wpFn_958 : WalkFn "walk_path__L9_L5" 9 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 958) (by decide +kernel) rfl, rfl, wpBody_958⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L10_L8` is its template. -/
theorem wpFn_959 : WalkFn "walk_path__L10_L8" 10 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 959) (by decide +kernel) rfl, rfl, wpBody_959⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L6` is its template. -/
theorem wpFn_960 : WalkFn "walk_path__L11_L6" 11 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 960) (by decide +kernel) rfl, rfl, wpBody_960⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L5` is its template. -/
theorem wpFn_961 : WalkFn "walk_path__L11_L5" 11 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 961) (by decide +kernel) rfl, rfl, wpBody_961⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L8` is its template. -/
theorem wpFn_962 : WalkFn "walk_path__L11_L8" 11 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 962) (by decide +kernel) rfl, rfl, wpBody_962⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L6` is its template. -/
theorem wpFn_963 : WalkFn "walk_path__L12_L6" 12 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1719) (by decide +kernel) rfl, rfl, wpBody_963⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L5` is its template. -/
theorem wpFn_964 : WalkFn "walk_path__L12_L5" 12 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1710) (by decide +kernel) rfl, rfl, wpBody_964⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L8` is its template. -/
theorem wpFn_965 : WalkFn "walk_path__L12_L8" 12 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 1801) (by decide +kernel) rfl, rfl, wpBody_965⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L6` is its template. -/
theorem wpFn_966 : WalkFn "walk_path__L13_L6" 13 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 966) (by decide +kernel) rfl, rfl, wpBody_966⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L5` is its template. -/
theorem wpFn_967 : WalkFn "walk_path__L13_L5" 13 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 967) (by decide +kernel) rfl, rfl, wpBody_967⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L8` is its template. -/
theorem wpFn_968 : WalkFn "walk_path__L13_L8" 13 8 :=
  ⟨_, Program.find?_of_indexOf? (j := 968) (by decide +kernel) rfl, rfl, wpBody_968⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L6` is its template. -/
theorem wpFn_969 : WalkFn "walk_path__L14_L6" 14 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 969) (by decide +kernel) rfl, rfl, wpBody_969⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L5` is its template. -/
theorem wpFn_970 : WalkFn "walk_path__L14_L5" 14 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 970) (by decide +kernel) rfl, rfl, wpBody_970⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L6` is its template. -/
theorem wpFn_971 : WalkFn "walk_path__L15_L6" 15 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 971) (by decide +kernel) rfl, rfl, wpBody_971⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L5` is its template. -/
theorem wpFn_972 : WalkFn "walk_path__L15_L5" 15 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl, rfl, wpBody_972⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L6` is its template. -/
theorem wpFn_973 : WalkFn "walk_path__L16_L6" 16 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 973) (by decide +kernel) rfl, rfl, wpBody_973⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L5` is its template. -/
theorem wpFn_974 : WalkFn "walk_path__L16_L5" 16 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 974) (by decide +kernel) rfl, rfl, wpBody_974⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L14_L4` is its template. -/
theorem wpFn_975 : WalkFn "walk_path__L14_L4" 14 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl, rfl, wpBody_975⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L11_L7` is its template. -/
theorem wpFn_976 : WalkFn "walk_path__L11_L7" 11 7 :=
  ⟨_, Program.find?_of_indexOf? (j := 976) (by decide +kernel) rfl, rfl, wpBody_976⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L12_L4` is its template. -/
theorem wpFn_977 : WalkFn "walk_path__L12_L4" 12 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1692) (by decide +kernel) rfl, rfl, wpBody_977⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L13_L4` is its template. -/
theorem wpFn_978 : WalkFn "walk_path__L13_L4" 13 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl, rfl, wpBody_978⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L15_L4` is its template. -/
theorem wpFn_979 : WalkFn "walk_path__L15_L4" 15 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 979) (by decide +kernel) rfl, rfl, wpBody_979⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L6` is its template. -/
theorem wpFn_980 : WalkFn "walk_path__L17_L6" 17 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 980) (by decide +kernel) rfl, rfl, wpBody_980⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L5` is its template. -/
theorem wpFn_981 : WalkFn "walk_path__L17_L5" 17 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 981) (by decide +kernel) rfl, rfl, wpBody_981⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L16_L4` is its template. -/
theorem wpFn_982 : WalkFn "walk_path__L16_L4" 16 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 982) (by decide +kernel) rfl, rfl, wpBody_982⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L6` is its template. -/
theorem wpFn_983 : WalkFn "walk_path__L18_L6" 18 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 1763) (by decide +kernel) rfl, rfl, wpBody_983⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L5` is its template. -/
theorem wpFn_984 : WalkFn "walk_path__L18_L5" 18 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 1757) (by decide +kernel) rfl, rfl, wpBody_984⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L17_L4` is its template. -/
theorem wpFn_985 : WalkFn "walk_path__L17_L4" 17 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 985) (by decide +kernel) rfl, rfl, wpBody_985⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L6` is its template. -/
theorem wpFn_986 : WalkFn "walk_path__L19_L6" 19 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 986) (by decide +kernel) rfl, rfl, wpBody_986⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L19_L5` is its template. -/
theorem wpFn_987 : WalkFn "walk_path__L19_L5" 19 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 987) (by decide +kernel) rfl, rfl, wpBody_987⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L6` is its template. -/
theorem wpFn_988 : WalkFn "walk_path__L20_L6" 20 6 :=
  ⟨_, Program.find?_of_indexOf? (j := 988) (by decide +kernel) rfl, rfl, wpBody_988⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L20_L5` is its template. -/
theorem wpFn_989 : WalkFn "walk_path__L20_L5" 20 5 :=
  ⟨_, Program.find?_of_indexOf? (j := 989) (by decide +kernel) rfl, rfl, wpBody_989⟩

set_option maxRecDepth 100000 in
/-- `walk_path__L18_L4` is its template. -/
theorem wpFn_990 : WalkFn "walk_path__L18_L4" 18 4 :=
  ⟨_, Program.find?_of_indexOf? (j := 1751) (by decide +kernel) rfl, rfl, wpBody_990⟩

end
end LeanVM.Guest.B1
