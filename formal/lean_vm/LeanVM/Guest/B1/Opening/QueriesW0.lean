/-
  LeanVM.Guest.B1.Opening.QueriesW0

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3` is sound with its queries named. -/
theorem oqSpecW_1084 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L15_L3" "__loop600" ⟨1, 64, 12, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1642)
    (Program.find?_of_indexOf? (j := 1084) (by decide +kernel) rfl) rfl oqBody_1084
    (Program.find?_of_indexOf? (j := 1643) (by decide +kernel) rfl) rfl oqBody_1643

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1086 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L16_L4" "__loop601" ⟨1, 64, 12, 4⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 1086) (by decide +kernel) rfl) rfl oqBody_1086
    (Program.find?_of_indexOf? (j := 1644) (by decide +kernel) rfl) rfl oqBody_1644

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1088 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L17_L5" "__loop602" ⟨1, 64, 12, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 1088) (by decide +kernel) rfl) rfl oqBody_1088
    (Program.find?_of_indexOf? (j := 1646) (by decide +kernel) rfl) rfl oqBody_1646

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1090 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L18_L6" "__loop603" ⟨1, 64, 12, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 1090) (by decide +kernel) rfl) rfl oqBody_1090
    (Program.find?_of_indexOf? (j := 1647) (by decide +kernel) rfl) rfl oqBody_1647

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2` is sound with its queries named. -/
theorem oqSpecW_1096 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L14_L2" "__loop604" ⟨0, 16, 12, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1747)
    (Program.find?_of_indexOf? (j := 1096) (by decide +kernel) rfl) rfl oqBody_1096
    (Program.find?_of_indexOf? (j := 1649) (by decide +kernel) rfl) rfl oqBody_1649

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3` is sound with its queries named. -/
theorem oqSpecW_1097 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L15_L3" "__loop605" ⟨0, 16, 12, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1642)
    (Program.find?_of_indexOf? (j := 1097) (by decide +kernel) rfl) rfl oqBody_1097
    (Program.find?_of_indexOf? (j := 1650) (by decide +kernel) rfl) rfl oqBody_1650

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1098 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L4" "__loop606" ⟨0, 16, 12, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 1098) (by decide +kernel) rfl) rfl oqBody_1098
    (Program.find?_of_indexOf? (j := 1651) (by decide +kernel) rfl) rfl oqBody_1651

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1099 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L5" "__loop607" ⟨0, 16, 12, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 1099) (by decide +kernel) rfl) rfl oqBody_1099
    (Program.find?_of_indexOf? (j := 1652) (by decide +kernel) rfl) rfl oqBody_1652

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7` is sound with its queries named. -/
theorem oqSpecW_1105 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L13_L7" "__loop608" ⟨0, 16, 6, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1748)
    (Program.find?_of_indexOf? (j := 1105) (by decide +kernel) rfl) rfl oqBody_1105
    (Program.find?_of_indexOf? (j := 1654) (by decide +kernel) rfl) rfl oqBody_1654

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6` is sound with its queries named. -/
theorem oqSpecW_1110 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L12_L6" "__loop609" ⟨0, 16, 6, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1749)
    (Program.find?_of_indexOf? (j := 1110) (by decide +kernel) rfl) rfl oqBody_1110
    (Program.find?_of_indexOf? (j := 1656) (by decide +kernel) rfl) rfl oqBody_1656

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1142 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L16_L4" "__loop610" ⟨1, 64, 12, 4⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 1142) (by decide +kernel) rfl) rfl oqBody_1142
    (Program.find?_of_indexOf? (j := 1663) (by decide +kernel) rfl) rfl oqBody_1663

end
end LeanVM.Guest.B1
