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
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L15_L3" "__loop509" ⟨1, 64, 12, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1642)
    (Program.find?_of_indexOf? (j := 977) (by decide +kernel) rfl) rfl oqBody_1084
    (Program.find?_of_indexOf? (j := 1439) (by decide +kernel) rfl) rfl oqBody_1643

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1086 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L16_L4" "__loop510" ⟨1, 64, 12, 4⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 979) (by decide +kernel) rfl) rfl oqBody_1086
    (Program.find?_of_indexOf? (j := 1440) (by decide +kernel) rfl) rfl oqBody_1644

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1088 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L17_L5" "__loop511" ⟨1, 64, 12, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 981) (by decide +kernel) rfl) rfl oqBody_1088
    (Program.find?_of_indexOf? (j := 1442) (by decide +kernel) rfl) rfl oqBody_1646

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1090 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L18_L6" "__loop512" ⟨1, 64, 12, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 983) (by decide +kernel) rfl) rfl oqBody_1090
    (Program.find?_of_indexOf? (j := 1443) (by decide +kernel) rfl) rfl oqBody_1647

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2` is sound with its queries named. -/
theorem oqSpecW_1096 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L14_L2" "__loop513" ⟨0, 16, 12, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1747)
    (Program.find?_of_indexOf? (j := 989) (by decide +kernel) rfl) rfl oqBody_1096
    (Program.find?_of_indexOf? (j := 1445) (by decide +kernel) rfl) rfl oqBody_1649

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L15_L3` is sound with its queries named. -/
theorem oqSpecW_1097 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L15_L3" "__loop514" ⟨0, 16, 12, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1642)
    (Program.find?_of_indexOf? (j := 990) (by decide +kernel) rfl) rfl oqBody_1097
    (Program.find?_of_indexOf? (j := 1446) (by decide +kernel) rfl) rfl oqBody_1650

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1098 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L4" "__loop515" ⟨0, 16, 12, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 991) (by decide +kernel) rfl) rfl oqBody_1098
    (Program.find?_of_indexOf? (j := 1447) (by decide +kernel) rfl) rfl oqBody_1651

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1099 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L5" "__loop516" ⟨0, 16, 12, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 992) (by decide +kernel) rfl) rfl oqBody_1099
    (Program.find?_of_indexOf? (j := 1448) (by decide +kernel) rfl) rfl oqBody_1652

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7` is sound with its queries named. -/
theorem oqSpecW_1105 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L13_L7" "__loop517" ⟨0, 16, 6, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1748)
    (Program.find?_of_indexOf? (j := 998) (by decide +kernel) rfl) rfl oqBody_1105
    (Program.find?_of_indexOf? (j := 1450) (by decide +kernel) rfl) rfl oqBody_1654

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6` is sound with its queries named. -/
theorem oqSpecW_1110 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L12_L6" "__loop518" ⟨0, 16, 6, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1749)
    (Program.find?_of_indexOf? (j := 1003) (by decide +kernel) rfl) rfl oqBody_1110
    (Program.find?_of_indexOf? (j := 1452) (by decide +kernel) rfl) rfl oqBody_1656

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1142 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L16_L4" "__loop519" ⟨1, 64, 12, 4⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1662)
    (Program.find?_of_indexOf? (j := 1035) (by decide +kernel) rfl) rfl oqBody_1142
    (Program.find?_of_indexOf? (j := 1459) (by decide +kernel) rfl) rfl oqBody_1663

end
end LeanVM.Guest.B1
