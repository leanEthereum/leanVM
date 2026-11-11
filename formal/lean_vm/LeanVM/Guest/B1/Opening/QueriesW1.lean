/-
  LeanVM.Guest.B1.Opening.QueriesW1

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1143 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L17_L5" "__loop520" ⟨1, 64, 12, 5⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 1036) (by decide +kernel) rfl) rfl oqBody_1143
    (Program.find?_of_indexOf? (j := 1460) (by decide +kernel) rfl) rfl oqBody_1664

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1144 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L18_L6" "__loop521" ⟨1, 64, 12, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 1037) (by decide +kernel) rfl) rfl oqBody_1144
    (Program.find?_of_indexOf? (j := 1462) (by decide +kernel) rfl) rfl oqBody_1666

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1145 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L7" "__loop522" ⟨1, 64, 12, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1038) (by decide +kernel) rfl) rfl oqBody_1145
    (Program.find?_of_indexOf? (j := 1463) (by decide +kernel) rfl) rfl oqBody_1667

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1149 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L6" "__loop523" ⟨0, 16, 12, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 1042) (by decide +kernel) rfl) rfl oqBody_1149
    (Program.find?_of_indexOf? (j := 1464) (by decide +kernel) rfl) rfl oqBody_1668

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1182 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L19_L7" "__loop524" ⟨1, 64, 12, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1075) (by decide +kernel) rfl) rfl oqBody_1182
    (Program.find?_of_indexOf? (j := 1471) (by decide +kernel) rfl) rfl oqBody_1675

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1183 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L2" "__loop525" ⟨1, 64, 18, 2⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1076) (by decide +kernel) rfl) rfl oqBody_1183
    (Program.find?_of_indexOf? (j := 1472) (by decide +kernel) rfl) rfl oqBody_1676

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1187 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L7" "__loop526" ⟨0, 16, 12, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1080) (by decide +kernel) rfl) rfl oqBody_1187
    (Program.find?_of_indexOf? (j := 1473) (by decide +kernel) rfl) rfl oqBody_1677

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1220 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L20_L2" "__loop527" ⟨1, 64, 18, 2⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1113) (by decide +kernel) rfl) rfl oqBody_1220
    (Program.find?_of_indexOf? (j := 1480) (by decide +kernel) rfl) rfl oqBody_1684

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1221 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L3" "__loop528" ⟨1, 64, 18, 3⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1114) (by decide +kernel) rfl) rfl oqBody_1221
    (Program.find?_of_indexOf? (j := 1481) (by decide +kernel) rfl) rfl oqBody_1685

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1225 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L2" "__loop529" ⟨0, 16, 18, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1118) (by decide +kernel) rfl) rfl oqBody_1225
    (Program.find?_of_indexOf? (j := 1482) (by decide +kernel) rfl) rfl oqBody_1686

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1258 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L21_L3" "__loop530" ⟨1, 64, 18, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1151) (by decide +kernel) rfl) rfl oqBody_1258
    (Program.find?_of_indexOf? (j := 1489) (by decide +kernel) rfl) rfl oqBody_1693

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1259 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L4" "__loop531" ⟨1, 64, 18, 4⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1700)
    (Program.find?_of_indexOf? (j := 1152) (by decide +kernel) rfl) rfl oqBody_1259
    (Program.find?_of_indexOf? (j := 1490) (by decide +kernel) rfl) rfl oqBody_1694

end
end LeanVM.Guest.B1
