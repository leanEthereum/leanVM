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
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L17_L5" "__loop611" ⟨1, 64, 12, 5⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1645)
    (Program.find?_of_indexOf? (j := 1143) (by decide +kernel) rfl) rfl oqBody_1143
    (Program.find?_of_indexOf? (j := 1664) (by decide +kernel) rfl) rfl oqBody_1664

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1144 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L18_L6" "__loop612" ⟨1, 64, 12, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 1144) (by decide +kernel) rfl) rfl oqBody_1144
    (Program.find?_of_indexOf? (j := 1666) (by decide +kernel) rfl) rfl oqBody_1666

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1145 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L7" "__loop613" ⟨1, 64, 12, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1145) (by decide +kernel) rfl) rfl oqBody_1145
    (Program.find?_of_indexOf? (j := 1667) (by decide +kernel) rfl) rfl oqBody_1667

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1149 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L6" "__loop614" ⟨0, 16, 12, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1665)
    (Program.find?_of_indexOf? (j := 1149) (by decide +kernel) rfl) rfl oqBody_1149
    (Program.find?_of_indexOf? (j := 1668) (by decide +kernel) rfl) rfl oqBody_1668

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1182 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L19_L7" "__loop615" ⟨1, 64, 12, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1182) (by decide +kernel) rfl) rfl oqBody_1182
    (Program.find?_of_indexOf? (j := 1675) (by decide +kernel) rfl) rfl oqBody_1675

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1183 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L2" "__loop616" ⟨1, 64, 18, 2⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1183) (by decide +kernel) rfl) rfl oqBody_1183
    (Program.find?_of_indexOf? (j := 1676) (by decide +kernel) rfl) rfl oqBody_1676

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1187 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L7" "__loop617" ⟨0, 16, 12, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1674)
    (Program.find?_of_indexOf? (j := 1187) (by decide +kernel) rfl) rfl oqBody_1187
    (Program.find?_of_indexOf? (j := 1677) (by decide +kernel) rfl) rfl oqBody_1677

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1220 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L20_L2" "__loop618" ⟨1, 64, 18, 2⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1220) (by decide +kernel) rfl) rfl oqBody_1220
    (Program.find?_of_indexOf? (j := 1684) (by decide +kernel) rfl) rfl oqBody_1684

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1221 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L3" "__loop619" ⟨1, 64, 18, 3⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1221) (by decide +kernel) rfl) rfl oqBody_1221
    (Program.find?_of_indexOf? (j := 1685) (by decide +kernel) rfl) rfl oqBody_1685

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1225 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L2" "__loop620" ⟨0, 16, 18, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1683)
    (Program.find?_of_indexOf? (j := 1225) (by decide +kernel) rfl) rfl oqBody_1225
    (Program.find?_of_indexOf? (j := 1686) (by decide +kernel) rfl) rfl oqBody_1686

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1258 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L21_L3" "__loop621" ⟨1, 64, 18, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1258) (by decide +kernel) rfl) rfl oqBody_1258
    (Program.find?_of_indexOf? (j := 1693) (by decide +kernel) rfl) rfl oqBody_1693

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1259 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L4" "__loop622" ⟨1, 64, 18, 4⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1700)
    (Program.find?_of_indexOf? (j := 1259) (by decide +kernel) rfl) rfl oqBody_1259
    (Program.find?_of_indexOf? (j := 1694) (by decide +kernel) rfl) rfl oqBody_1694

end
end LeanVM.Guest.B1
