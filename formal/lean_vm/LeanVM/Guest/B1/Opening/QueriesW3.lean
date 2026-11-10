/-
  LeanVM.Guest.B1.Opening.QueriesW3

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody3
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1115 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L17_L5" "__loop623" ⟨1, 64, 12, 5⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1710)
    (Program.find?_of_indexOf? (j := 1115) (by decide +kernel) rfl) rfl oqBody_1115
    (Program.find?_of_indexOf? (j := 1694) (by decide +kernel) rfl) rfl oqBody_1694

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L4` is sound with its queries named. -/
theorem oqSpecW_1125 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L4" "__loop627" ⟨0, 16, 12, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1125) (by decide +kernel) rfl) rfl oqBody_1125
    (Program.find?_of_indexOf? (j := 1700) (by decide +kernel) rfl) rfl oqBody_1700

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1157 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L17_L5" "__loop631" ⟨1, 64, 12, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1710)
    (Program.find?_of_indexOf? (j := 1157) (by decide +kernel) rfl) rfl oqBody_1157
    (Program.find?_of_indexOf? (j := 1711) (by decide +kernel) rfl) rfl oqBody_1711

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1199 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L7" "__loop635" ⟨1, 64, 12, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1728)
    (Program.find?_of_indexOf? (j := 1199) (by decide +kernel) rfl) rfl oqBody_1199
    (Program.find?_of_indexOf? (j := 1721) (by decide +kernel) rfl) rfl oqBody_1721

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1240 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L7" "__loop639" ⟨0, 16, 12, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1728)
    (Program.find?_of_indexOf? (j := 1240) (by decide +kernel) rfl) rfl oqBody_1240
    (Program.find?_of_indexOf? (j := 1731) (by decide +kernel) rfl) rfl oqBody_1731

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1306 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L21_L3" "__loop643" ⟨1, 64, 18, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1743)
    (Program.find?_of_indexOf? (j := 1306) (by decide +kernel) rfl) rfl oqBody_1306
    (Program.find?_of_indexOf? (j := 1744) (by decide +kernel) rfl) rfl oqBody_1744

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1346 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L22_L4" "__loop647" ⟨1, 64, 18, 4⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1751)
    (Program.find?_of_indexOf? (j := 1346) (by decide +kernel) rfl) rfl oqBody_1346
    (Program.find?_of_indexOf? (j := 1752) (by decide +kernel) rfl) rfl oqBody_1752

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1385 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L24_L6" "__loop651" ⟨1, 64, 18, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1763)
    (Program.find?_of_indexOf? (j := 1385) (by decide +kernel) rfl) rfl oqBody_1385
    (Program.find?_of_indexOf? (j := 1759) (by decide +kernel) rfl) rfl oqBody_1759

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1427 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L24_L6" "__loop655" ⟨0, 16, 18, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1763)
    (Program.find?_of_indexOf? (j := 1427) (by decide +kernel) rfl) rfl oqBody_1427
    (Program.find?_of_indexOf? (j := 1766) (by decide +kernel) rfl) rfl oqBody_1766

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1501 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L26_L2" "__loop659" ⟨1, 64, 24, 2⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1775)
    (Program.find?_of_indexOf? (j := 1501) (by decide +kernel) rfl) rfl oqBody_1501
    (Program.find?_of_indexOf? (j := 1776) (by decide +kernel) rfl) rfl oqBody_1776

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3` is sound with its queries named. -/
theorem oqSpecW_1549 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L27_L3" "__loop663" ⟨0, 16, 24, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1777)
    (Program.find?_of_indexOf? (j := 1549) (by decide +kernel) rfl) rfl oqBody_1549
    (Program.find?_of_indexOf? (j := 1784) (by decide +kernel) rfl) rfl oqBody_1784

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6` is sound with its queries named. -/
theorem oqSpecW_1639 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L30_L6" "__loop667" ⟨1, 64, 24, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1794)
    (Program.find?_of_indexOf? (j := 1639) (by decide +kernel) rfl) rfl oqBody_1639
    (Program.find?_of_indexOf? (j := 1795) (by decide +kernel) rfl) rfl oqBody_1795

end
end LeanVM.Guest.B1
