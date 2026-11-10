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
/-- `opening_queries__L0_L1_L64_L32_L15_L3` is sound with its queries named. -/
theorem oqSpecW_1111 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L15_L3" "__loop621" ⟨1, 64, 12, 3⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1707)
    (Program.find?_of_indexOf? (j := 1111) (by decide +kernel) rfl) rfl oqBody_1111
    (Program.find?_of_indexOf? (j := 1691) (by decide +kernel) rfl) rfl oqBody_1691

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L2` is sound with its queries named. -/
theorem oqSpecW_1123 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L14_L2" "__loop625" ⟨0, 16, 12, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1799)
    (Program.find?_of_indexOf? (j := 1123) (by decide +kernel) rfl) rfl oqBody_1123
    (Program.find?_of_indexOf? (j := 1698) (by decide +kernel) rfl) rfl oqBody_1698

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L15_L3` is sound with its queries named. -/
theorem oqSpecW_1155 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L15_L3" "__loop629" ⟨1, 64, 12, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1707)
    (Program.find?_of_indexOf? (j := 1155) (by decide +kernel) rfl) rfl oqBody_1155
    (Program.find?_of_indexOf? (j := 1708) (by decide +kernel) rfl) rfl oqBody_1708

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L5` is sound with its queries named. -/
theorem oqSpecW_1162 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L5" "__loop633" ⟨0, 16, 12, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1710)
    (Program.find?_of_indexOf? (j := 1162) (by decide +kernel) rfl) rfl oqBody_1162
    (Program.find?_of_indexOf? (j := 1713) (by decide +kernel) rfl) rfl oqBody_1713

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_1235 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L19_L7" "__loop637" ⟨1, 64, 12, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1728)
    (Program.find?_of_indexOf? (j := 1235) (by decide +kernel) rfl) rfl oqBody_1235
    (Program.find?_of_indexOf? (j := 1729) (by decide +kernel) rfl) rfl oqBody_1729

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1274 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L3" "__loop641" ⟨1, 64, 18, 3⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1743)
    (Program.find?_of_indexOf? (j := 1274) (by decide +kernel) rfl) rfl oqBody_1274
    (Program.find?_of_indexOf? (j := 1739) (by decide +kernel) rfl) rfl oqBody_1739

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1311 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L3" "__loop645" ⟨0, 16, 18, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1743)
    (Program.find?_of_indexOf? (j := 1311) (by decide +kernel) rfl) rfl oqBody_1311
    (Program.find?_of_indexOf? (j := 1746) (by decide +kernel) rfl) rfl oqBody_1746

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1350 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L22_L4" "__loop649" ⟨0, 16, 18, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1751)
    (Program.find?_of_indexOf? (j := 1350) (by decide +kernel) rfl) rfl oqBody_1350
    (Program.find?_of_indexOf? (j := 1754) (by decide +kernel) rfl) rfl oqBody_1754

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1422 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L24_L6" "__loop653" ⟨1, 64, 18, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1763)
    (Program.find?_of_indexOf? (j := 1422) (by decide +kernel) rfl) rfl oqBody_1422
    (Program.find?_of_indexOf? (j := 1764) (by decide +kernel) rfl) rfl oqBody_1764

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1460 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L26_L2" "__loop657" ⟨1, 64, 24, 2⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1775)
    (Program.find?_of_indexOf? (j := 1460) (by decide +kernel) rfl) rfl oqBody_1460
    (Program.find?_of_indexOf? (j := 1771) (by decide +kernel) rfl) rfl oqBody_1771

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1506 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L26_L2" "__loop661" ⟨0, 16, 24, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1775)
    (Program.find?_of_indexOf? (j := 1506) (by decide +kernel) rfl) rfl oqBody_1506
    (Program.find?_of_indexOf? (j := 1779) (by decide +kernel) rfl) rfl oqBody_1779

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5` is sound with its queries named. -/
theorem oqSpecW_1593 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L29_L5" "__loop665" ⟨1, 64, 24, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1789)
    (Program.find?_of_indexOf? (j := 1593) (by decide +kernel) rfl) rfl oqBody_1593
    (Program.find?_of_indexOf? (j := 1790) (by decide +kernel) rfl) rfl oqBody_1790

end
end LeanVM.Guest.B1
