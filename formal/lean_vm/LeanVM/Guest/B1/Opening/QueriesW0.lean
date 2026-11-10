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
/-- `opening_queries__L1_L1_L64_L32_L14_L8` is sound with its queries named. -/
theorem oqSpecW_1109 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L14_L8" "__loop620" ⟨1, 64, 6, 8⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 6, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1689)
    (Program.find?_of_indexOf? (j := 1109) (by decide +kernel) rfl) rfl oqBody_1109
    (Program.find?_of_indexOf? (j := 1690) (by decide +kernel) rfl) rfl oqBody_1690

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L13_L7` is sound with its queries named. -/
theorem oqSpecW_1121 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L13_L7" "__loop624" ⟨0, 16, 6, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1798)
    (Program.find?_of_indexOf? (j := 1121) (by decide +kernel) rfl) rfl oqBody_1121
    (Program.find?_of_indexOf? (j := 1697) (by decide +kernel) rfl) rfl oqBody_1697

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L12_L6` is sound with its queries named. -/
theorem oqSpecW_1131 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L12_L6" "__loop628" ⟨0, 16, 6, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 6, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1800)
    (Program.find?_of_indexOf? (j := 1131) (by decide +kernel) rfl) rfl oqBody_1131
    (Program.find?_of_indexOf? (j := 1702) (by decide +kernel) rfl) rfl oqBody_1702

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1158 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L18_L6" "__loop632" ⟨1, 64, 12, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1719)
    (Program.find?_of_indexOf? (j := 1158) (by decide +kernel) rfl) rfl oqBody_1158
    (Program.find?_of_indexOf? (j := 1712) (by decide +kernel) rfl) rfl oqBody_1712

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L6` is sound with its queries named. -/
theorem oqSpecW_1203 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L6" "__loop636" ⟨0, 16, 12, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 12, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1719)
    (Program.find?_of_indexOf? (j := 1203) (by decide +kernel) rfl) rfl oqBody_1203
    (Program.find?_of_indexOf? (j := 1722) (by decide +kernel) rfl) rfl oqBody_1722

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L2` is sound with its queries named. -/
theorem oqSpecW_1273 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L20_L2" "__loop640" ⟨1, 64, 18, 2⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1737)
    (Program.find?_of_indexOf? (j := 1273) (by decide +kernel) rfl) rfl oqBody_1273
    (Program.find?_of_indexOf? (j := 1738) (by decide +kernel) rfl) rfl oqBody_1738

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1307 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L4" "__loop644" ⟨1, 64, 18, 4⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1751)
    (Program.find?_of_indexOf? (j := 1307) (by decide +kernel) rfl) rfl oqBody_1307
    (Program.find?_of_indexOf? (j := 1745) (by decide +kernel) rfl) rfl oqBody_1745

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5` is sound with its queries named. -/
theorem oqSpecW_1347 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L23_L5" "__loop648" ⟨1, 64, 18, 5⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1757)
    (Program.find?_of_indexOf? (j := 1347) (by decide +kernel) rfl) rfl oqBody_1347
    (Program.find?_of_indexOf? (j := 1753) (by decide +kernel) rfl) rfl oqBody_1753

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is sound with its queries named. -/
theorem oqSpecW_1388 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L23_L5" "__loop652" ⟨0, 16, 18, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1757)
    (Program.find?_of_indexOf? (j := 1388) (by decide +kernel) rfl) rfl oqBody_1388
    (Program.find?_of_indexOf? (j := 1760) (by decide +kernel) rfl) rfl oqBody_1760

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is sound with its queries named. -/
theorem oqSpecW_1459 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L25_L7" "__loop656" ⟨1, 64, 18, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1769)
    (Program.find?_of_indexOf? (j := 1459) (by decide +kernel) rfl) rfl oqBody_1459
    (Program.find?_of_indexOf? (j := 1770) (by decide +kernel) rfl) rfl oqBody_1770

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3` is sound with its queries named. -/
theorem oqSpecW_1502 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L27_L3" "__loop660" ⟨1, 64, 24, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1777)
    (Program.find?_of_indexOf? (j := 1502) (by decide +kernel) rfl) rfl oqBody_1502
    (Program.find?_of_indexOf? (j := 1778) (by decide +kernel) rfl) rfl oqBody_1778

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8` is sound with its queries named. -/
theorem oqSpecW_1592 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L26_L8" "__loop664" ⟨1, 64, 18, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1802)
    (Program.find?_of_indexOf? (j := 1592) (by decide +kernel) rfl) rfl oqBody_1592
    (Program.find?_of_indexOf? (j := 1788) (by decide +kernel) rfl) rfl oqBody_1788

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5` is sound with its queries named. -/
theorem oqSpecW_1643 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L29_L5" "__loop668" ⟨0, 16, 24, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1789)
    (Program.find?_of_indexOf? (j := 1643) (by decide +kernel) rfl) rfl oqBody_1643
    (Program.find?_of_indexOf? (j := 1796) (by decide +kernel) rfl) rfl oqBody_1796

end
end LeanVM.Guest.B1
