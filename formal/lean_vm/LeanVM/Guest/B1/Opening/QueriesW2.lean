/-
  LeanVM.Guest.B1.Opening.QueriesW2

  A quarter of `opening_queries`' specializations, sound with their queries named.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L3` is sound with its queries named. -/
theorem oqSpecW_1263 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L3" "__loop623" ⟨0, 16, 18, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1692)
    (Program.find?_of_indexOf? (j := 1263) (by decide +kernel) rfl) rfl oqBody_1263
    (Program.find?_of_indexOf? (j := 1695) (by decide +kernel) rfl) rfl oqBody_1695

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is sound with its queries named. -/
theorem oqSpecW_1298 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L8" "__loop624" ⟨1, 64, 12, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1750)
    (Program.find?_of_indexOf? (j := 1298) (by decide +kernel) rfl) rfl oqBody_1298
    (Program.find?_of_indexOf? (j := 1699) (by decide +kernel) rfl) rfl oqBody_1699

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1299 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L22_L4" "__loop625" ⟨1, 64, 18, 4⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1700)
    (Program.find?_of_indexOf? (j := 1299) (by decide +kernel) rfl) rfl oqBody_1299
    (Program.find?_of_indexOf? (j := 1701) (by decide +kernel) rfl) rfl oqBody_1701

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L23_L5` is sound with its queries named. -/
theorem oqSpecW_1300 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L23_L5" "__loop626" ⟨1, 64, 18, 5⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1706)
    (Program.find?_of_indexOf? (j := 1300) (by decide +kernel) rfl) rfl oqBody_1300
    (Program.find?_of_indexOf? (j := 1702) (by decide +kernel) rfl) rfl oqBody_1702

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is sound with its queries named. -/
theorem oqSpecW_1303 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L22_L4" "__loop627" ⟨0, 16, 18, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1700)
    (Program.find?_of_indexOf? (j := 1303) (by decide +kernel) rfl) rfl oqBody_1303
    (Program.find?_of_indexOf? (j := 1703) (by decide +kernel) rfl) rfl oqBody_1703

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L5` is sound with its queries named. -/
theorem oqSpecW_1337 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L23_L5" "__loop628" ⟨1, 64, 18, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1706)
    (Program.find?_of_indexOf? (j := 1337) (by decide +kernel) rfl) rfl oqBody_1337
    (Program.find?_of_indexOf? (j := 1707) (by decide +kernel) rfl) rfl oqBody_1707

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1338 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L24_L6" "__loop629" ⟨1, 64, 18, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1712)
    (Program.find?_of_indexOf? (j := 1338) (by decide +kernel) rfl) rfl oqBody_1338
    (Program.find?_of_indexOf? (j := 1708) (by decide +kernel) rfl) rfl oqBody_1708

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is sound with its queries named. -/
theorem oqSpecW_1341 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L23_L5" "__loop630" ⟨0, 16, 18, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1706)
    (Program.find?_of_indexOf? (j := 1341) (by decide +kernel) rfl) rfl oqBody_1341
    (Program.find?_of_indexOf? (j := 1709) (by decide +kernel) rfl) rfl oqBody_1709

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1375 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L24_L6" "__loop631" ⟨1, 64, 18, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1712)
    (Program.find?_of_indexOf? (j := 1375) (by decide +kernel) rfl) rfl oqBody_1375
    (Program.find?_of_indexOf? (j := 1713) (by decide +kernel) rfl) rfl oqBody_1713

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L25_L7` is sound with its queries named. -/
theorem oqSpecW_1376 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L25_L7" "__loop632" ⟨1, 64, 18, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1718)
    (Program.find?_of_indexOf? (j := 1376) (by decide +kernel) rfl) rfl oqBody_1376
    (Program.find?_of_indexOf? (j := 1714) (by decide +kernel) rfl) rfl oqBody_1714

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L24_L6` is sound with its queries named. -/
theorem oqSpecW_1380 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L24_L6" "__loop633" ⟨0, 16, 18, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1712)
    (Program.find?_of_indexOf? (j := 1380) (by decide +kernel) rfl) rfl oqBody_1380
    (Program.find?_of_indexOf? (j := 1715) (by decide +kernel) rfl) rfl oqBody_1715

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is sound with its queries named. -/
theorem oqSpecW_1412 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L25_L7" "__loop634" ⟨1, 64, 18, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1718)
    (Program.find?_of_indexOf? (j := 1412) (by decide +kernel) rfl) rfl oqBody_1412
    (Program.find?_of_indexOf? (j := 1719) (by decide +kernel) rfl) rfl oqBody_1719

end
end LeanVM.Guest.B1
