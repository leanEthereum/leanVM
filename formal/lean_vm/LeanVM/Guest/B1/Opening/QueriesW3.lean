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
/-- `opening_queries__L0_L1_L64_L32_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1413 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L26_L2" "__loop635" ⟨1, 64, 24, 2⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1724)
    (Program.find?_of_indexOf? (j := 1413) (by decide +kernel) rfl) rfl oqBody_1413
    (Program.find?_of_indexOf? (j := 1720) (by decide +kernel) rfl) rfl oqBody_1720

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L7` is sound with its queries named. -/
theorem oqSpecW_1417 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L25_L7" "__loop636" ⟨0, 16, 18, 7⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 7⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1718)
    (Program.find?_of_indexOf? (j := 1417) (by decide +kernel) rfl) rfl oqBody_1417
    (Program.find?_of_indexOf? (j := 1721) (by decide +kernel) rfl) rfl oqBody_1721

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1454 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L26_L2" "__loop637" ⟨1, 64, 24, 2⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 2⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1724)
    (Program.find?_of_indexOf? (j := 1454) (by decide +kernel) rfl) rfl oqBody_1454
    (Program.find?_of_indexOf? (j := 1725) (by decide +kernel) rfl) rfl oqBody_1725

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L27_L3` is sound with its queries named. -/
theorem oqSpecW_1455 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L27_L3" "__loop638" ⟨1, 64, 24, 3⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 3⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1726)
    (Program.find?_of_indexOf? (j := 1455) (by decide +kernel) rfl) rfl oqBody_1455
    (Program.find?_of_indexOf? (j := 1727) (by decide +kernel) rfl) rfl oqBody_1727

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L26_L2` is sound with its queries named. -/
theorem oqSpecW_1459 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L26_L2" "__loop639" ⟨0, 16, 24, 2⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 2⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1724)
    (Program.find?_of_indexOf? (j := 1459) (by decide +kernel) rfl) rfl oqBody_1459
    (Program.find?_of_indexOf? (j := 1728) (by decide +kernel) rfl) rfl oqBody_1728

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L28_L4` is sound with its queries named. -/
theorem oqSpecW_1498 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L28_L4" "__loop640" ⟨1, 64, 24, 4⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 4⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1731)
    (Program.find?_of_indexOf? (j := 1498) (by decide +kernel) rfl) rfl oqBody_1498
    (Program.find?_of_indexOf? (j := 1732) (by decide +kernel) rfl) rfl oqBody_1732

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L27_L3` is sound with its queries named. -/
theorem oqSpecW_1502 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L27_L3" "__loop641" ⟨0, 16, 24, 3⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 3⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1726)
    (Program.find?_of_indexOf? (j := 1502) (by decide +kernel) rfl) rfl oqBody_1502
    (Program.find?_of_indexOf? (j := 1733) (by decide +kernel) rfl) rfl oqBody_1733

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L26_L8` is sound with its queries named. -/
theorem oqSpecW_1545 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L26_L8" "__loop642" ⟨1, 64, 18, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_1751)
    (Program.find?_of_indexOf? (j := 1545) (by decide +kernel) rfl) rfl oqBody_1545
    (Program.find?_of_indexOf? (j := 1737) (by decide +kernel) rfl) rfl oqBody_1737

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L29_L5` is sound with its queries named. -/
theorem oqSpecW_1546 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L29_L5" "__loop643" ⟨1, 64, 24, 5⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 5⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1738)
    (Program.find?_of_indexOf? (j := 1546) (by decide +kernel) rfl) rfl oqBody_1546
    (Program.find?_of_indexOf? (j := 1739) (by decide +kernel) rfl) rfl oqBody_1739

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L28_L4` is sound with its queries named. -/
theorem oqSpecW_1550 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L28_L4" "__loop644" ⟨0, 16, 24, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1731)
    (Program.find?_of_indexOf? (j := 1550) (by decide +kernel) rfl) rfl oqBody_1550
    (Program.find?_of_indexOf? (j := 1740) (by decide +kernel) rfl) rfl oqBody_1740

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L30_L6` is sound with its queries named. -/
theorem oqSpecW_1592 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L30_L6" "__loop645" ⟨1, 64, 24, 6⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 24, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_1743)
    (Program.find?_of_indexOf? (j := 1592) (by decide +kernel) rfl) rfl oqBody_1592
    (Program.find?_of_indexOf? (j := 1744) (by decide +kernel) rfl) rfl oqBody_1744

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L29_L5` is sound with its queries named. -/
theorem oqSpecW_1596 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L29_L5" "__loop646" ⟨0, 16, 24, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 24, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_1738)
    (Program.find?_of_indexOf? (j := 1596) (by decide +kernel) rfl) rfl oqBody_1596
    (Program.find?_of_indexOf? (j := 1745) (by decide +kernel) rfl) rfl oqBody_1745

end
end LeanVM.Guest.B1
