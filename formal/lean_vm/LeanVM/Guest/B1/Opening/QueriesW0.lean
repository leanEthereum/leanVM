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
/-- `opening_queries__L0_L1_L64_L32_L17_L8` is sound with its queries named. -/
theorem oqSpecW_413 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L17_L8" "__loop103" ⟨1, 64, 9, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 9, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_955)
    (Program.find?_of_indexOf? (j := 434) (by decide +kernel) rfl) rfl oqBody_413
    (Program.find?_of_indexOf? (j := 1119) (by decide +kernel) rfl) rfl oqBody_827

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L19_L8` is sound with its queries named. -/
theorem oqSpecW_449 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L8" "__loop375" ⟨1, 64, 11, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 11, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_962)
    (Program.find?_of_indexOf? (j := 470) (by decide +kernel) rfl) rfl oqBody_449
    (Program.find?_of_indexOf? (j := 860) (by decide +kernel) rfl) rfl oqBody_839

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L21_L6` is sound with its queries named. -/
theorem oqSpecW_701 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L21_L6" "__loop110" ⟨1, 64, 15, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 15, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_971)
    (Program.find?_of_indexOf? (j := 722) (by decide +kernel) rfl) rfl oqBody_701
    (Program.find?_of_indexOf? (j := 1134) (by decide +kernel) rfl) rfl oqBody_885

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L7` is sound with its queries named. -/
theorem oqSpecW_575 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L7" "__loop397" ⟨1, 64, 15, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 15, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_925)
    (Program.find?_of_indexOf? (j := 596) (by decide +kernel) rfl) rfl oqBody_575
    (Program.find?_of_indexOf? (j := 906) (by decide +kernel) rfl) rfl oqBody_865

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L7` is sound with its queries named. -/
theorem oqSpecW_598 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L24_L7" "__loop400" ⟨1, 64, 17, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 17, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_929)
    (Program.find?_of_indexOf? (j := 619) (by decide +kernel) rfl) rfl oqBody_598
    (Program.find?_of_indexOf? (j := 912) (by decide +kernel) rfl) rfl oqBody_869

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L20_L7` is sound with its queries named. -/
theorem oqSpecW_623 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L20_L7" "__loop405" ⟨1, 64, 13, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 13, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_921)
    (Program.find?_of_indexOf? (j := 644) (by decide +kernel) rfl) rfl oqBody_623
    (Program.find?_of_indexOf? (j := 922) (by decide +kernel) rfl) rfl oqBody_874

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L23_L7` is sound with its queries named. -/
theorem oqSpecW_654 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L23_L7" "__loop408" ⟨1, 64, 16, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 16, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_927)
    (Program.find?_of_indexOf? (j := 675) (by decide +kernel) rfl) rfl oqBody_654
    (Program.find?_of_indexOf? (j := 928) (by decide +kernel) rfl) rfl oqBody_877

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L14_L5` is sound with its queries named. -/
theorem oqSpecW_425 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L14_L5" "__loop106" ⟨0, 16, 9, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 9, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_958)
    (Program.find?_of_indexOf? (j := 446) (by decide +kernel) rfl) rfl oqBody_425
    (Program.find?_of_indexOf? (j := 1128) (by decide +kernel) rfl) rfl oqBody_833

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L6` is sound with its queries named. -/
theorem oqSpecW_418 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L6" "__loop104" ⟨0, 16, 10, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 10, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_956)
    (Program.find?_of_indexOf? (j := 439) (by decide +kernel) rfl) rfl oqBody_418
    (Program.find?_of_indexOf? (j := 1126) (by decide +kernel) rfl) rfl oqBody_829

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L18_L4` is sound with its queries named. -/
theorem oqSpecW_524 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L18_L4" "__loop390" ⟨0, 16, 14, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 14, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_975)
    (Program.find?_of_indexOf? (j := 545) (by decide +kernel) rfl) rfl oqBody_524
    (Program.find?_of_indexOf? (j := 892) (by decide +kernel) rfl) rfl oqBody_858

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L5` is sound with its queries named. -/
theorem oqSpecW_491 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L5" "__loop383" ⟨0, 16, 14, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 14, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_970)
    (Program.find?_of_indexOf? (j := 512) (by decide +kernel) rfl) rfl oqBody_491
    (Program.find?_of_indexOf? (j := 876) (by decide +kernel) rfl) rfl oqBody_849

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L6` is sound with its queries named. -/
theorem oqSpecW_489 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L6" "__loop382" ⟨0, 16, 14, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 14, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_969)
    (Program.find?_of_indexOf? (j := 510) (by decide +kernel) rfl) rfl oqBody_489
    (Program.find?_of_indexOf? (j := 874) (by decide +kernel) rfl) rfl oqBody_848

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L22_L4` is sound with its queries named. -/
theorem oqSpecW_761 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L22_L4" "__loop643" ⟨0, 16, 18, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_990)
    (Program.find?_of_indexOf? (j := 1350) (by decide +kernel) rfl) rfl oqBody_761
    (Program.find?_of_indexOf? (j := 1744) (by decide +kernel) rfl) rfl oqBody_894

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L6` is sound with its queries named. -/
theorem oqSpecW_600 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L23_L6" "__loop401" ⟨0, 16, 17, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 17, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_980)
    (Program.find?_of_indexOf? (j := 621) (by decide +kernel) rfl) rfl oqBody_600
    (Program.find?_of_indexOf? (j := 914) (by decide +kernel) rfl) rfl oqBody_870

end
end LeanVM.Guest.B1
