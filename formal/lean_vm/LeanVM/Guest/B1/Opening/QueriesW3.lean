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
/-- `opening_queries__L0_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_542 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L19_L7" "__loop392" ⟨1, 64, 12, 7⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_919)
    (Program.find?_of_indexOf? (j := 563) (by decide +kernel) rfl) rfl oqBody_542
    (Program.find?_of_indexOf? (j := 896) (by decide +kernel) rfl) rfl oqBody_860

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L20_L8` is sound with its queries named. -/
theorem oqSpecW_468 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L20_L8" "__loop378" ⟨1, 64, 12, 8⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_965)
    (Program.find?_of_indexOf? (j := 489) (by decide +kernel) rfl) rfl oqBody_468
    (Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl) rfl oqBody_843

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L22_L6` is sound with its queries named. -/
theorem oqSpecW_710 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L22_L6" "__loop416" ⟨1, 64, 16, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 16, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_973)
    (Program.find?_of_indexOf? (j := 731) (by decide +kernel) rfl) rfl oqBody_710
    (Program.find?_of_indexOf? (j := 942) (by decide +kernel) rfl) rfl oqBody_886

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L64_L32_L24_L6` is sound with its queries named. -/
theorem oqSpecW_732 :
    opening_queries_sound_w_Spec "opening_queries__L0_L1_L64_L32_L24_L6" "__loop418" ⟨1, 64, 18, 6⟩ 0 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 6⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 0 ≤ 1)) (hW := wpFn_983)
    (Program.find?_of_indexOf? (j := 753) (by decide +kernel) rfl) rfl oqBody_732
    (Program.find?_of_indexOf? (j := 944) (by decide +kernel) rfl) rfl oqBody_888

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L19_L7` is sound with its queries named. -/
theorem oqSpecW_614 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L19_L7" "__loop404" ⟨1, 64, 12, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 12, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_919)
    (Program.find?_of_indexOf? (j := 635) (by decide +kernel) rfl) rfl oqBody_614
    (Program.find?_of_indexOf? (j := 920) (by decide +kernel) rfl) rfl oqBody_873

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L22_L8` is sound with its queries named. -/
theorem oqSpecW_501 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L22_L8" "__loop384" ⟨1, 64, 14, 8⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 14, 8⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_878)
    (Program.find?_of_indexOf? (j := 522) (by decide +kernel) rfl) rfl oqBody_501
    (Program.find?_of_indexOf? (j := 879) (by decide +kernel) rfl) rfl oqBody_851

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L64_L32_L25_L7` is sound with its queries named. -/
theorem oqSpecW_676 :
    opening_queries_sound_w_Spec "opening_queries__L1_L1_L64_L32_L25_L7" "__loop410" ⟨1, 64, 18, 7⟩ 1 :=
  oqMain1_sound_w (s := ⟨1, 64, 18, 7⟩) (Or.inl ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hodd := (by decide : 1 ≤ 1)) (hW := wpFn_932)
    (Program.find?_of_indexOf? (j := 697) (by decide +kernel) rfl) rfl oqBody_676
    (Program.find?_of_indexOf? (j := 933) (by decide +kernel) rfl) rfl oqBody_880

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L16_L5` is sound with its queries named. -/
theorem oqSpecW_439 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L16_L5" "__loop374" ⟨0, 16, 11, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 11, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_961)
    (Program.find?_of_indexOf? (j := 460) (by decide +kernel) rfl) rfl oqBody_439
    (Program.find?_of_indexOf? (j := 858) (by decide +kernel) rfl) rfl oqBody_837

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L17_L6` is sound with its queries named. -/
theorem oqSpecW_436 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L17_L6" "__loop373" ⟨0, 16, 11, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 11, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_960)
    (Program.find?_of_indexOf? (j := 457) (by decide +kernel) rfl) rfl oqBody_436
    (Program.find?_of_indexOf? (j := 856) (by decide +kernel) rfl) rfl oqBody_836

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L19_L4` is sound with its queries named. -/
theorem oqSpecW_591 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L19_L4" "__loop399" ⟨0, 16, 15, 4⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 4⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_979)
    (Program.find?_of_indexOf? (j := 612) (by decide +kernel) rfl) rfl oqBody_591
    (Program.find?_of_indexOf? (j := 910) (by decide +kernel) rfl) rfl oqBody_867

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L20_L5` is sound with its queries named. -/
theorem oqSpecW_505 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L20_L5" "__loop386" ⟨0, 16, 15, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_972)
    (Program.find?_of_indexOf? (j := 526) (by decide +kernel) rfl) rfl oqBody_505
    (Program.find?_of_indexOf? (j := 883) (by decide +kernel) rfl) rfl oqBody_853

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L21_L6` is sound with its queries named. -/
theorem oqSpecW_503 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L21_L6" "__loop385" ⟨0, 16, 15, 6⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 15, 6⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_971)
    (Program.find?_of_indexOf? (j := 524) (by decide +kernel) rfl) rfl oqBody_503
    (Program.find?_of_indexOf? (j := 881) (by decide +kernel) rfl) rfl oqBody_852

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L23_L5` is sound with its queries named. -/
theorem oqSpecW_680 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L23_L5" "__loop412" ⟨0, 16, 18, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 18, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_984)
    (Program.find?_of_indexOf? (j := 701) (by decide +kernel) rfl) rfl oqBody_680
    (Program.find?_of_indexOf? (j := 937) (by decide +kernel) rfl) rfl oqBody_882

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L16_L24_L25_L5` is sound with its queries named. -/
theorem oqSpecW_757 :
    opening_queries_sound_w_Spec "opening_queries__L0_L0_L16_L24_L25_L5" "__loop422" ⟨0, 16, 20, 5⟩ 0 :=
  oqMain0_sound_w (s := ⟨0, 16, 20, 5⟩) (Or.inr ⟨rfl, rfl⟩) rfl (by decide) (by decide) (by decide) (hW := wpFn_989)
    (Program.find?_of_indexOf? (j := 778) (by decide +kernel) rfl) rfl oqBody_757
    (Program.find?_of_indexOf? (j := 952) (by decide +kernel) rfl) rfl oqBody_893

end
end LeanVM.Guest.B1
