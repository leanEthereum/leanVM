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
/-- `opening_queries__L0_L0_L4_L16_L14_L5_L4_L39_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_496 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L14_L5_L4_L39_L20_L5_L1" "__loop343" (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 14, 5, 4, 39, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L9_L5)
    (Program.find?_of_indexOf? (j := 496) (by decide +kernel) rfl) rfl oqBody_496
    (Program.find?_of_indexOf? (j := 924) (by decide +kernel) rfl) rfl oqLoopBody_496

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_515 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L5_L5_L120_L36_L6_L1" "__loop347" (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 5, 5, 120, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L5)
    (Program.find?_of_indexOf? (j := 515) (by decide +kernel) rfl) rfl oqBody_515
    (Program.find?_of_indexOf? (j := 928) (by decide +kernel) rfl) rfl oqLoopBody_515

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_535 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L5_L2_L208_L8_L3_L1" "__loop351" (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 5, 2, 208, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L5)
    (Program.find?_of_indexOf? (j := 535) (by decide +kernel) rfl) rfl oqBody_535
    (Program.find?_of_indexOf? (j := 932) (by decide +kernel) rfl) rfl oqLoopBody_535

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_557 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L5_L3_L290_L12_L4_L1" "__loop355" (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 5, 3, 290, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L5)
    (Program.find?_of_indexOf? (j := 557) (by decide +kernel) rfl) rfl oqBody_557
    (Program.find?_of_indexOf? (j := 936) (by decide +kernel) rfl) rfl oqLoopBody_557

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_575 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L4_L372_L20_L5_L1" "__loop359" (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 4, 372, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 575) (by decide +kernel) rfl) rfl oqBody_575
    (Program.find?_of_indexOf? (j := 940) (by decide +kernel) rfl) rfl oqLoopBody_575

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_592 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L5_L5_L454_L36_L6_L1" "__loop363" (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 5, 5, 454, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L5)
    (Program.find?_of_indexOf? (j := 592) (by decide +kernel) rfl) rfl oqBody_592
    (Program.find?_of_indexOf? (j := 944) (by decide +kernel) rfl) rfl oqLoopBody_592

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_611 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L4_L2_L543_L8_L3_L1" "__loop367" (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 4, 2, 543, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L4)
    (Program.find?_of_indexOf? (j := 611) (by decide +kernel) rfl) rfl oqBody_611
    (Program.find?_of_indexOf? (j := 948) (by decide +kernel) rfl) rfl oqLoopBody_611

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_634 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L5_L5_L666_L36_L6_L1" "__loop371" (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 5, 5, 666, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L5)
    (Program.find?_of_indexOf? (j := 634) (by decide +kernel) rfl) rfl oqBody_634
    (Program.find?_of_indexOf? (j := 954) (by decide +kernel) rfl) rfl oqLoopBody_634

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_657 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L3_L836_L12_L4_L1" "__loop375" (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 3, 836, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl) rfl oqBody_657
    (Program.find?_of_indexOf? (j := 960) (by decide +kernel) rfl) rfl oqLoopBody_657

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_681 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L5_L5_L1000_L36_L6_L1" "__loop379" (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 5, 5, 1000, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L5)
    (Program.find?_of_indexOf? (j := 681) (by decide +kernel) rfl) rfl oqBody_681
    (Program.find?_of_indexOf? (j := 966) (by decide +kernel) rfl) rfl oqLoopBody_681

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_698 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L4_L0_L0_L0_L0_L0" "__loop383" (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L4)
    (Program.find?_of_indexOf? (j := 698) (by decide +kernel) rfl) rfl oqBody_698
    (Program.find?_of_indexOf? (j := 971) (by decide +kernel) rfl) rfl oqLoopBody_698

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_728 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1" "__loop387" (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 728) (by decide +kernel) rfl) rfl oqBody_728
    (Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl) rfl oqLoopBody_728

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_765 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0" "__loop391" (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L7)
    (Program.find?_of_indexOf? (j := 765) (by decide +kernel) rfl) rfl oqBody_765
    (Program.find?_of_indexOf? (j := 980) (by decide +kernel) rfl) rfl oqLoopBody_765

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_777 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1" "__loop395" (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L4)
    (Program.find?_of_indexOf? (j := 777) (by decide +kernel) rfl) rfl oqBody_777
    (Program.find?_of_indexOf? (j := 984) (by decide +kernel) rfl) rfl oqLoopBody_777

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_797 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1" "__loop399" (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L5)
    (Program.find?_of_indexOf? (j := 797) (by decide +kernel) rfl) rfl oqBody_797
    (Program.find?_of_indexOf? (j := 990) (by decide +kernel) rfl) rfl oqLoopBody_797

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_818 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1" "__loop403" (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L4)
    (Program.find?_of_indexOf? (j := 818) (by decide +kernel) rfl) rfl oqBody_818
    (Program.find?_of_indexOf? (j := 996) (by decide +kernel) rfl) rfl oqLoopBody_818

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_839 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0" "__loop407" (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L19_L5)
    (Program.find?_of_indexOf? (j := 839) (by decide +kernel) rfl) rfl oqBody_839
    (Program.find?_of_indexOf? (j := 1002) (by decide +kernel) rfl) rfl oqLoopBody_839

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_858 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0" "__loop411" (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L4)
    (Program.find?_of_indexOf? (j := 858) (by decide +kernel) rfl) rfl oqBody_858
    (Program.find?_of_indexOf? (j := 1007) (by decide +kernel) rfl) rfl oqLoopBody_858

end
end LeanVM.Guest.B1
