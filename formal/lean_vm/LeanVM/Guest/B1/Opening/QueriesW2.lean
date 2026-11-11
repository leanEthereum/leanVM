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
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_492 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L5_L0_L0_L0_L0_L0" "__loop342" (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L5)
    (Program.find?_of_indexOf? (j := 492) (by decide +kernel) rfl) rfl oqBody_492
    (Program.find?_of_indexOf? (j := 922) (by decide +kernel) rfl) rfl oqLoopBody_492

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_512 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L5_L0_L0_L0_L0_L0" "__loop346" (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L5)
    (Program.find?_of_indexOf? (j := 512) (by decide +kernel) rfl) rfl oqBody_512
    (Program.find?_of_indexOf? (j := 926) (by decide +kernel) rfl) rfl oqLoopBody_512

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_531 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0" "__loop350" (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 531) (by decide +kernel) rfl) rfl oqBody_531
    (Program.find?_of_indexOf? (j := 930) (by decide +kernel) rfl) rfl oqLoopBody_531

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_552 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L5_L0_L0_L0_L0_L0" "__loop354" (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L5)
    (Program.find?_of_indexOf? (j := 552) (by decide +kernel) rfl) rfl oqBody_552
    (Program.find?_of_indexOf? (j := 934) (by decide +kernel) rfl) rfl oqLoopBody_552

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_572 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L5_L0_L0_L0_L0_L0" "__loop358" (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L5)
    (Program.find?_of_indexOf? (j := 572) (by decide +kernel) rfl) rfl oqBody_572
    (Program.find?_of_indexOf? (j := 938) (by decide +kernel) rfl) rfl oqLoopBody_572

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_589 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L5_L0_L0_L0_L0_L0" "__loop362" (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L5)
    (Program.find?_of_indexOf? (j := 589) (by decide +kernel) rfl) rfl oqBody_589
    (Program.find?_of_indexOf? (j := 942) (by decide +kernel) rfl) rfl oqLoopBody_589

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_605 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L21_L5_L0_L0_L0_L0_L0" "__loop366" (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 21, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L5)
    (Program.find?_of_indexOf? (j := 605) (by decide +kernel) rfl) rfl oqBody_605
    (Program.find?_of_indexOf? (j := 946) (by decide +kernel) rfl) rfl oqLoopBody_605

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_630 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0" "__loop370" (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L7)
    (Program.find?_of_indexOf? (j := 630) (by decide +kernel) rfl) rfl oqBody_630
    (Program.find?_of_indexOf? (j := 952) (by decide +kernel) rfl) rfl oqLoopBody_630

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_652 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L21_L7_L0_L0_L0_L0_L0" "__loop374" (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 21, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L7)
    (Program.find?_of_indexOf? (j := 652) (by decide +kernel) rfl) rfl oqBody_652
    (Program.find?_of_indexOf? (j := 958) (by decide +kernel) rfl) rfl oqLoopBody_652

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_676 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L23_L7_L0_L0_L0_L0_L0" "__loop378" (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 23, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L7)
    (Program.find?_of_indexOf? (j := 676) (by decide +kernel) rfl) rfl oqBody_676
    (Program.find?_of_indexOf? (j := 964) (by decide +kernel) rfl) rfl oqLoopBody_676

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_694 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L5_L0_L0_L0_L0_L0" "__loop382" (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L5)
    (Program.find?_of_indexOf? (j := 694) (by decide +kernel) rfl) rfl oqBody_694
    (Program.find?_of_indexOf? (j := 969) (by decide +kernel) rfl) rfl oqLoopBody_694

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_726 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L2_L1300_L8_L3_L1" "__loop386" (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 2, 1300, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 726) (by decide +kernel) rfl) rfl oqBody_726
    (Program.find?_of_indexOf? (j := 973) (by decide +kernel) rfl) rfl oqLoopBody_726

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_764 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0" "__loop390" (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L7)
    (Program.find?_of_indexOf? (j := 764) (by decide +kernel) rfl) rfl oqBody_764
    (Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl) rfl oqLoopBody_764

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_776 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L4_L2_L1635_L8_L3_L1" "__loop394" (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 4, 2, 1635, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L4)
    (Program.find?_of_indexOf? (j := 776) (by decide +kernel) rfl) rfl oqBody_776
    (Program.find?_of_indexOf? (j := 982) (by decide +kernel) rfl) rfl oqLoopBody_776

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_796 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L5_L5_L1758_L36_L6_L1" "__loop398" (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 5, 5, 1758, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L5)
    (Program.find?_of_indexOf? (j := 796) (by decide +kernel) rfl) rfl oqBody_796
    (Program.find?_of_indexOf? (j := 988) (by decide +kernel) rfl) rfl oqLoopBody_796

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_817 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L4_L3_L1928_L12_L4_L1" "__loop402" (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 4, 3, 1928, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L4)
    (Program.find?_of_indexOf? (j := 817) (by decide +kernel) rfl) rfl oqBody_817
    (Program.find?_of_indexOf? (j := 994) (by decide +kernel) rfl) rfl oqLoopBody_817

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_838 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L24_L5_L0_L0_L0_L0_L0" "__loop406" (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 24, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L19_L5)
    (Program.find?_of_indexOf? (j := 838) (by decide +kernel) rfl) rfl oqBody_838
    (Program.find?_of_indexOf? (j := 1000) (by decide +kernel) rfl) rfl oqLoopBody_838

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_857 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0" "__loop410" (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L4)
    (Program.find?_of_indexOf? (j := 857) (by decide +kernel) rfl) rfl oqBody_857
    (Program.find?_of_indexOf? (j := 1005) (by decide +kernel) rfl) rfl oqLoopBody_857

end
end LeanVM.Guest.B1
