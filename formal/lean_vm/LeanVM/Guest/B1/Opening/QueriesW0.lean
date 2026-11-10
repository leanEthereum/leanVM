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
/-- `opening_queries__L0_L1_L6_L32_L17_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_482 : opening_queries_sound_w_Spec "opening_queries__L0_L1_L6_L32_L17_L8_L0_L0_L0_L0_L0" "__loop340" (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨0, 1, 6, 32, 17, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L9_L8)
    (Program.find?_of_indexOf? (j := 482) (by decide +kernel) rfl) rfl oqBody_482
    (Program.find?_of_indexOf? (j := 939) (by decide +kernel) rfl) rfl oqLoopBody_482

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_508 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L18_L8_L0_L0_L0_L0_L0" "__loop344" (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 18, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L8)
    (Program.find?_of_indexOf? (j := 508) (by decide +kernel) rfl) rfl oqBody_508
    (Program.find?_of_indexOf? (j := 944) (by decide +kernel) rfl) rfl oqLoopBody_508

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_530 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L19_L8_L0_L0_L0_L0_L0" "__loop348" (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 19, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L8)
    (Program.find?_of_indexOf? (j := 530) (by decide +kernel) rfl) rfl oqBody_530
    (Program.find?_of_indexOf? (j := 949) (by decide +kernel) rfl) rfl oqLoopBody_530

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_556 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0" "__loop352" (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L8)
    (Program.find?_of_indexOf? (j := 556) (by decide +kernel) rfl) rfl oqBody_556
    (Program.find?_of_indexOf? (j := 954) (by decide +kernel) rfl) rfl oqLoopBody_556

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_582 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L21_L8_L0_L0_L0_L0_L0" "__loop356" (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 21, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L8)
    (Program.find?_of_indexOf? (j := 582) (by decide +kernel) rfl) rfl oqBody_582
    (Program.find?_of_indexOf? (j := 959) (by decide +kernel) rfl) rfl oqLoopBody_582

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_600 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L22_L8_L0_L0_L0_L0_L0" "__loop360" (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 22, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L8)
    (Program.find?_of_indexOf? (j := 600) (by decide +kernel) rfl) rfl oqBody_600
    (Program.find?_of_indexOf? (j := 964) (by decide +kernel) rfl) rfl oqLoopBody_600

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L8_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_617 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L23_L8_L0_L0_L0_L0_L0" "__loop364" (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 23, 8, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L8)
    (Program.find?_of_indexOf? (j := 617) (by decide +kernel) rfl) rfl oqBody_617
    (Program.find?_of_indexOf? (j := 969) (by decide +kernel) rfl) rfl oqLoopBody_617

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_638 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L18_L7_L0_L0_L0_L0_L0" "__loop368" (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 18, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L7)
    (Program.find?_of_indexOf? (j := 638) (by decide +kernel) rfl) rfl oqBody_638
    (Program.find?_of_indexOf? (j := 974) (by decide +kernel) rfl) rfl oqLoopBody_638

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_658 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L20_L7_L0_L0_L0_L0_L0" "__loop372" (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 20, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L7)
    (Program.find?_of_indexOf? (j := 658) (by decide +kernel) rfl) rfl oqBody_658
    (Program.find?_of_indexOf? (j := 980) (by decide +kernel) rfl) rfl oqLoopBody_658

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_682 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L22_L7_L0_L0_L0_L0_L0" "__loop376" (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 22, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L7)
    (Program.find?_of_indexOf? (j := 682) (by decide +kernel) rfl) rfl oqBody_682
    (Program.find?_of_indexOf? (j := 986) (by decide +kernel) rfl) rfl oqLoopBody_682

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_706 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L24_L7_L0_L0_L0_L0_L0" "__loop380" (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 24, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L7)
    (Program.find?_of_indexOf? (j := 706) (by decide +kernel) rfl) rfl oqBody_706
    (Program.find?_of_indexOf? (j := 992) (by decide +kernel) rfl) rfl oqLoopBody_706

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_719 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L4_L2_L1089_L8_L3_L1" "__loop384" (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 4, 2, 1089, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L4)
    (Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl) rfl oqBody_719
    (Program.find?_of_indexOf? (j := 996) (by decide +kernel) rfl) rfl oqLoopBody_719

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_756 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L4_L3_L1382_L12_L4_L1" "__loop388" (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 4, 3, 1382, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L4)
    (Program.find?_of_indexOf? (j := 756) (by decide +kernel) rfl) rfl oqBody_756
    (Program.find?_of_indexOf? (j := 1000) (by decide +kernel) rfl) rfl oqLoopBody_756

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_786 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0" "__loop392" (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L6)
    (Program.find?_of_indexOf? (j := 786) (by decide +kernel) rfl) rfl oqBody_786
    (Program.find?_of_indexOf? (j := 1005) (by decide +kernel) rfl) rfl oqLoopBody_786

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_802 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L20_L6_L0_L0_L0_L0_L0" "__loop396" (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L6)
    (Program.find?_of_indexOf? (j := 802) (by decide +kernel) rfl) rfl oqBody_802
    (Program.find?_of_indexOf? (j := 1010) (by decide +kernel) rfl) rfl oqLoopBody_802

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_820 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L22_L6_L0_L0_L0_L0_L0" "__loop400" (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L6)
    (Program.find?_of_indexOf? (j := 820) (by decide +kernel) rfl) rfl oqBody_820
    (Program.find?_of_indexOf? (j := 1016) (by decide +kernel) rfl) rfl oqLoopBody_820

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_842 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0" "__loop404" (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L6)
    (Program.find?_of_indexOf? (j := 842) (by decide +kernel) rfl) rfl oqBody_842
    (Program.find?_of_indexOf? (j := 1022) (by decide +kernel) rfl) rfl oqLoopBody_842

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_861 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L21_L4_L5_L2092_L36_L6_L1" "__loop408" (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 21, 4, 5, 2092, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L4)
    (Program.find?_of_indexOf? (j := 861) (by decide +kernel) rfl) rfl oqBody_861
    (Program.find?_of_indexOf? (j := 1027) (by decide +kernel) rfl) rfl oqLoopBody_861

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_878 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L21_L4_L2_L2181_L8_L3_L1" "__loop412" (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 21, 4, 2, 2181, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L4)
    (Program.find?_of_indexOf? (j := 878) (by decide +kernel) rfl) rfl oqBody_878
    (Program.find?_of_indexOf? (j := 1032) (by decide +kernel) rfl) rfl oqLoopBody_878

end
end LeanVM.Guest.B1
