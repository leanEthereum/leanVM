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
/-- `opening_queries__L0_L0_L4_L16_L16_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_487 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L6_L0_L0_L0_L0_L0" "__loop341" (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L6)
    (Program.find?_of_indexOf? (j := 487) (by decide +kernel) rfl) rfl oqBody_487
    (Program.find?_of_indexOf? (j := 921) (by decide +kernel) rfl) rfl oqLoopBody_487

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_508 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L6_L0_L0_L0_L0_L0" "__loop345" (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L6)
    (Program.find?_of_indexOf? (j := 508) (by decide +kernel) rfl) rfl oqBody_508
    (Program.find?_of_indexOf? (j := 925) (by decide +kernel) rfl) rfl oqLoopBody_508

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_527 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0" "__loop349" (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L6)
    (Program.find?_of_indexOf? (j := 527) (by decide +kernel) rfl) rfl oqBody_527
    (Program.find?_of_indexOf? (j := 929) (by decide +kernel) rfl) rfl oqLoopBody_527

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_548 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L6_L0_L0_L0_L0_L0" "__loop353" (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L6)
    (Program.find?_of_indexOf? (j := 548) (by decide +kernel) rfl) rfl oqBody_548
    (Program.find?_of_indexOf? (j := 933) (by decide +kernel) rfl) rfl oqLoopBody_548

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_569 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L6_L0_L0_L0_L0_L0" "__loop357" (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L14_L6)
    (Program.find?_of_indexOf? (j := 569) (by decide +kernel) rfl) rfl oqBody_569
    (Program.find?_of_indexOf? (j := 937) (by decide +kernel) rfl) rfl oqLoopBody_569

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_586 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L21_L6_L0_L0_L0_L0_L0" "__loop361" (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L6)
    (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl) rfl oqBody_586
    (Program.find?_of_indexOf? (j := 941) (by decide +kernel) rfl) rfl oqLoopBody_586

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_602 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L6_L0_L0_L0_L0_L0" "__loop365" (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L6)
    (Program.find?_of_indexOf? (j := 602) (by decide +kernel) rfl) rfl oqBody_602
    (Program.find?_of_indexOf? (j := 945) (by decide +kernel) rfl) rfl oqLoopBody_602

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_624 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L5_L4_L585_L20_L5_L1" "__loop369" (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 5, 4, 585, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L10_L5)
    (Program.find?_of_indexOf? (j := 624) (by decide +kernel) rfl) rfl oqBody_624
    (Program.find?_of_indexOf? (j := 950) (by decide +kernel) rfl) rfl oqLoopBody_624

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_645 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L5_L2_L754_L8_L3_L1" "__loop373" (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 5, 2, 754, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L11_L5)
    (Program.find?_of_indexOf? (j := 645) (by decide +kernel) rfl) rfl oqBody_645
    (Program.find?_of_indexOf? (j := 956) (by decide +kernel) rfl) rfl oqLoopBody_645

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_669 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L18_L5_L4_L918_L20_L5_L1" "__loop377" (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 18, 5, 4, 918, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L13_L5)
    (Program.find?_of_indexOf? (j := 669) (by decide +kernel) rfl) rfl oqBody_669
    (Program.find?_of_indexOf? (j := 962) (by decide +kernel) rfl) rfl oqLoopBody_669

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_691 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L23_L6_L0_L0_L0_L0_L0" "__loop381" (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L6)
    (Program.find?_of_indexOf? (j := 691) (by decide +kernel) rfl) rfl oqBody_691
    (Program.find?_of_indexOf? (j := 968) (by decide +kernel) rfl) rfl oqLoopBody_691

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_717 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L5_L1212_L36_L6_L1" "__loop385" (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 5, 1212, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 717) (by decide +kernel) rfl) rfl oqBody_717
    (Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl) rfl oqLoopBody_717

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_757 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L4_L5_L1546_L36_L6_L1" "__loop389" (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 4, 5, 1546, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L16_L4)
    (Program.find?_of_indexOf? (j := 757) (by decide +kernel) rfl) rfl oqBody_757
    (Program.find?_of_indexOf? (j := 976) (by decide +kernel) rfl) rfl oqLoopBody_757

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_774 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L21_L4_L0_L0_L0_L0_L0" "__loop393" (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 21, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L4)
    (Program.find?_of_indexOf? (j := 774) (by decide +kernel) rfl) rfl oqBody_774
    (Program.find?_of_indexOf? (j := 981) (by decide +kernel) rfl) rfl oqLoopBody_774

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_792 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L21_L6_L0_L0_L0_L0_L0" "__loop397" (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 21, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L15_L6)
    (Program.find?_of_indexOf? (j := 792) (by decide +kernel) rfl) rfl oqBody_792
    (Program.find?_of_indexOf? (j := 987) (by decide +kernel) rfl) rfl oqLoopBody_792

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_812 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L23_L6_L0_L0_L0_L0_L0" "__loop401" (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 23, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L17_L6)
    (Program.find?_of_indexOf? (j := 812) (by decide +kernel) rfl) rfl oqBody_812
    (Program.find?_of_indexOf? (j := 993) (by decide +kernel) rfl) rfl oqLoopBody_812

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_835 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L25_L6_L0_L0_L0_L0_L0" "__loop405" (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 25, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L19_L6)
    (Program.find?_of_indexOf? (j := 835) (by decide +kernel) rfl) rfl oqBody_835
    (Program.find?_of_indexOf? (j := 999) (by decide +kernel) rfl) rfl oqLoopBody_835

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_852 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L25_L5_L0_L0_L0_L0_L0" "__loop409" (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 25, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L20_L5)
    (Program.find?_of_indexOf? (j := 852) (by decide +kernel) rfl) rfl oqBody_852
    (Program.find?_of_indexOf? (j := 1004) (by decide +kernel) rfl) rfl oqLoopBody_852

end
end LeanVM.Guest.B1
