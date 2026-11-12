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
/-- `opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1013 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0" "__loop504" (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 1013) (by decide +kernel) rfl) rfl oqBody_1013
    (Program.find?_of_indexOf? (j := 1512) (by decide +kernel) rfl) rfl oqLoopBody_1013

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1024 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0" "__loop508" (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L4)
    (Program.find?_of_indexOf? (j := 1024) (by decide +kernel) rfl) rfl oqBody_1024
    (Program.find?_of_indexOf? (j := 1517) (by decide +kernel) rfl) rfl oqLoopBody_1024

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_1039 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1" "__loop512" (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 13, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L6_L7)
    (Program.find?_of_indexOf? (j := 1039) (by decide +kernel) rfl) rfl oqBody_1039
    (Program.find?_of_indexOf? (j := 1521) (by decide +kernel) rfl) rfl oqLoopBody_1039

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1071 : opening_queries_sound_w_Spec "opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0" "__loop516" (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨1, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L7)
    (Program.find?_of_indexOf? (j := 1071) (by decide +kernel) rfl) rfl oqBody_1071
    (Program.find?_of_indexOf? (j := 1526) (by decide +kernel) rfl) rfl oqLoopBody_1071

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1` is sound with its queries named. -/
theorem oqSpecW_1081 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1" "__loop520" (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L3)
    (Program.find?_of_indexOf? (j := 1081) (by decide +kernel) rfl) rfl oqBody_1081
    (Program.find?_of_indexOf? (j := 1530) (by decide +kernel) rfl) rfl oqLoopBody_1081

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1116 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0" "__loop524" (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L7)
    (Program.find?_of_indexOf? (j := 1116) (by decide +kernel) rfl) rfl oqBody_1116
    (Program.find?_of_indexOf? (j := 1535) (by decide +kernel) rfl) rfl oqLoopBody_1116

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_1122 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1" "__loop528" (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 1122) (by decide +kernel) rfl) rfl oqBody_1122
    (Program.find?_of_indexOf? (j := 1539) (by decide +kernel) rfl) rfl oqLoopBody_1122

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1` is sound with its queries named. -/
theorem oqSpecW_1159 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1" "__loop532" (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 15, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L3)
    (Program.find?_of_indexOf? (j := 1159) (by decide +kernel) rfl) rfl oqBody_1159
    (Program.find?_of_indexOf? (j := 1544) (by decide +kernel) rfl) rfl oqLoopBody_1159

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1190 : opening_queries_sound_w_Spec "opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0" "__loop536" (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨0, 1, 6, 32, 19, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L7)
    (Program.find?_of_indexOf? (j := 1190) (by decide +kernel) rfl) rfl oqBody_1190
    (Program.find?_of_indexOf? (j := 1548) (by decide +kernel) rfl) rfl oqLoopBody_1190

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_1200 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1" "__loop540" (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 17, 5, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L5)
    (Program.find?_of_indexOf? (j := 1200) (by decide +kernel) rfl) rfl oqBody_1200
    (Program.find?_of_indexOf? (j := 1553) (by decide +kernel) rfl) rfl oqLoopBody_1200

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1241 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0" "__loop544" (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L4)
    (Program.find?_of_indexOf? (j := 1241) (by decide +kernel) rfl) rfl oqBody_1241
    (Program.find?_of_indexOf? (j := 1558) (by decide +kernel) rfl) rfl oqLoopBody_1241

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1280 : opening_queries_sound_w_Spec "opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0" "__loop548" (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨0, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L3)
    (Program.find?_of_indexOf? (j := 1280) (by decide +kernel) rfl) rfl oqBody_1280
    (Program.find?_of_indexOf? (j := 1562) (by decide +kernel) rfl) rfl oqLoopBody_1280

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_1290 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1" "__loop552" (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 19, 7, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L12_L7)
    (Program.find?_of_indexOf? (j := 1290) (by decide +kernel) rfl) rfl oqBody_1290
    (Program.find?_of_indexOf? (j := 1567) (by decide +kernel) rfl) rfl oqLoopBody_1290

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1329 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0" "__loop556" (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L6)
    (Program.find?_of_indexOf? (j := 1329) (by decide +kernel) rfl) rfl oqBody_1329
    (Program.find?_of_indexOf? (j := 1572) (by decide +kernel) rfl) rfl oqLoopBody_1329

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1367 : opening_queries_sound_w_Spec "opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0" "__loop560" (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨0, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L5)
    (Program.find?_of_indexOf? (j := 1367) (by decide +kernel) rfl) rfl oqBody_1367
    (Program.find?_of_indexOf? (j := 1576) (by decide +kernel) rfl) rfl oqLoopBody_1367

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1` is sound with its queries named. -/
theorem oqSpecW_1378 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1" "__loop564" (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 20, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L2)
    (Program.find?_of_indexOf? (j := 1378) (by decide +kernel) rfl) rfl oqBody_1378
    (Program.find?_of_indexOf? (j := 1581) (by decide +kernel) rfl) rfl oqLoopBody_1378

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1422 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0" "__loop568" (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L24_L2)
    (Program.find?_of_indexOf? (j := 1422) (by decide +kernel) rfl) rfl oqBody_1422
    (Program.find?_of_indexOf? (j := 1586) (by decide +kernel) rfl) rfl oqLoopBody_1422

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0` is sound with its queries named. -/
theorem oqSpecW_1464 : opening_queries_sound_w_Spec "opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0" "__loop572" (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape) :=
  oqMain1_sound_w (sh := (⟨0, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape)) (by decide) (by decide) rfl rfl (by decide)
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L7)
    (Program.find?_of_indexOf? (j := 1464) (by decide +kernel) rfl) rfl oqBody_1464
    (Program.find?_of_indexOf? (j := 1590) (by decide +kernel) rfl) rfl oqLoopBody_1464

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1` is sound with its queries named. -/
theorem oqSpecW_1475 : opening_queries_sound_w_Spec "opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1" "__loop576" (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape) :=
  oqMain0_sound_w (sh := (⟨0, 0, 4, 16, 22, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape)) (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (wpFn_L18_L4)
    (Program.find?_of_indexOf? (j := 1475) (by decide +kernel) rfl) rfl oqBody_1475
    (Program.find?_of_indexOf? (j := 1595) (by decide +kernel) rfl) rfl oqLoopBody_1475

end
end LeanVM.Guest.B1
