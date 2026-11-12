/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS1

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1011 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0" "__loop503" (⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1011) (by decide +kernel) rfl) rfl oqBody_1011
    (Program.find?_of_indexOf? (j := 1510) (by decide +kernel) rfl) rfl oqLoopBody_1011

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1023 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L15_L3_L0_L0_L0_L0_L0" "__loop507" (⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L3
    (Program.find?_of_indexOf? (j := 1023) (by decide +kernel) rfl) rfl oqBody_1023
    (Program.find?_of_indexOf? (j := 1516) (by decide +kernel) rfl) rfl oqLoopBody_1023

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L12_L6_L2_L3_L8_L3_L1` is `CompleteAtB`. -/
theorem oqD_1038 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L12_L6_L2_L3_L8_L3_L1" "__loop511" (⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 12, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L6_L6
    (Program.find?_of_indexOf? (j := 1038) (by decide +kernel) rfl) rfl oqBody_1038
    (Program.find?_of_indexOf? (j := 1520) (by decide +kernel) rfl) rfl oqLoopBody_1038

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1070 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0" "__loop515" (⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB1 fs cert (s := ((⟨0, 1, 6, 32, 16, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1070) (by decide +kernel) rfl) rfl oqBody_1070
    (Program.find?_of_indexOf? (j := 1524) (by decide +kernel) rfl) rfl oqLoopBody_1070

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1080 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L14_L2_L3_L6_L12_L4_L1" "__loop519" (⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 14, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L2
    (Program.find?_of_indexOf? (j := 1080) (by decide +kernel) rfl) rfl oqBody_1080
    (Program.find?_of_indexOf? (j := 1529) (by decide +kernel) rfl) rfl oqLoopBody_1080

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L20_L2_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1111 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L20_L2_L0_L0_L0_L0_L0" "__loop523" (⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L2
    (Program.find?_of_indexOf? (j := 1111) (by decide +kernel) rfl) rfl oqBody_1111
    (Program.find?_of_indexOf? (j := 1534) (by decide +kernel) rfl) rfl oqLoopBody_1111

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L4_L10_L20_L5_L1` is `CompleteAtB`. -/
theorem oqD_1121 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L16_L4_L4_L10_L20_L5_L1" "__loop527" (⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 16, 4, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1121) (by decide +kernel) rfl) rfl oqBody_1121
    (Program.find?_of_indexOf? (j := 1538) (by decide +kernel) rfl) rfl oqLoopBody_1121

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1156 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L20_L2_L0_L0_L0_L0_L0" "__loop531" (⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 20, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L2
    (Program.find?_of_indexOf? (j := 1156) (by decide +kernel) rfl) rfl oqBody_1156
    (Program.find?_of_indexOf? (j := 1543) (by decide +kernel) rfl) rfl oqLoopBody_1156

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L5_L15_L36_L6_L1` is `CompleteAtB`. -/
theorem oqD_1162 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L18_L6_L5_L15_L36_L6_L1" "__loop535" (⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 18, 6, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1162) (by decide +kernel) rfl) rfl oqBody_1162
    (Program.find?_of_indexOf? (j := 1547) (by decide +kernel) rfl) rfl oqLoopBody_1162

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L2_L3_L8_L3_L1` is `CompleteAtB`. -/
theorem oqD_1199 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L16_L4_L2_L3_L8_L3_L1" "__loop539" (⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 16, 4, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1199) (by decide +kernel) rfl) rfl oqBody_1199
    (Program.find?_of_indexOf? (j := 1552) (by decide +kernel) rfl) rfl oqLoopBody_1199

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1237 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0" "__loop543" (⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L5
    (Program.find?_of_indexOf? (j := 1237) (by decide +kernel) rfl) rfl oqBody_1237
    (Program.find?_of_indexOf? (j := 1557) (by decide +kernel) rfl) rfl oqLoopBody_1237

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1247 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L19_L7_L3_L6_L12_L4_L1" "__loop547" (⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 19, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L7
    (Program.find?_of_indexOf? (j := 1247) (by decide +kernel) rfl) rfl oqBody_1247
    (Program.find?_of_indexOf? (j := 1561) (by decide +kernel) rfl) rfl oqLoopBody_1247

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1` is `CompleteAtB`. -/
theorem oqD_1289 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1" "__loop551" (⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 18, 6, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1289) (by decide +kernel) rfl) rfl oqBody_1289
    (Program.find?_of_indexOf? (j := 1566) (by decide +kernel) rfl) rfl oqLoopBody_1289

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1325 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0" "__loop555" (⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L7
    (Program.find?_of_indexOf? (j := 1325) (by decide +kernel) rfl) rfl oqBody_1325
    (Program.find?_of_indexOf? (j := 1571) (by decide +kernel) rfl) rfl oqLoopBody_1325

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L5_L15_L36_L6_L1` is `CompleteAtB`. -/
theorem oqD_1334 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L21_L3_L5_L15_L36_L6_L1" "__loop559" (⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 21, 3, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1334) (by decide +kernel) rfl) rfl oqBody_1334
    (Program.find?_of_indexOf? (j := 1575) (by decide +kernel) rfl) rfl oqLoopBody_1334

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L2_L3_L8_L3_L1` is `CompleteAtB`. -/
theorem oqD_1377 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L19_L7_L2_L3_L8_L3_L1" "__loop563" (⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 19, 7, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L7
    (Program.find?_of_indexOf? (j := 1377) (by decide +kernel) rfl) rfl oqBody_1377
    (Program.find?_of_indexOf? (j := 1580) (by decide +kernel) rfl) rfl oqLoopBody_1377

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L27_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1418 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L27_L3_L0_L0_L0_L0_L0" "__loop567" (⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L24_L3
    (Program.find?_of_indexOf? (j := 1418) (by decide +kernel) rfl) rfl oqBody_1418
    (Program.find?_of_indexOf? (j := 1585) (by decide +kernel) rfl) rfl oqLoopBody_1418

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L22_L4_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1428 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L22_L4_L3_L6_L12_L4_L1" "__loop571" (⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 22, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L4
    (Program.find?_of_indexOf? (j := 1428) (by decide +kernel) rfl) rfl oqBody_1428
    (Program.find?_of_indexOf? (j := 1589) (by decide +kernel) rfl) rfl oqLoopBody_1428

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L4_L10_L20_L5_L1` is `CompleteAtB`. -/
theorem oqD_1474 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L21_L3_L4_L10_L20_L5_L1" "__loop575" (⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 21, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1474) (by decide +kernel) rfl) rfl oqBody_1474
    (Program.find?_of_indexOf? (j := 1594) (by decide +kernel) rfl) rfl oqLoopBody_1474

end
end LeanVM.Guest.B1
