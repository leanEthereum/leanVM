/-
  LeanVM.Guest.B1.Opening.QueriesPlacedS0

  A quarter of `opening_queries`' specializations, `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1009 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0" "__loop502" (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L12_L3
    (Program.find?_of_indexOf? (j := 1009) (by decide +kernel) rfl) rfl oqBody_1009
    (Program.find?_of_indexOf? (j := 1508) (by decide +kernel) rfl) rfl oqLoopBody_1009

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1022 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0" "__loop506" (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L2
    (Program.find?_of_indexOf? (j := 1022) (by decide +kernel) rfl) rfl oqBody_1022
    (Program.find?_of_indexOf? (j := 1515) (by decide +kernel) rfl) rfl oqLoopBody_1022

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1032 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0" "__loop510" (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L6_L7
    (Program.find?_of_indexOf? (j := 1032) (by decide +kernel) rfl) rfl oqBody_1032
    (Program.find?_of_indexOf? (j := 1519) (by decide +kernel) rfl) rfl oqLoopBody_1032

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1` is `CompleteAtB`. -/
theorem oqD_1041 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1" "__loop514" (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L3
    (Program.find?_of_indexOf? (j := 1041) (by decide +kernel) rfl) rfl oqBody_1041
    (Program.find?_of_indexOf? (j := 1523) (by decide +kernel) rfl) rfl oqLoopBody_1041

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1079 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1" "__loop518" (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L6_L7
    (Program.find?_of_indexOf? (j := 1079) (by decide +kernel) rfl) rfl oqBody_1079
    (Program.find?_of_indexOf? (j := 1528) (by decide +kernel) rfl) rfl oqLoopBody_1079

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1110 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0" "__loop522" (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB1 fs cert (s := ((⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L12_L5
    (Program.find?_of_indexOf? (j := 1110) (by decide +kernel) rfl) rfl oqBody_1110
    (Program.find?_of_indexOf? (j := 1532) (by decide +kernel) rfl) rfl oqLoopBody_1110

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1` is `CompleteAtB`. -/
theorem oqD_1120 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1" "__loop526" (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L3
    (Program.find?_of_indexOf? (j := 1120) (by decide +kernel) rfl) rfl oqBody_1120
    (Program.find?_of_indexOf? (j := 1537) (by decide +kernel) rfl) rfl oqLoopBody_1120

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1151 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0" "__loop530" (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDB1 fs cert (s := ((⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1151) (by decide +kernel) rfl) rfl oqBody_1151
    (Program.find?_of_indexOf? (j := 1542) (by decide +kernel) rfl) rfl oqLoopBody_1151

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1` is `CompleteAtB`. -/
theorem oqD_1161 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1" "__loop534" (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L5
    (Program.find?_of_indexOf? (j := 1161) (by decide +kernel) rfl) rfl oqBody_1161
    (Program.find?_of_indexOf? (j := 1546) (by decide +kernel) rfl) rfl oqLoopBody_1161

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1195 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0" "__loop538" (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1195) (by decide +kernel) rfl) rfl oqBody_1195
    (Program.find?_of_indexOf? (j := 1551) (by decide +kernel) rfl) rfl oqLoopBody_1195

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1236 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0" "__loop542" (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB1 fs cert (s := ((⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L12_L8
    (Program.find?_of_indexOf? (j := 1236) (by decide +kernel) rfl) rfl oqBody_1236
    (Program.find?_of_indexOf? (j := 1555) (by decide +kernel) rfl) rfl oqLoopBody_1236

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1246 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1" "__loop546" (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1246) (by decide +kernel) rfl) rfl oqBody_1246
    (Program.find?_of_indexOf? (j := 1560) (by decide +kernel) rfl) rfl oqLoopBody_1246

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1285 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0" "__loop550" (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L5
    (Program.find?_of_indexOf? (j := 1285) (by decide +kernel) rfl) rfl oqBody_1285
    (Program.find?_of_indexOf? (j := 1565) (by decide +kernel) rfl) rfl oqLoopBody_1285

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1324 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0" "__loop554" (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB1 fs cert (s := ((⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L18_L4
    (Program.find?_of_indexOf? (j := 1324) (by decide +kernel) rfl) rfl oqBody_1324
    (Program.find?_of_indexOf? (j := 1569) (by decide +kernel) rfl) rfl oqLoopBody_1324

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1` is `CompleteAtB`. -/
theorem oqD_1333 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1" "__loop558" (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L2
    (Program.find?_of_indexOf? (j := 1333) (by decide +kernel) rfl) rfl oqBody_1333
    (Program.find?_of_indexOf? (j := 1574) (by decide +kernel) rfl) rfl oqLoopBody_1333

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1372 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0" "__loop562" (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L7
    (Program.find?_of_indexOf? (j := 1372) (by decide +kernel) rfl) rfl oqBody_1372
    (Program.find?_of_indexOf? (j := 1579) (by decide +kernel) rfl) rfl oqLoopBody_1372

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1417 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0" "__loop566" (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB1 fs cert (s := ((⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L18_L6
    (Program.find?_of_indexOf? (j := 1417) (by decide +kernel) rfl) rfl oqBody_1417
    (Program.find?_of_indexOf? (j := 1583) (by decide +kernel) rfl) rfl oqLoopBody_1417

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1` is `CompleteAtB`. -/
theorem oqD_1427 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1" "__loop570" (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1427) (by decide +kernel) rfl) rfl oqBody_1427
    (Program.find?_of_indexOf? (j := 1588) (by decide +kernel) rfl) rfl oqLoopBody_1427

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0` is `CompleteAtB`. -/
theorem oqD_1469 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDB fs cert "opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0" "__loop574" (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDB0 fs cert (s := ((⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L24_L3
    (Program.find?_of_indexOf? (j := 1469) (by decide +kernel) rfl) rfl oqBody_1469
    (Program.find?_of_indexOf? (j := 1593) (by decide +kernel) rfl) rfl oqLoopBody_1469

end
end LeanVM.Guest.B1
