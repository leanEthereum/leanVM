/-
  LeanVM.Guest.B1.Opening.QueriesPlacedES3

  A quarter of `opening_queries`' specializations, `CompleteAtE`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody3
public import LeanVM.Guest.B1.Opening.QueriesPlacedE
public import LeanVM.Guest.B1.Opening.WalkFns

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1015 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0" "__loop505" (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDE1 fs cert (s := ((⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1015) (by decide +kernel) rfl) rfl oqBody_1015
    (Program.find?_of_indexOf? (j := 1514) (by decide +kernel) rfl) rfl oqLoopBody_1015

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1025 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0" "__loop509" (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L5
    (Program.find?_of_indexOf? (j := 1025) (by decide +kernel) rfl) rfl oqBody_1025
    (Program.find?_of_indexOf? (j := 1518) (by decide +kernel) rfl) rfl oqLoopBody_1025

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1` is `CompleteAtE`. -/
theorem oqDE_1040 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1" "__loop513" (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L2
    (Program.find?_of_indexOf? (j := 1040) (by decide +kernel) rfl) rfl oqBody_1040
    (Program.find?_of_indexOf? (j := 1522) (by decide +kernel) rfl) rfl oqLoopBody_1040

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1076 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0" "__loop517" (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1076) (by decide +kernel) rfl) rfl oqBody_1076
    (Program.find?_of_indexOf? (j := 1527) (by decide +kernel) rfl) rfl oqLoopBody_1076

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1` is `CompleteAtE`. -/
theorem oqDE_1082 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1" "__loop521" (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1082) (by decide +kernel) rfl) rfl oqBody_1082
    (Program.find?_of_indexOf? (j := 1531) (by decide +kernel) rfl) rfl oqLoopBody_1082

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1` is `CompleteAtE`. -/
theorem oqDE_1119 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1" "__loop525" (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L2
    (Program.find?_of_indexOf? (j := 1119) (by decide +kernel) rfl) rfl oqBody_1119
    (Program.find?_of_indexOf? (j := 1536) (by decide +kernel) rfl) rfl oqLoopBody_1119

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1150 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0" "__loop529" (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 :=
  oqCompleteDE1 fs cert (s := ((⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 0 ≤ 1) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1150) (by decide +kernel) rfl) rfl oqBody_1150
    (Program.find?_of_indexOf? (j := 1540) (by decide +kernel) rfl) rfl oqLoopBody_1150

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1` is `CompleteAtE`. -/
theorem oqDE_1160 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1" "__loop533" (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L4
    (Program.find?_of_indexOf? (j := 1160) (by decide +kernel) rfl) rfl oqBody_1160
    (Program.find?_of_indexOf? (j := 1545) (by decide +kernel) rfl) rfl oqLoopBody_1160

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1191 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0" "__loop537" (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDE1 fs cert (s := ((⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L4
    (Program.find?_of_indexOf? (j := 1191) (by decide +kernel) rfl) rfl oqBody_1191
    (Program.find?_of_indexOf? (j := 1550) (by decide +kernel) rfl) rfl oqLoopBody_1191

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1` is `CompleteAtE`. -/
theorem oqDE_1201 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1" "__loop541" (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L6
    (Program.find?_of_indexOf? (j := 1201) (by decide +kernel) rfl) rfl oqBody_1201
    (Program.find?_of_indexOf? (j := 1554) (by decide +kernel) rfl) rfl oqLoopBody_1201

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1` is `CompleteAtE`. -/
theorem oqDE_1245 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1" "__loop545" (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L5
    (Program.find?_of_indexOf? (j := 1245) (by decide +kernel) rfl) rfl oqBody_1245
    (Program.find?_of_indexOf? (j := 1559) (by decide +kernel) rfl) rfl oqLoopBody_1245

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1281 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0" "__loop549" (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDE1 fs cert (s := ((⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L18_L6
    (Program.find?_of_indexOf? (j := 1281) (by decide +kernel) rfl) rfl oqBody_1281
    (Program.find?_of_indexOf? (j := 1564) (by decide +kernel) rfl) rfl oqLoopBody_1281

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1` is `CompleteAtE`. -/
theorem oqDE_1291 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1" "__loop553" (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L2
    (Program.find?_of_indexOf? (j := 1291) (by decide +kernel) rfl) rfl oqBody_1291
    (Program.find?_of_indexOf? (j := 1568) (by decide +kernel) rfl) rfl oqLoopBody_1291

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1` is `CompleteAtE`. -/
theorem oqDE_1332 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1" "__loop557" (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L12_L7
    (Program.find?_of_indexOf? (j := 1332) (by decide +kernel) rfl) rfl oqBody_1332
    (Program.find?_of_indexOf? (j := 1573) (by decide +kernel) rfl) rfl oqLoopBody_1332

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1368 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0" "__loop561" (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDE1 fs cert (s := ((⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L24_L2
    (Program.find?_of_indexOf? (j := 1368) (by decide +kernel) rfl) rfl oqBody_1368
    (Program.find?_of_indexOf? (j := 1578) (by decide +kernel) rfl) rfl oqLoopBody_1368

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1` is `CompleteAtE`. -/
theorem oqDE_1379 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1" "__loop565" (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L3
    (Program.find?_of_indexOf? (j := 1379) (by decide +kernel) rfl) rfl oqBody_1379
    (Program.find?_of_indexOf? (j := 1582) (by decide +kernel) rfl) rfl oqLoopBody_1379

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1` is `CompleteAtE`. -/
theorem oqDE_1426 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1" "__loop569" (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L2
    (Program.find?_of_indexOf? (j := 1426) (by decide +kernel) rfl) rfl oqBody_1426
    (Program.find?_of_indexOf? (j := 1587) (by decide +kernel) rfl) rfl oqLoopBody_1426

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0` is `CompleteAtE`. -/
theorem oqDE_1465 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0" "__loop573" (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 :=
  oqCompleteDE1 fs cert (s := ((⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide : 1 ≤ 1) (by decide +kernel) wpFn_L24_L4
    (Program.find?_of_indexOf? (j := 1465) (by decide +kernel) rfl) rfl oqBody_1465
    (Program.find?_of_indexOf? (j := 1592) (by decide +kernel) rfl) rfl oqLoopBody_1465

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1` is `CompleteAtE`. -/
theorem oqDE_1476 (fs : String → ℕ) (cert : String → V → ℕ) :
    OqCompleteDE fs cert "opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1" "__loop577" (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 :=
  oqCompleteDE0 fs cert (s := ((⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)) (by decide) (by decide) rfl (by decide)
    (by decide) (by decide +kernel) wpFn_L18_L5
    (Program.find?_of_indexOf? (j := 1476) (by decide +kernel) rfl) rfl oqBody_1476
    (Program.find?_of_indexOf? (j := 1596) (by decide +kernel) rfl) rfl oqLoopBody_1476

end
end LeanVM.Guest.B1
