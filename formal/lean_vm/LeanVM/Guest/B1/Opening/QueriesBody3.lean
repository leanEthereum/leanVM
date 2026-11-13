/-
  LeanVM.Guest.B1.Opening.QueriesBody3

  The bodies of a quarter of `opening_queries`' specializations and of their loop helpers are
  the templates (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Opening.QueriesT
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1015 : (fn% «opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18, 6, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1015 : (fn% «opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 18,
    6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1025 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1025 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1`. -/
theorem oqBody_1040 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 2,
    3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1_loop0`. -/
theorem oqLoopBody_1040 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 14, 2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14,
    2, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1076 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1076 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18, 6,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1`. -/
theorem oqBody_1082 : (fn% «opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 16,
    4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1082 : (fn% «opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 16, 4, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1`. -/
theorem oqBody_1119 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0,
    4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1_loop0`. -/
theorem oqLoopBody_1119 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf
    (⟨0, 0, 4, 16, 14, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1150 : (fn% «opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 18, 6, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1150 : (fn% «opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨0, 1, 6, 32, 18, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 18,
    6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1`. -/
theorem oqBody_1160 : (fn% «opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0
    (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1_loop0`. -/
theorem oqLoopBody_1160 : (fn% «opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 16, 4, 5, 15, 36, 6, 1, [1, 6, 360, 18245760,
    78274681211224091]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1191 : (fn% «opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22, 4, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1191 : (fn% «opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 22,
    4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1`. -/
theorem oqBody_1201 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18, 6, 2,
    3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1_loop0`. -/
theorem oqLoopBody_1201 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 18, 6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 18,
    6, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1`. -/
theorem oqBody_1245 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 17,
    5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1245 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 17, 5, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1281 : (fn% «opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24, 6, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1281 : (fn% «opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 24,
    6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1`. -/
theorem oqBody_1291 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0,
    4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1_loop0`. -/
theorem oqLoopBody_1291 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf
    (⟨0, 0, 4, 16, 20, 2, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1`. -/
theorem oqBody_1332 : (fn% «opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0
    (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1_loop0`. -/
theorem oqLoopBody_1332 : (fn% «opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 19, 7, 5, 15, 36, 6, 1, [1, 6, 360, 18245760,
    78274681211224091]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1368 : (fn% «opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26, 2, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1368 : (fn% «opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 26, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 26,
    2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1`. -/
theorem oqBody_1379 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 2,
    3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1_loop0`. -/
theorem oqLoopBody_1379 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 21, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21,
    3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1`. -/
theorem oqBody_1426 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 20,
    2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1426 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 20, 2, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1465 : (fn% «opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 28, 4, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1465 : (fn% «opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 28, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 28,
    4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1`. -/
theorem oqBody_1476 : (fn% «opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0,
    4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1_loop0`. -/
theorem oqLoopBody_1476 : (fn% «opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf
    (⟨0, 0, 4, 16, 23, 5, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
