/-
  LeanVM.Guest.B1.Opening.QueriesBody0

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
/-- `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1009 : (fn% «opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 15, 3, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1009 : (fn% «opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 15, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 15,
    3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0`. -/
theorem oqBody_1022 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 14, 2, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1022 : (fn% «opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 14, 2, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 14, 2,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1032 : (fn% «opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 13, 7, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1032 : (fn% «opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 13, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 13, 7,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1`. -/
theorem oqBody_1041 : (fn% «opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 15, 3, 2,
    3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1_loop0`. -/
theorem oqLoopBody_1041 : (fn% «opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 15, 3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 15,
    3, 2, 3, 8, 3, 1, [1, 6]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1`. -/
theorem oqBody_1079 : (fn% «opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 13,
    7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1079 : (fn% «opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 13, 7, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1110 : (fn% «opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17, 5, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1110 : (fn% «opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨0, 1, 6, 32, 17, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 17,
    5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1`. -/
theorem oqBody_1120 : (fn% «opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0,
    4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1_loop0`. -/
theorem oqLoopBody_1120 : (fn% «opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq (oqWalkOf
    (⟨0, 0, 4, 16, 15, 3, 4, 10, 20, 5, 1, [1, 6, 360, 18245760]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1151 : (fn% «opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21, 3, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1151 : (fn% «opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨1, 1, 6, 32, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 1 (oqWalkOf (⟨1, 1, 6, 32, 21,
    3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1`. -/
theorem oqBody_1161 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0
    (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1_loop0`. -/
theorem oqLoopBody_1161 : (fn% «opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 17, 5, 5, 15, 36, 6, 1, [1, 6, 360, 18245760,
    78274681211224091]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1195 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21, 3, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1195 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 21, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 21, 3,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0`. -/
theorem oqBody_1236 : (fn% «opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 20, 8, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1236 : (fn% «opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨0, 1, 6, 32, 20, 8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 20,
    8, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1`. -/
theorem oqBody_1246 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 18,
    6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1246 : (fn% «opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 18, 6, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqBody_1285 : (fn% «opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 23, 5, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1285 : (fn% «opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 23, 5, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 23, 5,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqBody_1324 : (fn% «opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 22, 4, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1324 : (fn% «opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨0, 1, 6, 32, 22, 4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 22,
    4, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1`. -/
theorem oqBody_1333 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ : OqShape).oq 0
    (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1_loop0`. -/
theorem oqLoopBody_1333 : (fn% «opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760, 78274681211224091]⟩ :
    OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 20, 2, 5, 15, 36, 6, 1, [1, 6, 360, 18245760,
    78274681211224091]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqBody_1372 : (fn% «opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 25, 7, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1372 : (fn% «opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 25, 7, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 25, 7,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqBody_1417 : (fn% «opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 24, 6, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1417 : (fn% «opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop1T (⟨0, 1, 6, 32, 24, 6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 1, 6, 32, 24,
    6, 0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1`. -/
theorem oqBody_1427 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1»).body = oqMainT
    (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 21,
    3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1_loop0`. -/
theorem oqLoopBody_1427 : (fn% «opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4,
    16, 21, 3, 3, 6, 12, 4, 1, [1, 6, 360]⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0`. -/
theorem oqBody_1469 : (fn% «opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0»).body = oqMainT
    (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq 0 (oqWalkOf (⟨0, 0, 4, 16, 27, 3, 0, 0,
    0, 0, 0, []⟩ : OqShape).oq) name% «opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0_loop0`. -/
theorem oqLoopBody_1469 : (fn% «opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0_loop0»).body =
    oqLoop0T (⟨0, 0, 4, 16, 27, 3, 0, 0, 0, 0, 0, []⟩ : OqShape).oq (oqWalkOf (⟨0, 0, 4, 16, 27, 3,
    0, 0, 0, 0, 0, []⟩ : OqShape).oq)
    name% «opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0_loop0» :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1
