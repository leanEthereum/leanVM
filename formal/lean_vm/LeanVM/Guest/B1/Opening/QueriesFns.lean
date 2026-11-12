/-
  LeanVM.Guest.B1.Opening.QueriesFns

  Every deployed specialization of `opening_queries` and its loop helper are found with the
  templates' bodies, and its shape has the facts the specializations' theorems take.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesBody0
public import LeanVM.Guest.B1.Opening.QueriesBody1
public import LeanVM.Guest.B1.Opening.QueriesBody2
public import LeanVM.Guest.B1.Opening.QueriesBody3
public import LeanVM.Guest.B1.Opening.QueriesPlacedD2
public import LeanVM.Guest.B1.Opening.WalkFns
public import Mathlib.Tactic.IntervalCases

/-!
# The specializations of `opening_queries`, found

For each entry `p = (name, loop, sh)` of `openingQueriesLoops`:

* `OqFns p` (`oqFns_all`): its `walk_path` is a walk of its depths (`WalkFn`), `name` finds the
  function with the body `oqMainT` and `loop` the loop helper with the body `oqLoopT` (`oqLoop0T`
  at base `0`, `oqLoop1T` at base `1`), from `QueriesBody*` (the bodies, by kernel evaluation);
* `OqSide p` (`oqSide_all`, by kernel evaluation): the shape's row and final level, its base and
  odd query, its depths' bounds, and the table's own entry check (`oqEntryB`).

The statements over every entry (`QueriesAllW`, `QueriesPlacedAll`, `QueriesPlacedEAll`) take
these and apply their base's theorem.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The loop helper's template at the shape's base. -/
def oqLoopT (s : Oq) (odd : ℕ) (walk loop : String) : List Stmt :=
  match s.base with
  | 0 => oqLoop0T s walk loop
  | _ => oqLoop1T s odd walk loop

theorem oqLoopT_zero {s : Oq} (h : s.base = 0) (odd : ℕ) (walk loop : String) :
    oqLoopT s odd walk loop = oqLoop0T s walk loop := by
  unfold oqLoopT; rw [h]; rfl

theorem oqLoopT_one {s : Oq} (h : s.base = 1) (odd : ℕ) (walk loop : String) :
    oqLoopT s odd walk loop = oqLoop1T s odd walk loop := by
  unfold oqLoopT; rw [h]; rfl

/-- **Entry `p`'s functions**: its walk, and the function and loop helper with the templates'
bodies. -/
def OqFns (p : String × String × OqShape) : Prop :=
  WalkFn (oqWalkOf p.2.2.oq) p.2.2.oq.pd p.2.2.cd ∧
    ∃ fm fl : Fn, coreProgram.find? p.1 = some fm ∧
      fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7] ∧
      fm.body = oqMainT p.2.2.oq p.2.2.odd (oqWalkOf p.2.2.oq) p.2.1 ∧
      coreProgram.find? p.2.1 = some fl ∧ fl.params = oqLoopParams ∧
      fl.body = oqLoopT p.2.2.oq p.2.2.odd (oqWalkOf p.2.2.oq) p.2.1

/-- **Entry `p`'s shape facts.** -/
def OqSide (p : String × String × OqShape) : Prop :=
  p.2.2.oq.RowShape ∧ p.2.2.oq.FinOk ∧
    (p.2.2.base = 0 ∧ p.2.2.odd = 0 ∨
      p.2.2.base = 1 ∧ p.2.2.final = 0 ∧ p.2.2.odd ≤ 1) ∧
    1 ≤ p.2.2.oq.pd ∧ 2 ≤ p.2.2.cd ∧ p.2.2.cd ≤ 8 ∧ p.2.2.cd ≤ p.2.2.depth ∧
    oqEntryB p.1 p.2.2.oq p.2.2.odd = true

instance (p : String × String × OqShape) : Decidable (OqSide p) := by
  unfold OqSide; infer_instance

/-- No entry: `getD`'s fallback. -/
def oqNone : String × String × OqShape := ("", "", ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩)

set_option maxRecDepth 100000 in
/-- **Every entry has its shape facts**, by the kernel. -/
theorem oqSide_all : ∀ p ∈ openingQueriesLoops, OqSide p := by decide +kernel

set_option maxRecDepth 100000 in
/-- Entry 0, `opening_queries__L1_L1_L6_L32_L15_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1009 : OqFns (openingQueriesLoops.getD 0 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1009, Data.core1508,
    coreProgram_find?_at (j := 1009) rfl, rfl, oqBody_1009,
    coreProgram_find?_at (j := 1508) rfl, rfl, oqLoopBody_1009⟩

set_option maxRecDepth 100000 in
/-- Entry 1, `opening_queries__L1_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1011 : OqFns (openingQueriesLoops.getD 1 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1011, Data.core1510,
    coreProgram_find?_at (j := 1011) rfl, rfl, oqBody_1011,
    coreProgram_find?_at (j := 1510) rfl, rfl, oqLoopBody_1011⟩

set_option maxRecDepth 100000 in
/-- Entry 2, `opening_queries__L1_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1013 : OqFns (openingQueriesLoops.getD 2 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1013, Data.core1512,
    coreProgram_find?_at (j := 1013) rfl, rfl, oqBody_1013,
    coreProgram_find?_at (j := 1512) rfl, rfl, oqLoopBody_1013⟩

set_option maxRecDepth 100000 in
/-- Entry 3, `opening_queries__L1_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1015 : OqFns (openingQueriesLoops.getD 3 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1015, Data.core1514,
    coreProgram_find?_at (j := 1015) rfl, rfl, oqBody_1015,
    coreProgram_find?_at (j := 1514) rfl, rfl, oqLoopBody_1015⟩

set_option maxRecDepth 100000 in
/-- Entry 4, `opening_queries__L0_L0_L4_L16_L14_L2_L0_L0_L0_L0_L0`. -/
theorem oqFns_1022 : OqFns (openingQueriesLoops.getD 4 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L2, Data.core1022, Data.core1515,
    coreProgram_find?_at (j := 1022) rfl, rfl, oqBody_1022,
    coreProgram_find?_at (j := 1515) rfl, rfl, oqLoopBody_1022⟩

set_option maxRecDepth 100000 in
/-- Entry 5, `opening_queries__L0_L0_L4_L16_L15_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1023 : OqFns (openingQueriesLoops.getD 5 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1023, Data.core1516,
    coreProgram_find?_at (j := 1023) rfl, rfl, oqBody_1023,
    coreProgram_find?_at (j := 1516) rfl, rfl, oqLoopBody_1023⟩

set_option maxRecDepth 100000 in
/-- Entry 6, `opening_queries__L0_L0_L4_L16_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1024 : OqFns (openingQueriesLoops.getD 6 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1024, Data.core1517,
    coreProgram_find?_at (j := 1024) rfl, rfl, oqBody_1024,
    coreProgram_find?_at (j := 1517) rfl, rfl, oqLoopBody_1024⟩

set_option maxRecDepth 100000 in
/-- Entry 7, `opening_queries__L0_L0_L4_L16_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1025 : OqFns (openingQueriesLoops.getD 7 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1025, Data.core1518,
    coreProgram_find?_at (j := 1025) rfl, rfl, oqBody_1025,
    coreProgram_find?_at (j := 1518) rfl, rfl, oqLoopBody_1025⟩

set_option maxRecDepth 100000 in
/-- Entry 8, `opening_queries__L0_L0_L4_L16_L13_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1032 : OqFns (openingQueriesLoops.getD 8 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L6_L7, Data.core1032, Data.core1519,
    coreProgram_find?_at (j := 1032) rfl, rfl, oqBody_1032,
    coreProgram_find?_at (j := 1519) rfl, rfl, oqLoopBody_1032⟩

set_option maxRecDepth 100000 in
/-- Entry 9, `opening_queries__L0_L0_L4_L16_L12_L6_L2_L3_L8_L3_L1`. -/
theorem oqFns_1038 : OqFns (openingQueriesLoops.getD 9 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L6_L6, Data.core1038, Data.core1520,
    coreProgram_find?_at (j := 1038) rfl, rfl, oqBody_1038,
    coreProgram_find?_at (j := 1520) rfl, rfl, oqLoopBody_1038⟩

set_option maxRecDepth 100000 in
/-- Entry 10, `opening_queries__L0_L0_L4_L16_L13_L7_L2_L3_L8_L3_L1`. -/
theorem oqFns_1039 : OqFns (openingQueriesLoops.getD 10 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L6_L7, Data.core1039, Data.core1521,
    coreProgram_find?_at (j := 1039) rfl, rfl, oqBody_1039,
    coreProgram_find?_at (j := 1521) rfl, rfl, oqLoopBody_1039⟩

set_option maxRecDepth 100000 in
/-- Entry 11, `opening_queries__L0_L0_L4_L16_L14_L2_L2_L3_L8_L3_L1`. -/
theorem oqFns_1040 : OqFns (openingQueriesLoops.getD 11 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L2, Data.core1040, Data.core1522,
    coreProgram_find?_at (j := 1040) rfl, rfl, oqBody_1040,
    coreProgram_find?_at (j := 1522) rfl, rfl, oqLoopBody_1040⟩

set_option maxRecDepth 100000 in
/-- Entry 12, `opening_queries__L0_L0_L4_L16_L15_L3_L2_L3_L8_L3_L1`. -/
theorem oqFns_1041 : OqFns (openingQueriesLoops.getD 12 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1041, Data.core1523,
    coreProgram_find?_at (j := 1041) rfl, rfl, oqBody_1041,
    coreProgram_find?_at (j := 1523) rfl, rfl, oqLoopBody_1041⟩

set_option maxRecDepth 100000 in
/-- Entry 13, `opening_queries__L0_L1_L6_L32_L16_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1070 : OqFns (openingQueriesLoops.getD 13 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1070, Data.core1524,
    coreProgram_find?_at (j := 1070) rfl, rfl, oqBody_1070,
    coreProgram_find?_at (j := 1524) rfl, rfl, oqLoopBody_1070⟩

set_option maxRecDepth 100000 in
/-- Entry 14, `opening_queries__L1_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1071 : OqFns (openingQueriesLoops.getD 14 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1071, Data.core1526,
    coreProgram_find?_at (j := 1071) rfl, rfl, oqBody_1071,
    coreProgram_find?_at (j := 1526) rfl, rfl, oqLoopBody_1071⟩

set_option maxRecDepth 100000 in
/-- Entry 15, `opening_queries__L0_L0_L4_L16_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1076 : OqFns (openingQueriesLoops.getD 15 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1076, Data.core1527,
    coreProgram_find?_at (j := 1076) rfl, rfl, oqBody_1076,
    coreProgram_find?_at (j := 1527) rfl, rfl, oqLoopBody_1076⟩

set_option maxRecDepth 100000 in
/-- Entry 16, `opening_queries__L0_L0_L4_L16_L13_L7_L3_L6_L12_L4_L1`. -/
theorem oqFns_1079 : OqFns (openingQueriesLoops.getD 16 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L6_L7, Data.core1079, Data.core1528,
    coreProgram_find?_at (j := 1079) rfl, rfl, oqBody_1079,
    coreProgram_find?_at (j := 1528) rfl, rfl, oqLoopBody_1079⟩

set_option maxRecDepth 100000 in
/-- Entry 17, `opening_queries__L0_L0_L4_L16_L14_L2_L3_L6_L12_L4_L1`. -/
theorem oqFns_1080 : OqFns (openingQueriesLoops.getD 17 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L2, Data.core1080, Data.core1529,
    coreProgram_find?_at (j := 1080) rfl, rfl, oqBody_1080,
    coreProgram_find?_at (j := 1529) rfl, rfl, oqLoopBody_1080⟩

set_option maxRecDepth 100000 in
/-- Entry 18, `opening_queries__L0_L0_L4_L16_L15_L3_L3_L6_L12_L4_L1`. -/
theorem oqFns_1081 : OqFns (openingQueriesLoops.getD 18 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1081, Data.core1530,
    coreProgram_find?_at (j := 1081) rfl, rfl, oqBody_1081,
    coreProgram_find?_at (j := 1530) rfl, rfl, oqLoopBody_1081⟩

set_option maxRecDepth 100000 in
/-- Entry 19, `opening_queries__L0_L0_L4_L16_L16_L4_L3_L6_L12_L4_L1`. -/
theorem oqFns_1082 : OqFns (openingQueriesLoops.getD 19 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1082, Data.core1531,
    coreProgram_find?_at (j := 1082) rfl, rfl, oqBody_1082,
    coreProgram_find?_at (j := 1531) rfl, rfl, oqLoopBody_1082⟩

set_option maxRecDepth 100000 in
/-- Entry 20, `opening_queries__L0_L1_L6_L32_L17_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1110 : OqFns (openingQueriesLoops.getD 20 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1110, Data.core1532,
    coreProgram_find?_at (j := 1110) rfl, rfl, oqBody_1110,
    coreProgram_find?_at (j := 1532) rfl, rfl, oqLoopBody_1110⟩

set_option maxRecDepth 100000 in
/-- Entry 21, `opening_queries__L1_L1_L6_L32_L20_L2_L0_L0_L0_L0_L0`. -/
theorem oqFns_1111 : OqFns (openingQueriesLoops.getD 21 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1111, Data.core1534,
    coreProgram_find?_at (j := 1111) rfl, rfl, oqBody_1111,
    coreProgram_find?_at (j := 1534) rfl, rfl, oqLoopBody_1111⟩

set_option maxRecDepth 100000 in
/-- Entry 22, `opening_queries__L0_L0_L4_L16_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1116 : OqFns (openingQueriesLoops.getD 22 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1116, Data.core1535,
    coreProgram_find?_at (j := 1116) rfl, rfl, oqBody_1116,
    coreProgram_find?_at (j := 1535) rfl, rfl, oqLoopBody_1116⟩

set_option maxRecDepth 100000 in
/-- Entry 23, `opening_queries__L0_L0_L4_L16_L14_L2_L4_L10_L20_L5_L1`. -/
theorem oqFns_1119 : OqFns (openingQueriesLoops.getD 23 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L2, Data.core1119, Data.core1536,
    coreProgram_find?_at (j := 1119) rfl, rfl, oqBody_1119,
    coreProgram_find?_at (j := 1536) rfl, rfl, oqLoopBody_1119⟩

set_option maxRecDepth 100000 in
/-- Entry 24, `opening_queries__L0_L0_L4_L16_L15_L3_L4_L10_L20_L5_L1`. -/
theorem oqFns_1120 : OqFns (openingQueriesLoops.getD 24 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1120, Data.core1537,
    coreProgram_find?_at (j := 1120) rfl, rfl, oqBody_1120,
    coreProgram_find?_at (j := 1537) rfl, rfl, oqLoopBody_1120⟩

set_option maxRecDepth 100000 in
/-- Entry 25, `opening_queries__L0_L0_L4_L16_L16_L4_L4_L10_L20_L5_L1`. -/
theorem oqFns_1121 : OqFns (openingQueriesLoops.getD 25 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1121, Data.core1538,
    coreProgram_find?_at (j := 1121) rfl, rfl, oqBody_1121,
    coreProgram_find?_at (j := 1538) rfl, rfl, oqLoopBody_1121⟩

set_option maxRecDepth 100000 in
/-- Entry 26, `opening_queries__L0_L0_L4_L16_L17_L5_L4_L10_L20_L5_L1`. -/
theorem oqFns_1122 : OqFns (openingQueriesLoops.getD 26 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1122, Data.core1539,
    coreProgram_find?_at (j := 1122) rfl, rfl, oqBody_1122,
    coreProgram_find?_at (j := 1539) rfl, rfl, oqLoopBody_1122⟩

set_option maxRecDepth 100000 in
/-- Entry 27, `opening_queries__L0_L1_L6_L32_L18_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1150 : OqFns (openingQueriesLoops.getD 27 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1150, Data.core1540,
    coreProgram_find?_at (j := 1150) rfl, rfl, oqBody_1150,
    coreProgram_find?_at (j := 1540) rfl, rfl, oqLoopBody_1150⟩

set_option maxRecDepth 100000 in
/-- Entry 28, `opening_queries__L1_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1151 : OqFns (openingQueriesLoops.getD 28 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1151, Data.core1542,
    coreProgram_find?_at (j := 1151) rfl, rfl, oqBody_1151,
    coreProgram_find?_at (j := 1542) rfl, rfl, oqLoopBody_1151⟩

set_option maxRecDepth 100000 in
/-- Entry 29, `opening_queries__L0_L0_L4_L16_L20_L2_L0_L0_L0_L0_L0`. -/
theorem oqFns_1156 : OqFns (openingQueriesLoops.getD 29 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1156, Data.core1543,
    coreProgram_find?_at (j := 1156) rfl, rfl, oqBody_1156,
    coreProgram_find?_at (j := 1543) rfl, rfl, oqLoopBody_1156⟩

set_option maxRecDepth 100000 in
/-- Entry 30, `opening_queries__L0_L0_L4_L16_L15_L3_L5_L15_L36_L6_L1`. -/
theorem oqFns_1159 : OqFns (openingQueriesLoops.getD 30 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L3, Data.core1159, Data.core1544,
    coreProgram_find?_at (j := 1159) rfl, rfl, oqBody_1159,
    coreProgram_find?_at (j := 1544) rfl, rfl, oqLoopBody_1159⟩

set_option maxRecDepth 100000 in
/-- Entry 31, `opening_queries__L0_L0_L4_L16_L16_L4_L5_L15_L36_L6_L1`. -/
theorem oqFns_1160 : OqFns (openingQueriesLoops.getD 31 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1160, Data.core1545,
    coreProgram_find?_at (j := 1160) rfl, rfl, oqBody_1160,
    coreProgram_find?_at (j := 1545) rfl, rfl, oqLoopBody_1160⟩

set_option maxRecDepth 100000 in
/-- Entry 32, `opening_queries__L0_L0_L4_L16_L17_L5_L5_L15_L36_L6_L1`. -/
theorem oqFns_1161 : OqFns (openingQueriesLoops.getD 32 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1161, Data.core1546,
    coreProgram_find?_at (j := 1161) rfl, rfl, oqBody_1161,
    coreProgram_find?_at (j := 1546) rfl, rfl, oqLoopBody_1161⟩

set_option maxRecDepth 100000 in
/-- Entry 33, `opening_queries__L0_L0_L4_L16_L18_L6_L5_L15_L36_L6_L1`. -/
theorem oqFns_1162 : OqFns (openingQueriesLoops.getD 33 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1162, Data.core1547,
    coreProgram_find?_at (j := 1162) rfl, rfl, oqBody_1162,
    coreProgram_find?_at (j := 1547) rfl, rfl, oqLoopBody_1162⟩

set_option maxRecDepth 100000 in
/-- Entry 34, `opening_queries__L0_L1_L6_L32_L19_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1190 : OqFns (openingQueriesLoops.getD 34 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1190, Data.core1548,
    coreProgram_find?_at (j := 1190) rfl, rfl, oqBody_1190,
    coreProgram_find?_at (j := 1548) rfl, rfl, oqLoopBody_1190⟩

set_option maxRecDepth 100000 in
/-- Entry 35, `opening_queries__L1_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1191 : OqFns (openingQueriesLoops.getD 35 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L4, Data.core1191, Data.core1550,
    coreProgram_find?_at (j := 1191) rfl, rfl, oqBody_1191,
    coreProgram_find?_at (j := 1550) rfl, rfl, oqLoopBody_1191⟩

set_option maxRecDepth 100000 in
/-- Entry 36, `opening_queries__L0_L0_L4_L16_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1195 : OqFns (openingQueriesLoops.getD 36 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1195, Data.core1551,
    coreProgram_find?_at (j := 1195) rfl, rfl, oqBody_1195,
    coreProgram_find?_at (j := 1551) rfl, rfl, oqLoopBody_1195⟩

set_option maxRecDepth 100000 in
/-- Entry 37, `opening_queries__L0_L0_L4_L16_L16_L4_L2_L3_L8_L3_L1`. -/
theorem oqFns_1199 : OqFns (openingQueriesLoops.getD 37 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L4, Data.core1199, Data.core1552,
    coreProgram_find?_at (j := 1199) rfl, rfl, oqBody_1199,
    coreProgram_find?_at (j := 1552) rfl, rfl, oqLoopBody_1199⟩

set_option maxRecDepth 100000 in
/-- Entry 38, `opening_queries__L0_L0_L4_L16_L17_L5_L2_L3_L8_L3_L1`. -/
theorem oqFns_1200 : OqFns (openingQueriesLoops.getD 38 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1200, Data.core1553,
    coreProgram_find?_at (j := 1200) rfl, rfl, oqBody_1200,
    coreProgram_find?_at (j := 1553) rfl, rfl, oqLoopBody_1200⟩

set_option maxRecDepth 100000 in
/-- Entry 39, `opening_queries__L0_L0_L4_L16_L18_L6_L2_L3_L8_L3_L1`. -/
theorem oqFns_1201 : OqFns (openingQueriesLoops.getD 39 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1201, Data.core1554,
    coreProgram_find?_at (j := 1201) rfl, rfl, oqBody_1201,
    coreProgram_find?_at (j := 1554) rfl, rfl, oqLoopBody_1201⟩

set_option maxRecDepth 100000 in
/-- Entry 40, `opening_queries__L0_L1_L6_L32_L20_L8_L0_L0_L0_L0_L0`. -/
theorem oqFns_1236 : OqFns (openingQueriesLoops.getD 40 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L8, Data.core1236, Data.core1555,
    coreProgram_find?_at (j := 1236) rfl, rfl, oqBody_1236,
    coreProgram_find?_at (j := 1555) rfl, rfl, oqLoopBody_1236⟩

set_option maxRecDepth 100000 in
/-- Entry 41, `opening_queries__L1_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1237 : OqFns (openingQueriesLoops.getD 41 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L5, Data.core1237, Data.core1557,
    coreProgram_find?_at (j := 1237) rfl, rfl, oqBody_1237,
    coreProgram_find?_at (j := 1557) rfl, rfl, oqLoopBody_1237⟩

set_option maxRecDepth 100000 in
/-- Entry 42, `opening_queries__L0_L0_L4_L16_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1241 : OqFns (openingQueriesLoops.getD 42 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L4, Data.core1241, Data.core1558,
    coreProgram_find?_at (j := 1241) rfl, rfl, oqBody_1241,
    coreProgram_find?_at (j := 1558) rfl, rfl, oqLoopBody_1241⟩

set_option maxRecDepth 100000 in
/-- Entry 43, `opening_queries__L0_L0_L4_L16_L17_L5_L3_L6_L12_L4_L1`. -/
theorem oqFns_1245 : OqFns (openingQueriesLoops.getD 43 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L5, Data.core1245, Data.core1559,
    coreProgram_find?_at (j := 1245) rfl, rfl, oqBody_1245,
    coreProgram_find?_at (j := 1559) rfl, rfl, oqLoopBody_1245⟩

set_option maxRecDepth 100000 in
/-- Entry 44, `opening_queries__L0_L0_L4_L16_L18_L6_L3_L6_L12_L4_L1`. -/
theorem oqFns_1246 : OqFns (openingQueriesLoops.getD 44 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1246, Data.core1560,
    coreProgram_find?_at (j := 1246) rfl, rfl, oqBody_1246,
    coreProgram_find?_at (j := 1560) rfl, rfl, oqLoopBody_1246⟩

set_option maxRecDepth 100000 in
/-- Entry 45, `opening_queries__L0_L0_L4_L16_L19_L7_L3_L6_L12_L4_L1`. -/
theorem oqFns_1247 : OqFns (openingQueriesLoops.getD 45 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1247, Data.core1561,
    coreProgram_find?_at (j := 1247) rfl, rfl, oqBody_1247,
    coreProgram_find?_at (j := 1561) rfl, rfl, oqLoopBody_1247⟩

set_option maxRecDepth 100000 in
/-- Entry 46, `opening_queries__L0_L1_L6_L32_L21_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1280 : OqFns (openingQueriesLoops.getD 46 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1280, Data.core1562,
    coreProgram_find?_at (j := 1280) rfl, rfl, oqBody_1280,
    coreProgram_find?_at (j := 1562) rfl, rfl, oqLoopBody_1280⟩

set_option maxRecDepth 100000 in
/-- Entry 47, `opening_queries__L1_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1281 : OqFns (openingQueriesLoops.getD 47 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L6, Data.core1281, Data.core1564,
    coreProgram_find?_at (j := 1281) rfl, rfl, oqBody_1281,
    coreProgram_find?_at (j := 1564) rfl, rfl, oqLoopBody_1281⟩

set_option maxRecDepth 100000 in
/-- Entry 48, `opening_queries__L0_L0_L4_L16_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1285 : OqFns (openingQueriesLoops.getD 48 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L5, Data.core1285, Data.core1565,
    coreProgram_find?_at (j := 1285) rfl, rfl, oqBody_1285,
    coreProgram_find?_at (j := 1565) rfl, rfl, oqLoopBody_1285⟩

set_option maxRecDepth 100000 in
/-- Entry 49, `opening_queries__L0_L0_L4_L16_L18_L6_L4_L10_L20_L5_L1`. -/
theorem oqFns_1289 : OqFns (openingQueriesLoops.getD 49 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L6, Data.core1289, Data.core1566,
    coreProgram_find?_at (j := 1289) rfl, rfl, oqBody_1289,
    coreProgram_find?_at (j := 1566) rfl, rfl, oqLoopBody_1289⟩

set_option maxRecDepth 100000 in
/-- Entry 50, `opening_queries__L0_L0_L4_L16_L19_L7_L4_L10_L20_L5_L1`. -/
theorem oqFns_1290 : OqFns (openingQueriesLoops.getD 50 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1290, Data.core1567,
    coreProgram_find?_at (j := 1290) rfl, rfl, oqBody_1290,
    coreProgram_find?_at (j := 1567) rfl, rfl, oqLoopBody_1290⟩

set_option maxRecDepth 100000 in
/-- Entry 51, `opening_queries__L0_L0_L4_L16_L20_L2_L4_L10_L20_L5_L1`. -/
theorem oqFns_1291 : OqFns (openingQueriesLoops.getD 51 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1291, Data.core1568,
    coreProgram_find?_at (j := 1291) rfl, rfl, oqBody_1291,
    coreProgram_find?_at (j := 1568) rfl, rfl, oqLoopBody_1291⟩

set_option maxRecDepth 100000 in
/-- Entry 52, `opening_queries__L0_L1_L6_L32_L22_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1324 : OqFns (openingQueriesLoops.getD 52 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L4, Data.core1324, Data.core1569,
    coreProgram_find?_at (j := 1324) rfl, rfl, oqBody_1324,
    coreProgram_find?_at (j := 1569) rfl, rfl, oqLoopBody_1324⟩

set_option maxRecDepth 100000 in
/-- Entry 53, `opening_queries__L1_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1325 : OqFns (openingQueriesLoops.getD 53 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L7, Data.core1325, Data.core1571,
    coreProgram_find?_at (j := 1325) rfl, rfl, oqBody_1325,
    coreProgram_find?_at (j := 1571) rfl, rfl, oqLoopBody_1325⟩

set_option maxRecDepth 100000 in
/-- Entry 54, `opening_queries__L0_L0_L4_L16_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1329 : OqFns (openingQueriesLoops.getD 54 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L6, Data.core1329, Data.core1572,
    coreProgram_find?_at (j := 1329) rfl, rfl, oqBody_1329,
    coreProgram_find?_at (j := 1572) rfl, rfl, oqLoopBody_1329⟩

set_option maxRecDepth 100000 in
/-- Entry 55, `opening_queries__L0_L0_L4_L16_L19_L7_L5_L15_L36_L6_L1`. -/
theorem oqFns_1332 : OqFns (openingQueriesLoops.getD 55 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1332, Data.core1573,
    coreProgram_find?_at (j := 1332) rfl, rfl, oqBody_1332,
    coreProgram_find?_at (j := 1573) rfl, rfl, oqLoopBody_1332⟩

set_option maxRecDepth 100000 in
/-- Entry 56, `opening_queries__L0_L0_L4_L16_L20_L2_L5_L15_L36_L6_L1`. -/
theorem oqFns_1333 : OqFns (openingQueriesLoops.getD 56 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1333, Data.core1574,
    coreProgram_find?_at (j := 1333) rfl, rfl, oqBody_1333,
    coreProgram_find?_at (j := 1574) rfl, rfl, oqLoopBody_1333⟩

set_option maxRecDepth 100000 in
/-- Entry 57, `opening_queries__L0_L0_L4_L16_L21_L3_L5_L15_L36_L6_L1`. -/
theorem oqFns_1334 : OqFns (openingQueriesLoops.getD 57 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1334, Data.core1575,
    coreProgram_find?_at (j := 1334) rfl, rfl, oqBody_1334,
    coreProgram_find?_at (j := 1575) rfl, rfl, oqLoopBody_1334⟩

set_option maxRecDepth 100000 in
/-- Entry 58, `opening_queries__L0_L1_L6_L32_L23_L5_L0_L0_L0_L0_L0`. -/
theorem oqFns_1367 : OqFns (openingQueriesLoops.getD 58 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L5, Data.core1367, Data.core1576,
    coreProgram_find?_at (j := 1367) rfl, rfl, oqBody_1367,
    coreProgram_find?_at (j := 1576) rfl, rfl, oqLoopBody_1367⟩

set_option maxRecDepth 100000 in
/-- Entry 59, `opening_queries__L1_L1_L6_L32_L26_L2_L0_L0_L0_L0_L0`. -/
theorem oqFns_1368 : OqFns (openingQueriesLoops.getD 59 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L24_L2, Data.core1368, Data.core1578,
    coreProgram_find?_at (j := 1368) rfl, rfl, oqBody_1368,
    coreProgram_find?_at (j := 1578) rfl, rfl, oqLoopBody_1368⟩

set_option maxRecDepth 100000 in
/-- Entry 60, `opening_queries__L0_L0_L4_L16_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1372 : OqFns (openingQueriesLoops.getD 60 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L7, Data.core1372, Data.core1579,
    coreProgram_find?_at (j := 1372) rfl, rfl, oqBody_1372,
    coreProgram_find?_at (j := 1579) rfl, rfl, oqLoopBody_1372⟩

set_option maxRecDepth 100000 in
/-- Entry 61, `opening_queries__L0_L0_L4_L16_L19_L7_L2_L3_L8_L3_L1`. -/
theorem oqFns_1377 : OqFns (openingQueriesLoops.getD 61 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L12_L7, Data.core1377, Data.core1580,
    coreProgram_find?_at (j := 1377) rfl, rfl, oqBody_1377,
    coreProgram_find?_at (j := 1580) rfl, rfl, oqLoopBody_1377⟩

set_option maxRecDepth 100000 in
/-- Entry 62, `opening_queries__L0_L0_L4_L16_L20_L2_L2_L3_L8_L3_L1`. -/
theorem oqFns_1378 : OqFns (openingQueriesLoops.getD 62 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1378, Data.core1581,
    coreProgram_find?_at (j := 1378) rfl, rfl, oqBody_1378,
    coreProgram_find?_at (j := 1581) rfl, rfl, oqLoopBody_1378⟩

set_option maxRecDepth 100000 in
/-- Entry 63, `opening_queries__L0_L0_L4_L16_L21_L3_L2_L3_L8_L3_L1`. -/
theorem oqFns_1379 : OqFns (openingQueriesLoops.getD 63 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1379, Data.core1582,
    coreProgram_find?_at (j := 1379) rfl, rfl, oqBody_1379,
    coreProgram_find?_at (j := 1582) rfl, rfl, oqLoopBody_1379⟩

set_option maxRecDepth 100000 in
/-- Entry 64, `opening_queries__L0_L1_L6_L32_L24_L6_L0_L0_L0_L0_L0`. -/
theorem oqFns_1417 : OqFns (openingQueriesLoops.getD 64 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L6, Data.core1417, Data.core1583,
    coreProgram_find?_at (j := 1417) rfl, rfl, oqBody_1417,
    coreProgram_find?_at (j := 1583) rfl, rfl, oqLoopBody_1417⟩

set_option maxRecDepth 100000 in
/-- Entry 65, `opening_queries__L1_L1_L6_L32_L27_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1418 : OqFns (openingQueriesLoops.getD 65 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L24_L3, Data.core1418, Data.core1585,
    coreProgram_find?_at (j := 1418) rfl, rfl, oqBody_1418,
    coreProgram_find?_at (j := 1585) rfl, rfl, oqLoopBody_1418⟩

set_option maxRecDepth 100000 in
/-- Entry 66, `opening_queries__L0_L0_L4_L16_L26_L2_L0_L0_L0_L0_L0`. -/
theorem oqFns_1422 : OqFns (openingQueriesLoops.getD 66 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L24_L2, Data.core1422, Data.core1586,
    coreProgram_find?_at (j := 1422) rfl, rfl, oqBody_1422,
    coreProgram_find?_at (j := 1586) rfl, rfl, oqLoopBody_1422⟩

set_option maxRecDepth 100000 in
/-- Entry 67, `opening_queries__L0_L0_L4_L16_L20_L2_L3_L6_L12_L4_L1`. -/
theorem oqFns_1426 : OqFns (openingQueriesLoops.getD 67 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L2, Data.core1426, Data.core1587,
    coreProgram_find?_at (j := 1426) rfl, rfl, oqBody_1426,
    coreProgram_find?_at (j := 1587) rfl, rfl, oqLoopBody_1426⟩

set_option maxRecDepth 100000 in
/-- Entry 68, `opening_queries__L0_L0_L4_L16_L21_L3_L3_L6_L12_L4_L1`. -/
theorem oqFns_1427 : OqFns (openingQueriesLoops.getD 68 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1427, Data.core1588,
    coreProgram_find?_at (j := 1427) rfl, rfl, oqBody_1427,
    coreProgram_find?_at (j := 1588) rfl, rfl, oqLoopBody_1427⟩

set_option maxRecDepth 100000 in
/-- Entry 69, `opening_queries__L0_L0_L4_L16_L22_L4_L3_L6_L12_L4_L1`. -/
theorem oqFns_1428 : OqFns (openingQueriesLoops.getD 69 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L4, Data.core1428, Data.core1589,
    coreProgram_find?_at (j := 1428) rfl, rfl, oqBody_1428,
    coreProgram_find?_at (j := 1589) rfl, rfl, oqLoopBody_1428⟩

set_option maxRecDepth 100000 in
/-- Entry 70, `opening_queries__L0_L1_L6_L32_L25_L7_L0_L0_L0_L0_L0`. -/
theorem oqFns_1464 : OqFns (openingQueriesLoops.getD 70 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L7, Data.core1464, Data.core1590,
    coreProgram_find?_at (j := 1464) rfl, rfl, oqBody_1464,
    coreProgram_find?_at (j := 1590) rfl, rfl, oqLoopBody_1464⟩

set_option maxRecDepth 100000 in
/-- Entry 71, `opening_queries__L1_L1_L6_L32_L28_L4_L0_L0_L0_L0_L0`. -/
theorem oqFns_1465 : OqFns (openingQueriesLoops.getD 71 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L24_L4, Data.core1465, Data.core1592,
    coreProgram_find?_at (j := 1465) rfl, rfl, oqBody_1465,
    coreProgram_find?_at (j := 1592) rfl, rfl, oqLoopBody_1465⟩

set_option maxRecDepth 100000 in
/-- Entry 72, `opening_queries__L0_L0_L4_L16_L27_L3_L0_L0_L0_L0_L0`. -/
theorem oqFns_1469 : OqFns (openingQueriesLoops.getD 72 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L24_L3, Data.core1469, Data.core1593,
    coreProgram_find?_at (j := 1469) rfl, rfl, oqBody_1469,
    coreProgram_find?_at (j := 1593) rfl, rfl, oqLoopBody_1469⟩

set_option maxRecDepth 100000 in
/-- Entry 73, `opening_queries__L0_L0_L4_L16_L21_L3_L4_L10_L20_L5_L1`. -/
theorem oqFns_1474 : OqFns (openingQueriesLoops.getD 73 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L3, Data.core1474, Data.core1594,
    coreProgram_find?_at (j := 1474) rfl, rfl, oqBody_1474,
    coreProgram_find?_at (j := 1594) rfl, rfl, oqLoopBody_1474⟩

set_option maxRecDepth 100000 in
/-- Entry 74, `opening_queries__L0_L0_L4_L16_L22_L4_L4_L10_L20_L5_L1`. -/
theorem oqFns_1475 : OqFns (openingQueriesLoops.getD 74 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L4, Data.core1475, Data.core1595,
    coreProgram_find?_at (j := 1475) rfl, rfl, oqBody_1475,
    coreProgram_find?_at (j := 1595) rfl, rfl, oqLoopBody_1475⟩

set_option maxRecDepth 100000 in
/-- Entry 75, `opening_queries__L0_L0_L4_L16_L23_L5_L4_L10_L20_L5_L1`. -/
theorem oqFns_1476 : OqFns (openingQueriesLoops.getD 75 oqNone) := by
  unfold OqFns
  exact ⟨wpFn_L18_L5, Data.core1476, Data.core1596,
    coreProgram_find?_at (j := 1476) rfl, rfl, oqBody_1476,
    coreProgram_find?_at (j := 1596) rfl, rfl, oqLoopBody_1476⟩

/-- **Every entry's functions are found with the templates' bodies.** -/
theorem oqFns_all : ∀ p ∈ openingQueriesLoops, OqFns p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  rw [List.getElem_eq_getD oqNone]
  have hi' : i < 76 := hi
  interval_cases i
  exacts [oqFns_1009, oqFns_1011, oqFns_1013, oqFns_1015, oqFns_1022, oqFns_1023, oqFns_1024,
    oqFns_1025, oqFns_1032, oqFns_1038, oqFns_1039, oqFns_1040, oqFns_1041, oqFns_1070,
    oqFns_1071, oqFns_1076, oqFns_1079, oqFns_1080, oqFns_1081, oqFns_1082, oqFns_1110,
    oqFns_1111, oqFns_1116, oqFns_1119, oqFns_1120, oqFns_1121, oqFns_1122, oqFns_1150,
    oqFns_1151, oqFns_1156, oqFns_1159, oqFns_1160, oqFns_1161, oqFns_1162, oqFns_1190,
    oqFns_1191, oqFns_1195, oqFns_1199, oqFns_1200, oqFns_1201, oqFns_1236, oqFns_1237,
    oqFns_1241, oqFns_1245, oqFns_1246, oqFns_1247, oqFns_1280, oqFns_1281, oqFns_1285,
    oqFns_1289, oqFns_1290, oqFns_1291, oqFns_1324, oqFns_1325, oqFns_1329, oqFns_1332,
    oqFns_1333, oqFns_1334, oqFns_1367, oqFns_1368, oqFns_1372, oqFns_1377, oqFns_1378,
    oqFns_1379, oqFns_1417, oqFns_1418, oqFns_1422, oqFns_1426, oqFns_1427, oqFns_1428,
    oqFns_1464, oqFns_1465, oqFns_1469, oqFns_1474, oqFns_1475, oqFns_1476]

end
end LeanVM.Guest.B1
