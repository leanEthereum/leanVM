module

public import LeanVM.Guest.Fast.WhirTables
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Whir.InterfaceW

/-!
# `open_stacked`'s tables, checked

* `callMatch r c`: the `OsCall` `r` is the `level_queries` dispatch `c` of the template
  (`osQCalls`) in numbers: its shape, its odd query and iterations, its depth, its arguments' and
  returns' cells (cells all), its callee the `level_queries` specialization of `r.lq`, whose
  `opening_queries` call (`lqCall`) is `r.fn`'s on the cells `r.qargs` returning `r.pw + 2`, its loop
  and its queries' `walk_path` the functions of `r`'s indices (`decoderFunctionName`,
  `Fast/FunctionNames.lean`);
* `osWordsTab_eq`, `callsOK`: the literal tables of `Fast/WhirTables.lean` are the template's at
  every size and rate, by kernel evaluation, a size and rate at a time (`callsOK_j`, at the index
  `j = (r - 1) * 11 + m`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A cell's number. -/
def vIdx (v : V) : ℕ := v.idx

/-- Whether a value is the cell of its number. -/
def isN (v : V) : Bool := v == .n v.idx

/-- **The table's call `r` is the template's dispatch `c`.** -/
noncomputable def callMatch (r : OsCall) : ℕ × OsLv × String × List V × List V → Bool
  | (lvl, lv, _, args, rets) =>
    r.base == (lvOq lvl lv).base && r.I == (lvOq lvl lv).I && r.pd == (lvOq lvl lv).pd &&
      r.cd == (lvOq lvl lv).cd && r.odd == lv.queries % 2 * (if lvl = 0 then 1 else 0) &&
      r.N == lv.queries / (1 + if lvl = 0 then 1 else 0) && r.depth == lv.depth &&
      r.cd == lv.capDepth && r.args == args.map vIdx && r.rets == rets.map vIdx &&
      args.all isN && rets.all isN && decoderFunctionName r.lq == osQueriesName lvl lv &&
      decide (lqCall lvl lv = (decoderFunctionName r.fn, r.qargs.map V.n, [V.n (r.pw + 2)])) &&
      decoderFunctionName r.loop == oqLoopOf (oqNameOf lvl lv) &&
      decoderFunctionName r.walk == oqWalkOf (lvOq lvl lv)

/-- The configuration at the index `j = (r - 1) * 11 + m`. -/
def osCfgAt (j : ℕ) : OsCfg := osCfgR (j % 11) (j / 11)

/-- The `level_queries` dispatches at the index `j`. -/
def osCallsOf (j : ℕ) : List (ℕ × OsLv × String × List V × List V) :=
  osQCalls (osCfgAt j) 0 (osCfgAt j).levels (osHead (osCfgAt j)).2

theorem osWordsTab_eq : osWordsTab = (List.range 44).map fun j ↦ osWordsLen (osCfgAt j) := by
  decide +kernel

/-- The calls at the index `j` are the table's. -/
def CallsOK (j : ℕ) : Prop :=
  (osCallsTab.getD j []).length = (osCallsOf j).length ∧
    ((osCallsTab.getD j []).zip (osCallsOf j)).all (fun p ↦ callMatch p.1 p.2) = true

theorem callsOK_0 : CallsOK 0 := by unfold CallsOK; decide +kernel

theorem callsOK_1 : CallsOK 1 := by unfold CallsOK; decide +kernel

theorem callsOK_2 : CallsOK 2 := by unfold CallsOK; decide +kernel

theorem callsOK_3 : CallsOK 3 := by unfold CallsOK; decide +kernel

theorem callsOK_4 : CallsOK 4 := by unfold CallsOK; decide +kernel

theorem callsOK_5 : CallsOK 5 := by unfold CallsOK; decide +kernel

theorem callsOK_6 : CallsOK 6 := by unfold CallsOK; decide +kernel

theorem callsOK_7 : CallsOK 7 := by unfold CallsOK; decide +kernel

theorem callsOK_8 : CallsOK 8 := by unfold CallsOK; decide +kernel

theorem callsOK_9 : CallsOK 9 := by unfold CallsOK; decide +kernel

theorem callsOK_10 : CallsOK 10 := by unfold CallsOK; decide +kernel

theorem callsOK_11 : CallsOK 11 := by unfold CallsOK; decide +kernel

theorem callsOK_12 : CallsOK 12 := by unfold CallsOK; decide +kernel

theorem callsOK_13 : CallsOK 13 := by unfold CallsOK; decide +kernel

theorem callsOK_14 : CallsOK 14 := by unfold CallsOK; decide +kernel

theorem callsOK_15 : CallsOK 15 := by unfold CallsOK; decide +kernel

theorem callsOK_16 : CallsOK 16 := by unfold CallsOK; decide +kernel

theorem callsOK_17 : CallsOK 17 := by unfold CallsOK; decide +kernel

theorem callsOK_18 : CallsOK 18 := by unfold CallsOK; decide +kernel

theorem callsOK_19 : CallsOK 19 := by unfold CallsOK; decide +kernel

theorem callsOK_20 : CallsOK 20 := by unfold CallsOK; decide +kernel

theorem callsOK_21 : CallsOK 21 := by unfold CallsOK; decide +kernel

theorem callsOK_22 : CallsOK 22 := by unfold CallsOK; decide +kernel

theorem callsOK_23 : CallsOK 23 := by unfold CallsOK; decide +kernel

theorem callsOK_24 : CallsOK 24 := by unfold CallsOK; decide +kernel

theorem callsOK_25 : CallsOK 25 := by unfold CallsOK; decide +kernel

theorem callsOK_26 : CallsOK 26 := by unfold CallsOK; decide +kernel

theorem callsOK_27 : CallsOK 27 := by unfold CallsOK; decide +kernel

theorem callsOK_28 : CallsOK 28 := by unfold CallsOK; decide +kernel

theorem callsOK_29 : CallsOK 29 := by unfold CallsOK; decide +kernel

theorem callsOK_30 : CallsOK 30 := by unfold CallsOK; decide +kernel

theorem callsOK_31 : CallsOK 31 := by unfold CallsOK; decide +kernel

theorem callsOK_32 : CallsOK 32 := by unfold CallsOK; decide +kernel

theorem callsOK_33 : CallsOK 33 := by unfold CallsOK; decide +kernel

theorem callsOK_34 : CallsOK 34 := by unfold CallsOK; decide +kernel

theorem callsOK_35 : CallsOK 35 := by unfold CallsOK; decide +kernel

theorem callsOK_36 : CallsOK 36 := by unfold CallsOK; decide +kernel

theorem callsOK_37 : CallsOK 37 := by unfold CallsOK; decide +kernel

theorem callsOK_38 : CallsOK 38 := by unfold CallsOK; decide +kernel

theorem callsOK_39 : CallsOK 39 := by unfold CallsOK; decide +kernel

theorem callsOK_40 : CallsOK 40 := by unfold CallsOK; decide +kernel

theorem callsOK_41 : CallsOK 41 := by unfold CallsOK; decide +kernel

theorem callsOK_42 : CallsOK 42 := by unfold CallsOK; decide +kernel

theorem callsOK_43 : CallsOK 43 := by unfold CallsOK; decide +kernel

/-- **Every size and rate's calls are the table's.** -/
theorem callsOK : ∀ j < 44, CallsOK j
  | 0, _ => callsOK_0
  | 1, _ => callsOK_1
  | 2, _ => callsOK_2
  | 3, _ => callsOK_3
  | 4, _ => callsOK_4
  | 5, _ => callsOK_5
  | 6, _ => callsOK_6
  | 7, _ => callsOK_7
  | 8, _ => callsOK_8
  | 9, _ => callsOK_9
  | 10, _ => callsOK_10
  | 11, _ => callsOK_11
  | 12, _ => callsOK_12
  | 13, _ => callsOK_13
  | 14, _ => callsOK_14
  | 15, _ => callsOK_15
  | 16, _ => callsOK_16
  | 17, _ => callsOK_17
  | 18, _ => callsOK_18
  | 19, _ => callsOK_19
  | 20, _ => callsOK_20
  | 21, _ => callsOK_21
  | 22, _ => callsOK_22
  | 23, _ => callsOK_23
  | 24, _ => callsOK_24
  | 25, _ => callsOK_25
  | 26, _ => callsOK_26
  | 27, _ => callsOK_27
  | 28, _ => callsOK_28
  | 29, _ => callsOK_29
  | 30, _ => callsOK_30
  | 31, _ => callsOK_31
  | 32, _ => callsOK_32
  | 33, _ => callsOK_33
  | 34, _ => callsOK_34
  | 35, _ => callsOK_35
  | 36, _ => callsOK_36
  | 37, _ => callsOK_37
  | 38, _ => callsOK_38
  | 39, _ => callsOK_39
  | 40, _ => callsOK_40
  | 41, _ => callsOK_41
  | 42, _ => callsOK_42
  | 43, _ => callsOK_43
  | _ + 44, h => absurd h (by omega)

end
end LeanVM.Guest.Fast
