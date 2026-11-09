module

public import LeanVM.Guest.Fast.WhirTables
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Whir.InterfaceW

/-!
# `open_stacked`'s tables, checked

* `callMatch r c`: the `OsCall` `r` is the `opening_queries` call `c` of the template
  (`osQCalls`) in numbers: its shape, its odd query and iterations, its depth, its arguments' and
  returns' cells (cells all), its callee, its loop and its queries' `walk_path` the functions of
  `r`'s indices (`decoderFunctionName`, `Fast/FunctionNames.lean`);
* `osWordsTab_eq`, `callsOK`: the literal tables of `Fast/WhirTables.lean` are the template's,
  by kernel evaluation, a candidate at a time (`callsOK_m`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A cell's number. -/
def vIdx (v : V) : ℕ := v.idx

/-- Whether a value is the cell of its number. -/
def isN (v : V) : Bool := v == .n v.idx

/-- **The table's call `r` is the template's call `c`.** -/
noncomputable def callMatch (r : OsCall) : ℕ × OsLv × String × List V × List V → Bool
  | (lvl, lv, name, args, rets) =>
    r.base == (lvOq lvl lv).base && r.I == (lvOq lvl lv).I && r.pd == (lvOq lvl lv).pd &&
      r.cd == (lvOq lvl lv).cd && r.odd == lv.queries % 2 * (if lvl = 0 then 1 else 0) &&
      r.N == lv.queries / (1 + if lvl = 0 then 1 else 0) && r.depth == lv.depth &&
      r.args == args.map vIdx && r.rets == rets.map vIdx && args.all isN && rets.all isN &&
      decoderFunctionName r.fn == name && decoderFunctionName r.loop == oqLoopOf name &&
      decoderFunctionName r.walk == oqWalkOf (lvOq lvl lv)

/-- Candidate `m`'s `opening_queries` calls. -/
def osCallsOf (m : ℕ) : List (ℕ × OsLv × String × List V × List V) :=
  osQCalls (osCfg m) 0 (osCfg m).levels (osHead (osCfg m)).2

theorem osWordsTab_eq : osWordsTab = (List.range 28).map fun m ↦ osWordsLen (osCfg m) := by
  decide +kernel

/-- Candidate `m`'s calls are the table's. -/
def CallsOK (m : ℕ) : Prop :=
  (osCallsTab.getD m []).length = (osCallsOf m).length ∧
    ((osCallsTab.getD m []).zip (osCallsOf m)).all (fun p ↦ callMatch p.1 p.2) = true

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

/-- **Every candidate's calls are the table's.** -/
theorem callsOK : ∀ m < 28, CallsOK m
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
  | _ + 28, h => absurd h (by omega)

end
end LeanVM.Guest.Fast
