module

public import LeanVM.Guest.Fast.WhirTables
public import LeanVM.Guest.Fast.FunctionNames
public import LeanVM.Guest.B1.Whir.Witness

/-!
# `open_stacked`'s tables, checked

* `osQCalls c`: each level's `level_queries` dispatch of the template at the configuration `c`,
  with the level's index and row, from the state before its queries (`osPreQ`, `osQCallOf`), the
  states threaded as `osLevelsW` threads them (`osLevelsW_eq`);
* `callMatch c r q`: the `OsCall` `r` is the dispatch `q` in numbers: its `opening_queries`
  callee's shape, the indices of `level_queries`' specialization, of its `opening_queries`
  callee, of that callee's loop and of its queries' `walk_path` (`decoderFunctionName`,
  `Fast/FunctionNames.lean`), the loop's iterations, the level's depth and cap depth, the
  dispatch's arguments' and returns' cells (cells all);
* `osWordsTab_eq`, `callsOK`: the literal tables of `Fast/WhirTables.lean` are the template's at
  every size and rate (`osCfgAt j`: size `j % 11`, rate index `j / 11`), by kernel evaluation, a
  configuration at a time (`callsOK_j`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A cell's number. -/
def vIdx (v : V) : ℕ := v.idx

/-- Whether a value is the cell of its number. -/
def isN (v : V) : Bool := v == .n v.idx

/-- Two shapes, field by field. -/
def shapeBEq (a b : OqShape) : Bool :=
  a.odd == b.odd && a.base == b.base && a.folds == b.folds && a.leafCells == b.leafCells &&
    a.depth == b.depth && a.cd == b.cd && a.mu == b.mu && a.vanish == b.vanish &&
    a.nHs == b.nHs && a.hsBits == b.hsBits && a.final == b.final && a.vs == b.vs

theorem eq_of_shapeBEq {a b : OqShape} (h : shapeBEq a b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := b
  simp only [shapeBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rfl

/-- The levels' `level_queries` dispatches from level `lvl` on, with the levels' indices and
rows, the state threaded as `osLevelsW` threads it. -/
def osQCallsFrom (c : OsCfg) : ℕ → List OsLv → OsSt → List (ℕ × OsLv × List V × List V)
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    (lvl, lv, osQCallOf c lvl lv (osPreQ c lvl lv s)) :: osQCallsFrom c (lvl + 1) rest (osLevel c lvl lv s).2

/-- **The levels' `level_queries` dispatches** of the template at the configuration `c`. -/
def osQCalls (c : OsCfg) : List (ℕ × OsLv × List V × List V) := osQCallsFrom c 0 c.levels (osHead c).2

theorem osLevelsW_eq (rd : Reader) (V : FrameMap) (σ : Val) (c : OsCfg) :
    ∀ lvl lvs s, osLevelsW rd V σ c lvl lvs s =
      (osQCallsFrom c lvl lvs s).map fun q ↦ osLevelW rd V c q.1 q.2.1 (q.2.2.1.map σ) (q.2.2.2.map σ)
  | _, [], _ => rfl
  | lvl, lv :: rest, s => by
    rw [osLevelsW, osQCallsFrom, List.map_cons, osLevelsW_eq rd V σ c (lvl + 1) rest]

/-- **The table's call `r` is the dispatch `q`** of the configuration `c`. -/
noncomputable def callMatch (c : OsCfg) (r : OsCall) : ℕ × OsLv × List V × List V → Bool
  | (lvl, lv, args, rets) =>
    shapeBEq (oqShapeAt r.sh) (oqShapeOf (osOqName c lvl lv)) &&
      decoderFunctionName r.lq == osQueriesName c lvl lv &&
      decoderFunctionName r.fn == osOqName c lvl lv &&
      decoderFunctionName r.loop == oqLoopOf (osOqName c lvl lv) &&
      decoderFunctionName r.walk == oqWalkOf (oqShapeOf (osOqName c lvl lv)).oq &&
      r.N == lv.queries / (1 + lvBase lvl) && r.depth == lv.depth && r.cd == lv.capDepth &&
      r.args == args.map vIdx && r.rets == rets.map vIdx && args.all isN && rets.all isN

/-- The configuration at the table's index `j`: the size `j % 11` at the rate index `j / 11`. -/
def osCfgAt (j : ℕ) : OsCfg := osCfgR (j % 11) (j / 11)

theorem osWordsTab_eq : osWordsTab = (List.range 44).map fun j ↦ osWordsLen (osCfgAt j) := by
  decide +kernel

/-- Configuration `j`'s dispatches are the table's. -/
def CallsOK (j : ℕ) : Prop :=
  (osCallsTab.getD j []).length = (osQCalls (osCfgAt j)).length ∧
    ((osCallsTab.getD j []).zip (osQCalls (osCfgAt j))).all
      (fun p ↦ callMatch (osCfgAt j) p.1 p.2) = true

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

/-- **Every configuration's dispatches are the table's.** -/
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
