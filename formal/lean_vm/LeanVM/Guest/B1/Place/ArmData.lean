/-
  LeanVM.Guest.B1.Place.ArmData

  The decided facts of `open_stacked`'s placed lift at every arm and rate.
-/

module

public import LeanVM.Guest.B1.Place.ArmCalls
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.RateCfg
public import LeanVM.Guest.B1.Whir.TableMem
public import LeanVM.Guest.B1.Whir.OqKey
public import LeanVM.Guest.B1.Whir.TableKeys
import LeanVM.Guest.StmtsAppend

/-!
# The arms' decided facts

`BodyOk c`: every call statement of the body names a callee of `osKindOf`, every dispatch is on
the rate's selector over four names, and the body takes no frame address. `LvFacts c l`: level
`l`'s helpers are entries of their tables (`level_positions` with its loop `lpLoopA c l`), its
positions' slice sits at its offset (`posOff`) and holds its queries, its `opening_queries` shape matches its row, and its words fit
their buffers. `armBody_ok`, `armLv_ok`: both at every arm `m < 11` and rate `ri < 4`, by the
kernel, the body once per arm (`bodyOk_rate`: it is the same at every rate).
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- A statement the lift places: a call of a named callee, or a dispatch on the rate's selector
over four names. -/
def bodyOkS : Stmt → Bool
  | .call f _ _ => (osKindOf f).isSome
  | .callIf _ f _ => (osKindOf f).isSome
  | .dispatch x fs _ _ => decide (x = .n osRate) && fs.length == 4
  | .match_ x arms => decide (x = .n osRate) && arms.length == 4 && arms.all fun a ↦ a.all Stmt.quietS
  | _ => true

theorem bodyOkS_dispatch {x : V} {fs : List String} {a r : List V}
    (h : bodyOkS (.dispatch x fs a r) = true) : x = .n osRate ∧ fs.length = 4 := by
  simpa [bodyOkS] using h

theorem bodyOkS_match {x : V} {arms : List (List Stmt)} (h : bodyOkS (.match_ x arms) = true) :
    x = .n osRate ∧ arms.length = 4 ∧ (arms.all fun a ↦ a.all Stmt.quietS) = true := by
  simp only [bodyOkS, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem bodyOkS_call {s : Stmt} (h : bodyOkS s = true) {x : Option V × String × List V × List V}
    (hx : Main.Stmt.callS s = some x) : (osKindOf x.2.1).isSome = true := by
  cases s with
  | call f a r =>
    simp only [Main.Stmt.callS, Option.some.injEq] at hx
    subst hx
    exact h
  | callIf cv f a =>
    simp only [Main.Stmt.callS, Option.some.injEq] at hx
    subst hx
    exact h
  | _ => simp [Main.Stmt.callS] at hx

/-- A call into a specialization of `level_residual` (the finish's, named by `lrTable`). -/
def isLrCall : Stmt → Bool
  | .call f _ _ => lrTable.any (·.1 == f)
  | _ => false

/-- The body before the finish: the head, the levels, the closing rounds. -/
def osBodyPre (c : OsCfg) : List Stmt :=
  (osHead c).1 ⧺ (osLevels c 0 c.levels (osHead c).2).1 ⧺ osTlA c

/-- **The body's decided facts**: every statement placed (a call into `level_residual` aside, which
only the finish makes), the body before the finish placed, `fold_final_msg` named, no frame
address, the final level a level. -/
def BodyOk (c : OsCfg) : Prop :=
  (osBodyA c).all (fun s ↦ bodyOkS s || isLrCall s) = true ∧ (osBodyPre c).all bodyOkS = true ∧
    (osKindOf ("fold_final_msg__L" ++ natStr c.yrLog)).isSome = true ∧
    (osBodyA c).filterMap Main.Stmt.addrS = [] ∧ c.yrLevel < c.levels.length

instance (c : OsCfg) : Decidable (BodyOk c) := by unfold BodyOk; infer_instance

/-- Level `l`'s `level_positions` loop, from `lpTable`'s entry of its depths (`LvFacts` checks the
entry's name). -/
def lpLoopA (c : OsCfg) (l : ℕ) : String :=
  let lv := osLvA c l
  ((lpTable.find? fun e ↦ e.2.2.1 == lv.depth && e.2.2.2 == lv.capDepth).map (·.2.1)).getD ""

/-- Level `l`'s `level_residual` loops, from `lrTable`'s entry of its columns and high part. -/
def lrLoopsA (c : OsCfg) (l : ℕ) : String × String :=
  let lv := osLvA c l
  ((lrTable.find? fun e ↦ e.2.1 == lv.logCols && e.2.2.1 == lv.folds && e.2.2.2.1 == lv.highBits).map
    (·.2.2.2.2)).getD ("", "")

/-- **Level `l`'s decided facts.** -/
def LvFacts (c : OsCfg) (l : ℕ) : Prop :=
  (osPositionsName (osLvA c l), lpLoopA c l, (osLvA c l).depth, (osLvA c l).capDepth) ∈ lpTable ∧
  (osQueriesName c l (osLvA c l), (osLvA c l).queries, lvBase l, (osLvA c l).folds,
    (osLvA c l).leafCells, (osLvA c l).depth, (osLvA c l).capDepth,
    (if l = c.yrLevel then (osLvA c l).logCols else 0),
    (if l = c.yrLevel then c.yrLen + (osLvA c l).folds else 0),
    (if l = c.yrLevel then c.yrLog + 1 else 0), (if l = c.yrLevel then 1 else 0)) ∈ lqTable ∧
  (l < c.yrLevel → (osResidualName (osLvA c l), (osLvA c l).logCols, (osLvA c l).folds,
    (osLvA c l).highBits, (lrLoopsA c l).1, (lrLoopsA c l).2) ∈ lrTable ∧
    resBatch ≤ (osLvA c l).queries ∧ (osLvA c l).queries ≤ 2 ^ 20) ∧
  (osLvA c l).posOff = ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum ∧
  (osLvA c l).queries ≤ (osLvA c l).squeezes * (128 / (osLvA c l).depth) ∧
  0 < 128 / (osLvA c l).depth ∧ 1 ≤ (osLvA c l).squeezes ∧ (osLvA c l).squeezes ≤ 64 ∧
  (oqSA c l).pd + (osLvA c l).capDepth = (osLvA c l).depth ∧
  ((oqSA c l).final = 1 ↔ l = c.yrLevel) ∧
  2 * (osLvA c l).foldsOff + 2 * (oqSA c l).folds ≤ 2 * c.nFolds ∧
  (l = c.yrLevel → (oqSA c l).nHs ≤ c.yrLen + (osLvA c l).folds) ∧
  (osLvA c l).logCols ≤ ligColsCap ∧ (osLvA c l).folds ≤ hsStride ∧
  oqQA c l = (osLvA c l).queries

/-- `LvFacts` by numbers, at the `opening_queries` shape `S`: `LvFacts c l` is it at the shape of
level `l`'s name (`lvFacts_iff`: the tables' names are their numbers, `Whir/TableKeys`), which
the kernel finds by its numbers too (`oqShapeOf_osOqName`). -/
def LvFactsS (S : OqShape) (c : OsCfg) (l : ℕ) : Prop :=
  (lpLoopA c l, (osLvA c l).depth, (osLvA c l).capDepth) ∈ lpTable.map (·.2) ∧
  ((osLvA c l).queries, lvBase l, (osLvA c l).folds, (osLvA c l).leafCells, (osLvA c l).depth,
    (osLvA c l).capDepth, (if l = c.yrLevel then (osLvA c l).logCols else 0),
    (if l = c.yrLevel then c.yrLen + (osLvA c l).folds else 0),
    (if l = c.yrLevel then c.yrLog + 1 else 0), (if l = c.yrLevel then 1 else 0)) ∈ lqTable.map (·.2) ∧
  (l < c.yrLevel → ((osLvA c l).logCols, (osLvA c l).folds, (osLvA c l).highBits, (lrLoopsA c l).1,
    (lrLoopsA c l).2) ∈ lrTable.map (·.2) ∧
    resBatch ≤ (osLvA c l).queries ∧ (osLvA c l).queries ≤ 2 ^ 20) ∧
  (osLvA c l).posOff = ((c.levels.take l).map fun lv ↦ lv.squeezes * (128 / lv.depth)).sum ∧
  (osLvA c l).queries ≤ (osLvA c l).squeezes * (128 / (osLvA c l).depth) ∧
  0 < 128 / (osLvA c l).depth ∧ 1 ≤ (osLvA c l).squeezes ∧ (osLvA c l).squeezes ≤ 64 ∧
  S.oq.pd + (osLvA c l).capDepth = (osLvA c l).depth ∧
  (S.oq.final = 1 ↔ l = c.yrLevel) ∧
  2 * (osLvA c l).foldsOff + 2 * S.oq.folds ≤ 2 * c.nFolds ∧
  (l = c.yrLevel → S.oq.nHs ≤ c.yrLen + (osLvA c l).folds) ∧
  (osLvA c l).logCols ≤ ligColsCap ∧ (osLvA c l).folds ≤ hsStride ∧
  oqCount (lqOdd (osLvA c l).queries (lvBase l)) S.oq.base (oqNA c l) = (osLvA c l).queries

theorem lvFacts_iff (c : OsCfg) (l : ℕ) :
    LvFacts c l ↔ LvFactsS (oqShapeOf (osOqName c l (osLvA c l))) c l := by
  unfold LvFacts LvFactsS
  rw [lp_mem, lq_mem, lr_mem]
  exact Iff.rfl

open scoped LeanVM.Guest.B1.Whir.TableMem in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
instance (S : OqShape) (c : OsCfg) (l : ℕ) : Decidable (LvFactsS S c l) := by
  unfold LvFactsS; infer_instance

instance (c : OsCfg) (l : ℕ) : Decidable (LvFacts c l) :=
  decidable_of_iff (LvFactsS (oqShapeK (osOqKey c l (osLvA c l))) c l) <| by
    rw [lvFacts_iff, oqShapeOf_osOqName]

theorem osBodyPre_wl (c : OsCfg) (L : List OsLv) :
    osBodyPre (c.withLevels L) = osBodyPre (c.withLevels (L.map OsLv.rf)) := by
  simp only [osBodyPre, osTlA, osHead, osTail, osLevels_wl, List.length_map, getD_rf, OsLv.rf_folds,
    List.map_map]
  simp only [Function.comp_def, OsLv.rf_rf]

theorem osBodyPre_rate (m ri : ℕ) : osBodyPre (osCfgR m ri) = osBodyPre (osCfg m) := by
  have h : (osLevelsR m ri).map OsLv.rf = (osLevelsR m 0).map OsLv.rf := by
    simp only [osLevelsR, List.map_map]; rfl
  exact (osBodyPre_wl _ _).trans ((congrArg (fun L ↦ osBodyPre ((osCfg m).withLevels L)) h).trans
    (osBodyPre_wl (osCfg m) (osLevelsR m 0)).symm)

theorem osBodyA_rate (m ri : ℕ) : osBodyA (osCfgR m ri) = osBodyA (osCfg m) := by
  have h := osBody_rate m ri
  rw [osBody_eq, osBody_eq] at h
  exact (List.append_inj_left' h (by simp only [List.length_singleton])).symm

/-- **The body's decided facts are the same at every rate**: the body reads the levels' rate-free
columns alone. -/
theorem bodyOk_rate (m ri : ℕ) : BodyOk (osCfgR m ri) ↔ BodyOk (osCfg m) := by
  have hl : (osCfgR m ri).levels.length = (osCfg m).levels.length :=
    (osCfgR_levels_length m ri).trans (osCfgR_levels_length m 0).symm
  unfold BodyOk
  rw [osBodyA_rate, osBodyPre_rate, hl]
  exact Iff.rfl

theorem armBody_0 : BodyOk (osCfg 0) := by decide +kernel
theorem armBody_1 : BodyOk (osCfg 1) := by decide +kernel
theorem armBody_2 : BodyOk (osCfg 2) := by decide +kernel
theorem armBody_3 : BodyOk (osCfg 3) := by decide +kernel
theorem armBody_4 : BodyOk (osCfg 4) := by decide +kernel
theorem armBody_5 : BodyOk (osCfg 5) := by decide +kernel
theorem armBody_6 : BodyOk (osCfg 6) := by decide +kernel
theorem armBody_7 : BodyOk (osCfg 7) := by decide +kernel
theorem armBody_8 : BodyOk (osCfg 8) := by decide +kernel
theorem armBody_9 : BodyOk (osCfg 9) := by decide +kernel
theorem armBody_10 : BodyOk (osCfg 10) := by decide +kernel

/-- **Every arm's body has its decided facts at every rate** (a kernel check per arm: all at once
hold too much memory). -/
theorem armBody_ok {m : ℕ} (ri : ℕ) (hm : m < 11) : BodyOk (osCfgR m ri) := by
  rw [bodyOk_rate]
  interval_cases m
  exacts [armBody_0, armBody_1, armBody_2, armBody_3, armBody_4, armBody_5, armBody_6, armBody_7,
    armBody_8, armBody_9, armBody_10]

set_option maxRecDepth 100000 in
theorem armLv_all : ∀ m < 11, ∀ ri < 4, ∀ l < (osCfgR m ri).levels.length, LvFacts (osCfgR m ri) l := by
  decide +kernel

/-- **Every arm's levels have their decided facts at every rate.** -/
theorem armLv_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) :
    ∀ l < (osCfgR m ri).levels.length, LvFacts (osCfgR m ri) l :=
  armLv_all m hm ri hri

end
end LeanVM.Guest.B1.Arm
