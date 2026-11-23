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

/-!
# The arms' decided facts

`BodyOk c`: every call statement of the body names a callee of `osKindOf`, every dispatch is on
the rate's selector over four names, and the body takes no frame address. `LvFacts c l`: level
`l`'s helpers are entries of their tables (`level_positions` with its loop `lpLoopA c l`), its
positions' slice sits at its offset (`posOff`) and holds its queries, its `opening_queries` shape matches its row, and its words fit
their buffers. `armBody_ok`, `armLv_ok`: both at every arm `m < 11` and rate `ri < 4`, by the
kernel.
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
  (osHead c).1 ++ (osLevels c 0 c.levels (osHead c).2).1 ++ osTlA c

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

set_option maxRecDepth 100000 in
theorem armBody_0 : ∀ ri < 4, BodyOk (osCfgR 0 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_1 : ∀ ri < 4, BodyOk (osCfgR 1 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_2 : ∀ ri < 4, BodyOk (osCfgR 2 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_3 : ∀ ri < 4, BodyOk (osCfgR 3 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_4 : ∀ ri < 4, BodyOk (osCfgR 4 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_5 : ∀ ri < 4, BodyOk (osCfgR 5 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_6 : ∀ ri < 4, BodyOk (osCfgR 6 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_7 : ∀ ri < 4, BodyOk (osCfgR 7 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_8 : ∀ ri < 4, BodyOk (osCfgR 8 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_9 : ∀ ri < 4, BodyOk (osCfgR 9 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_10 : ∀ ri < 4, BodyOk (osCfgR 10 ri) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_0 : ∀ ri < 4, ∀ l < (osCfgR 0 ri).levels.length, LvFacts (osCfgR 0 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_1 : ∀ ri < 4, ∀ l < (osCfgR 1 ri).levels.length, LvFacts (osCfgR 1 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_2 : ∀ ri < 4, ∀ l < (osCfgR 2 ri).levels.length, LvFacts (osCfgR 2 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_3 : ∀ ri < 4, ∀ l < (osCfgR 3 ri).levels.length, LvFacts (osCfgR 3 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_4 : ∀ ri < 4, ∀ l < (osCfgR 4 ri).levels.length, LvFacts (osCfgR 4 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_5 : ∀ ri < 4, ∀ l < (osCfgR 5 ri).levels.length, LvFacts (osCfgR 5 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_6 : ∀ ri < 4, ∀ l < (osCfgR 6 ri).levels.length, LvFacts (osCfgR 6 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_7 : ∀ ri < 4, ∀ l < (osCfgR 7 ri).levels.length, LvFacts (osCfgR 7 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_8 : ∀ ri < 4, ∀ l < (osCfgR 8 ri).levels.length, LvFacts (osCfgR 8 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_9 : ∀ ri < 4, ∀ l < (osCfgR 9 ri).levels.length, LvFacts (osCfgR 9 ri) l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem armLv_10 : ∀ ri < 4, ∀ l < (osCfgR 10 ri).levels.length, LvFacts (osCfgR 10 ri) l := by
  decide +kernel

/-- **Every arm's body has its decided facts at every rate.** -/
theorem armBody_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : BodyOk (osCfgR m ri) := by
  interval_cases m
  · exact armBody_0 ri hri
  · exact armBody_1 ri hri
  · exact armBody_2 ri hri
  · exact armBody_3 ri hri
  · exact armBody_4 ri hri
  · exact armBody_5 ri hri
  · exact armBody_6 ri hri
  · exact armBody_7 ri hri
  · exact armBody_8 ri hri
  · exact armBody_9 ri hri
  · exact armBody_10 ri hri

/-- **Every arm's levels have their decided facts at every rate.** -/
theorem armLv_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) :
    ∀ l < (osCfgR m ri).levels.length, LvFacts (osCfgR m ri) l := by
  interval_cases m
  · exact armLv_0 ri hri
  · exact armLv_1 ri hri
  · exact armLv_2 ri hri
  · exact armLv_3 ri hri
  · exact armLv_4 ri hri
  · exact armLv_5 ri hri
  · exact armLv_6 ri hri
  · exact armLv_7 ri hri
  · exact armLv_8 ri hri
  · exact armLv_9 ri hri
  · exact armLv_10 ri hri

end
end LeanVM.Guest.B1.Arm
