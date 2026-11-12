/-
  LeanVM.Guest.B1.Place.ArmData

  The decided facts of `open_stacked`'s placed lift at every arm and rate.
-/

module

public import LeanVM.Guest.B1.Place.ArmCalls
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.RateCfg

/-!
# The arms' decided facts

`BodyOk c`: every call statement of the body names a callee of `osKindOf`, every dispatch is on
the rate's selector over four names, and the body takes no frame address. `LvFacts c l`: level
`l`'s helpers are entries of their tables (`level_positions` with its loop `lpLoopA c l`), its
positions' slices fit `ligPosCap`, its `opening_queries` shape matches its row, and its words fit
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
  | _ => true

theorem bodyOkS_dispatch {x : V} {fs : List String} {a r : List V}
    (h : bodyOkS (.dispatch x fs a r) = true) : x = .n osRate ∧ fs.length = 4 := by
  simpa [bodyOkS] using h

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

/-- **The body's decided facts.** -/
def BodyOk (c : OsCfg) : Prop :=
  (osBodyA c).all bodyOkS = true ∧ (osBodyA c).filterMap Main.Stmt.addrS = [] ∧
    c.yrLevel < c.levels.length

instance (c : OsCfg) : Decidable (BodyOk c) := by unfold BodyOk; infer_instance

/-- Level `l`'s `level_positions` loop, from `lpTable`. -/
def lpLoopA (c : OsCfg) (l : ℕ) : String :=
  ((lpTable.find? fun e ↦ e.1 == osPositionsName (osLvA c l)).map (·.2.2.1)).getD ""

/-- Level `l`'s `level_residual` loops, from `lrTable`. -/
def lrLoopsA (c : OsCfg) (l : ℕ) : String × String :=
  ((lrTable.find? fun e ↦ e.1 == osResidualName (osLvA c l)).map (·.2.2.2.2.2)).getD ("", "")

/-- **Level `l`'s decided facts.** -/
def LvFacts (c : OsCfg) (l : ℕ) : Prop :=
  (osPositionsName (osLvA c l), (osLvA c l).squeezes, lpLoopA c l, (osLvA c l).depth,
    (osLvA c l).capDepth) ∈ lpTable ∧
  (osQueriesName c l (osLvA c l), (osLvA c l).queries, lvBase l, (osLvA c l).folds,
    (osLvA c l).leafCells, (osLvA c l).depth, (osLvA c l).capDepth,
    (if l = c.yrLevel then (osLvA c l).logCols else 0),
    (if l = c.yrLevel then c.yrLen + (osLvA c l).folds else 0),
    (if l = c.yrLevel then c.yrLog + 1 else 0), (if l = c.yrLevel then 1 else 0)) ∈ lqTable ∧
  (l < c.yrLevel → (osResidualName (osLvA c l), (osLvA c l).queries, (osLvA c l).logCols,
    (osLvA c l).folds, (osLvA c l).highBits, (lrLoopsA c l).1, (lrLoopsA c l).2) ∈ lrTable) ∧
  (osLvA c l).posOff = l * ligPosCap ∧
  (osLvA c l).squeezes * (128 / (osLvA c l).depth) ≤ ligPosCap ∧
  (osLvA c l).queries ≤ (osLvA c l).squeezes * (128 / (osLvA c l).depth) ∧
  0 < 128 / (osLvA c l).depth ∧ 1 ≤ (osLvA c l).squeezes ∧
  (oqSA c l).pd + (oqSA c l).cd = (osLvA c l).depth ∧ (oqSA c l).cd = (osLvA c l).capDepth ∧
  ((oqSA c l).final = 1 ↔ l = c.yrLevel) ∧
  2 * (osLvA c l).foldsOff + 2 * (oqSA c l).folds ≤ 2 * c.nFolds ∧
  (l = c.yrLevel → (oqSA c l).nHs ≤ c.yrLen + (osLvA c l).folds) ∧
  (osLvA c l).logCols ≤ ligColsCap ∧ (osLvA c l).folds ≤ hsStride ∧
  oqQA c l = (osLvA c l).queries

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
instance (c : OsCfg) (l : ℕ) : Decidable (LvFacts c l) := by unfold LvFacts; infer_instance

set_option maxRecDepth 100000 in
theorem armBody_0 : BodyOk (osCfg 0) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_1 : BodyOk (osCfg 1) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_2 : BodyOk (osCfg 2) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_3 : BodyOk (osCfg 3) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_4 : BodyOk (osCfg 4) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_5 : BodyOk (osCfg 5) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_6 : BodyOk (osCfg 6) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_7 : BodyOk (osCfg 7) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_8 : BodyOk (osCfg 8) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_9 : BodyOk (osCfg 9) := by decide +kernel

set_option maxRecDepth 100000 in
theorem armBody_10 : BodyOk (osCfg 10) := by decide +kernel

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

theorem armBody_cfg (m : ℕ) (hm : m < 11) : BodyOk (osCfg m) := by
  interval_cases m
  · exact armBody_0
  · exact armBody_1
  · exact armBody_2
  · exact armBody_3
  · exact armBody_4
  · exact armBody_5
  · exact armBody_6
  · exact armBody_7
  · exact armBody_8
  · exact armBody_9
  · exact armBody_10

theorem osBodyA_rate {m ri : ℕ} (hm : m < ligNSizes) (hri : ri < ligNRates) :
    osBodyA (osCfgR m ri) = osBodyA (osCfg m) := by
  have h := osBody_rate hm hri
  rw [osBody_eq, osBody_eq] at h
  have hl : [Stmt.ret (osBodyRet (osCfg m))].length = [Stmt.ret (osBodyRet (osCfgR m ri))].length := by
    rw [List.length_singleton, List.length_singleton]
  exact (List.append_inj' h hl).1.symm

/-- **Every arm's body has its decided facts at every rate.** -/
theorem armBody_ok {m ri : ℕ} (hm : m < 11) (hri : ri < 4) : BodyOk (osCfgR m ri) := by
  have h := armBody_cfg m hm
  unfold BodyOk at h ⊢
  rw [osBodyA_rate hm hri]
  refine ⟨h.1, h.2.1, ?_⟩
  have e : (osCfgR m ri).yrLevel = (osCfg m).yrLevel := rfl
  have e3 : (osCfgR m ri).levels.length = (osCfg m).levels.length := by
    simp [osCfgR, osCfg, osLevelsR]
  rw [e, e3]
  exact h.2.2

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
