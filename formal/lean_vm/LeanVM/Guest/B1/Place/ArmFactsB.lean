/-
  LeanVM.Guest.B1.Place.ArmFactsB

  open_stacked's per-arm, per-rate facts as decidable checks, and their meaning.
-/

module

public import LeanVM.Guest.B1.Place.ArmFacts
public import LeanVM.Guest.B1.Whir.Names
public import LeanVM.Guest.B1.Place.KidShapes
public import LeanVM.Guest.B1.Place.HonestSizes

/-!
# The arms' facts, checked

The facts of `OsArmFacts m ri`, and the frames' shapes and the rows' shapes the placed lift reads,
as propositions decided by kernel evaluation:

* `ArmBodyP m`: the arm's body not a loop, no `frameAddr`, its dispatches short, its buffers'
  sizes positive and their total below `2^64 - 1`. The body is the same at every rate
  (`osBodyAc_rate`), so it is decided once per arm, at `osCfg m`;
* `ArmRateP m ri`: at the rate's rows `osCfgR m ri`, each level's `LvArm` (its callees' kinds, its
  helpers' table entries, its rows' shapes), the final message's and the folded message's kinds,
  the query positions' total below `2^64 - 1`;
* `KidShapesP c`: `OsKidShapes c`, decidably;
* `LpNodupP`: `lpTable`'s names are distinct, once.

`osArmFacts_of`: with the arm's core IR its template (`OsData m`) and its sizes (`osSizesB`),
they are `OsArmFacts m ri`. `ArmFacts{m}.lean` decide arm `m`'s, `ArmFactsDec.lean` collects
them (both generated), `ArmFactsAll.lean` states them by name.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A body that ends in a `ret` of some word. -/
def notLoopB (b : List Stmt) : Bool :=
  match b.reverse with
  | .ret (_ :: _) :: _ => true
  | _ => false

theorem fn_loop_false {fn : Fn} (h : notLoopB fn.body = true) : fn.loop = false := by
  unfold notLoopB at h
  unfold Fn.loop
  split at h
  · rename_i hr
    rw [hr]
  · exact absurd h (by simp)

/-- A statement that is no dispatch of `2^64 - 1` callees or more. -/
def dispShortS : Stmt → Bool
  | .dispatch _ fs _ _ => decide (fs.length < 2 ^ 64 - 1)
  | _ => true

theorem dispShort_of {pre : List Stmt} (h : pre.all dispShortS = true) : DispShort pre := by
  intro s hs x fs args rets he
  have := List.all_eq_true.mp h s hs
  subst he
  simpa [dispShortS] using this

/-- A statement that is no dispatch, or one on the rate's selector over four callees. -/
def dispRateS : Stmt → Bool
  | .dispatch x fs _ _ => decide (x = .n osRate) && decide (fs.length = 4)
  | _ => true

theorem dispRate_of {pre : List Stmt} (h : pre.all dispRateS = true) :
    ∀ s ∈ pre, ∀ x fs a r, s = .dispatch x fs a r → x = .n osRate ∧ fs.length = 4 := by
  intro s hs x fs a r he
  have := List.all_eq_true.mp h s hs
  subst he
  simpa [dispRateS] using this

/-- **The arm `m`'s body facts**, at `osCfg m`. -/
def ArmBodyP (m : ℕ) : Prop :=
  notLoopB (osBody (osCfg m)) = true ∧
  ((osBodyAc (osCfg m)).filterMap Main.Stmt.addrS).isEmpty = true ∧
  (osBodyAc (osCfg m)).all dispShortS = true ∧
  (osSizesL (osCfg m)).all (0 < ·) = true ∧
  (osSizesL (osCfg m)).sum < 2 ^ 64 - 1 ∧
  (osBodyAc (osCfg m)).all dispRateS = true

instance (m : ℕ) : Decidable (ArmBodyP m) := by unfold ArmBodyP; infer_instance

/-- **Level `i`'s facts at the configuration `c`**: its callees' kinds, its rows' shapes, its
helpers' table entries. -/
structure LvArm (c : OsCfg) (i : ℕ) : Prop where
  ood : i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)
  grind : osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits)
  rw : osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
    natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0))
  pos : osKindOf (osPositionsName (lvAt c i)) = none
  q : osKindOf (osQueriesName i (lvAt c i)) = none
  res : osKindOf (osResidualName (lvAt c i)) = none
  il : 2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl
  lp : (osPositionsName (lvAt c i), (lvAt c i).squeezes, lpLoopOf (osPositionsName (lvAt c i)),
    (lvAt c i).depth, (lvAt c i).capDepth) ∈ lpTable
  lq : (osQueriesName i (lvAt c i), (lvAt c i).queries, (if i = 0 then 1 else 0),
    (lvAt c i).interleave, (lvAt c i).leafCells, (lvAt c i).depth, (lvAt c i).capDepth) ∈ lqTable
  lr : (osResidualName (lvAt c i), (lvAt c i).queries, (lvAt c i).logCols,
    (lrLoopsOf (osResidualName (lvAt c i))).1, (lrLoopsOf (osResidualName (lvAt c i))).2) ∈ lrTable
  posOff : (lvAt c i).posOff = i * ligPosCap
  perSq : 0 < 192 / (lvAt c i).depth
  qSq : (lvAt c i).queries ≤ (lvAt c i).squeezes * (192 / (lvAt c i).depth)
  capD : (lvAt c i).capDepth ≤ (lvAt c i).depth
  posEnd : (lvAt c i).posOff + (lvAt c i).queries ≤ c.levels.length * ligPosCap

/-- `LvArm`'s names, as a decidable proposition. -/
def LvNamesP (c : OsCfg) (i : ℕ) : Prop :=
  (i ≠ c.yrLevel →
    osKindOf ("opening_ood_point__L" ++ natStr (lvAt c i).logCols) = some (.ood (lvAt c i).logCols)) ∧
  osKindOf ("grind_check__L" ++ natStr (lvAt c i).grind) = some (.grind Whir.queryGrindingBits) ∧
  osKindOf ("opening_row_weights__L" ++ natStr (lvAt c i).folds ++ "_L" ++
    natStr (if i = 0 then 1 else 0)) = some (.rw (lvAt c i).folds (if i = 0 then 1 else 0)) ∧
  osKindOf (osPositionsName (lvAt c i)) = none ∧
  osKindOf (osQueriesName i (lvAt c i)) = none ∧
  osKindOf (osResidualName (lvAt c i)) = none ∧
  2 ^ rwLo (lvAt c i).folds + 2 ^ ((lvAt c i).folds - rwLo (lvAt c i).folds) ≤ c.maxIl ∧
  (osPositionsName (lvAt c i), (lvAt c i).squeezes, lpLoopOf (osPositionsName (lvAt c i)),
    (lvAt c i).depth, (lvAt c i).capDepth) ∈ lpTable ∧
  (osQueriesName i (lvAt c i), (lvAt c i).queries, (if i = 0 then 1 else 0), (lvAt c i).interleave,
    (lvAt c i).leafCells, (lvAt c i).depth, (lvAt c i).capDepth) ∈ lqTable ∧
  (osResidualName (lvAt c i), (lvAt c i).queries, (lvAt c i).logCols,
    (lrLoopsOf (osResidualName (lvAt c i))).1, (lrLoopsOf (osResidualName (lvAt c i))).2) ∈ lrTable

instance (c : OsCfg) (i : ℕ) : Decidable (LvNamesP c i) := by unfold LvNamesP; infer_instance

/-- `LvArm`'s shapes, as a decidable proposition. -/
def LvShapeP (c : OsCfg) (i : ℕ) : Prop :=
  (lvAt c i).posOff = i * ligPosCap ∧ 0 < 192 / (lvAt c i).depth ∧
  (lvAt c i).queries ≤ (lvAt c i).squeezes * (192 / (lvAt c i).depth) ∧
  (lvAt c i).capDepth ≤ (lvAt c i).depth ∧
  (lvAt c i).posOff + (lvAt c i).queries ≤ c.levels.length * ligPosCap

instance (c : OsCfg) (i : ℕ) : Decidable (LvShapeP c i) := by unfold LvShapeP; infer_instance

/-- `LvArm`, as a decidable proposition. -/
def LvArmP (c : OsCfg) (i : ℕ) : Prop := LvNamesP c i ∧ LvShapeP c i

instance (c : OsCfg) (i : ℕ) : Decidable (LvArmP c i) := by unfold LvArmP; infer_instance

theorem LvArmP.out {c : OsCfg} {i : ℕ} (h : LvArmP c i) : LvArm c i :=
  let ⟨⟨a1, a2, a3, a6, a7, a8, a9, a10, a11, a12⟩, a13, a14, a15, a16, a17⟩ := h
  ⟨a1, a2, a3, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩

/-- **The arm `m`'s facts at the rate `ri`**, at `osCfgR m ri`. -/
def ArmRateP (m ri : ℕ) : Prop :=
  ri < 4 ∧ (∀ i < (osCfgR m ri).levels.length, LvArmP (osCfgR m ri) i) ∧
  osKindOf ("opening_final_message__L" ++ natStr (osCfgR m ri).yrLen) =
    some (.fm (osCfgR m ri).yrLen) ∧
  osKindOf ("fold_final_msg__L" ++ natStr (osCfgR m ri).yrLog) = some (.ffm (osCfgR m ri).yrLog) ∧
  (osCfgR m ri).levels.length * ligPosCap < 2 ^ 64 - 1

instance (m ri : ℕ) : Decidable (ArmRateP m ri) := by unfold ArmRateP; infer_instance

/-- `OsKidShapes`, as a decidable proposition. -/
def KidShapesP (c : OsCfg) : Prop :=
  (∀ i < c.levels.length, ∀ f ∈ blockNames (lvA c i (lvAt c i) (osLvSt0 c i)), osKindOf f ≠ none) ∧
  (∀ i < c.levels.length, ∀ f ∈ blockNames (lvB c i (lvAt c i) (osLvSt0 c i)),
    osKindOf f = none → f ∈ (c.lvAt i).map (osQueriesName i)) ∧
  (∀ f ∈ blockNames (osTlSt c).1, osKindOf f ≠ none) ∧
  (∀ f ∈ blockNames (osFinA c (osTlSt c).2.1 (osTlSt c).2.2), osKindOf f = none →
    ∃ l < c.levels.length, f ∈ (c.lvAt l).map osResidualName) ∧
  (∀ i < c.levels.length, ∀ l < c.levels.length, ∀ lv ∈ c.lvAt i, ∀ lv' ∈ c.lvAt l,
    osQueriesName i lv ≠ osPositionsName lv' ∧ osQueriesName i lv ≠ osResidualName lv' ∧
      osResidualName lv ≠ osPositionsName lv')

instance (c : OsCfg) : Decidable (KidShapesP c) := by unfold KidShapesP; infer_instance

theorem KidShapesP.out {c : OsCfg} (h : KidShapesP c) : OsKidShapes c :=
  let ⟨a1, a2, a3, a4, a5⟩ := h
  ⟨a1, a2, a3, a4, a5⟩

/-- **`lpTable`'s names are distinct.** -/
def LpNodupP : Prop := (lpTable.map (·.1)).Nodup

instance : Decidable LpNodupP := by unfold LpNodupP; infer_instance

/-! ## The body at every rate -/

theorem osBodyAc_rate (m ri : ℕ) : osBodyAc (osCfgR m ri) = osBodyAc (osCfg m) := by
  have h := osBody_splitC (osCfgR m ri)
  rw [← osBody_rate, osBody_splitC (osCfg m)] at h
  exact (List.append_inj' h (by simp only [List.length_singleton])).1.symm

theorem osSizesL_rate (m ri : ℕ) : osSizesL (osCfgR m ri) = osSizesL (osCfg m) := by
  simp [osSizesL, osCfgR, osCfg, osLevelsR]

theorem openName_arm {m : ℕ} (hm : m < osArms) :
    openName (m + minOpenLog) = "open_stacked__L" ++ natStr m := by
  simp only [openName, openNames, Nat.add_sub_cancel, natStr_eq]
  rw [List.getD_eq_getElem _ _ (by simpa using hm)]
  simp

/-! ## The meaning -/

/-- **The checks' meaning**, the sizes by `osSizesB` (`HonestSizes.lean`). -/
theorem osArmFacts_of {m ri : ℕ} (hm : m < osArms) (hd : OsData m) (hb : ArmBodyP m)
    (hr : ArmRateP m ri) (hs : osSizesB (osCfgR m ri) = true) (hn : LpNodupP) :
    OsArmFacts m ri := by
  have hname := openName_arm hm
  obtain ⟨hloop, haddr, hdisp, hpos, htot, -⟩ := hb
  obtain ⟨hri, hlv, hfm, hffm, -⟩ := hr
  have hl : ∀ i < (osCfgR m ri).levels.length, LvArm (osCfgR m ri) i := fun i hi ↦ (hlv i hi).out
  obtain ⟨fn, hfind, hpar, hbody⟩ := hd
  have hfind' : coreProgram.find? (openName (m + minOpenLog)) = some fn := by rw [hname]; exact hfind
  refine ⟨⟨fn, hfind', hpar, hbody, ?_⟩, ⟨hri, fun i _ ↦ ⟨osCfgR_lvAt_length m ri i,
      osCfgR_lvAt_getD i hri⟩, fun i hi ↦ (hl i hi).ood, fun i hi ↦ (hl i hi).grind, hfm,
      fun i hi ↦ (hl i hi).rw, hffm,
      fun i hi ↦ (hl i hi).pos, fun i hi ↦ (hl i hi).q, fun i hi ↦ (hl i hi).res,
      fun i hi ↦ (hl i hi).il⟩,
    (osSizesB_sound hs).1, ?_, ?_, ?_, ?_, fun i hi ↦ ⟨_, (hl i hi).lp⟩, fun i hi ↦ (hl i hi).lq,
    fun i hi ↦ ⟨_, _, (hl i hi).lr⟩, hn⟩
  · rw [Program.loop_of_find? hfind']
    exact fn_loop_false (by rw [hbody]; exact hloop)
  · rw [osSizesL_rate]
    simpa using hpos
  · rwa [osSizesL_rate]
  · rw [osBodyAc_rate]
    exact List.isEmpty_iff.mp haddr
  · rw [osBodyAc_rate]
    exact dispShort_of hdisp

end
end LeanVM.Guest.B1
