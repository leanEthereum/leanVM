/-
  LeanVM.Guest.B1.Whir.Facts

  A candidate's static facts as one decidable proposition, for the kernel to decide, and what
  they give.
-/

module

public import LeanVM.Guest.B1.Whir.Levels
public import LeanVM.Guest.B1.Whir.LrSound
public import LeanVM.Guest.B1.Fs.Message
public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Merkle.Meaning
public import LeanVM.Guest.B1.Whir.TableMem
public import LeanVM.Guest.B1.Whir.OqKey
public import LeanVM.Guest.B1.Whir.TableKeys

/-!
# A candidate's facts, decided

`CandOk m ri μ r cfg`: the configuration `Whir.ladder μ r = cfg` against size `m`'s rows at rate
`ri` (`osCfgR m ri`) level by level (`MidOk`, `FinOkF`: the arithmetic `MidFacts`, `FinFacts`,
`LvFin` and the finish need, the names of the level's callees in B1-a's tables and the helpers'
(`lpTable`, `lqTable`, `lrTable`), the `opening_queries` specialization's shape), decided by
the entries' numbers (`Whir/TableKeys`, `Whir/OqKey`). `candB m ri`
decides it at `μ = m + minOpenLog`, `r = ri + 1`; `Whir/Facts{m}.lean` decide it, one size a
module.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open scoped TableMem

@[expose] public section

/-! ## A level's `opening_queries` shape -/

/-- The level's `opening_queries` entry and its shape, checked. -/
def QshOk (c : OsCfg) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Prop :=
  (oqEntry (osOqName c lvl lv)).map (·.1) = some (osOqName c lvl lv) ∧
    (oqShapeOf (osOqName c lvl lv)).odd = lv.queries % 2 * (if lvl = 0 then 1 else 0) ∧
    (oqShapeOf (osOqName c lvl lv)).base = (if lvl = 0 then 1 else 0) ∧
    (oqShapeOf (osOqName c lvl lv)).folds = lv.folds ∧
    (oqShapeOf (osOqName c lvl lv)).depth = lv.depth ∧
    (oqShapeOf (osOqName c lvl lv)).cd = lv.capDepth ∧
    (oqShapeOf (osOqName c lvl lv)).final = fin ∧
    2 ≤ (oqShapeOf (osOqName c lvl lv)).cd ∧ (oqShapeOf (osOqName c lvl lv)).cd ≤ 8 ∧
    (oqShapeOf (osOqName c lvl lv)).cd ≤ (oqShapeOf (osOqName c lvl lv)).depth ∧
    oqCount (oqShapeOf (osOqName c lvl lv)).odd (oqShapeOf (osOqName c lvl lv)).base
      (lv.queries / (1 + if lvl = 0 then 1 else 0)) = lv.queries

/-- `QshOk` by numbers: the entry and shape of the level's numbers (`Whir/OqKey`). -/
def QshOkK (k : List ℕ) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Prop :=
  (oqEntryK k).isSome ∧
    (oqShapeK k).odd = lv.queries % 2 * (if lvl = 0 then 1 else 0) ∧
    (oqShapeK k).base = (if lvl = 0 then 1 else 0) ∧
    (oqShapeK k).folds = lv.folds ∧
    (oqShapeK k).depth = lv.depth ∧
    (oqShapeK k).cd = lv.capDepth ∧
    (oqShapeK k).final = fin ∧
    2 ≤ (oqShapeK k).cd ∧ (oqShapeK k).cd ≤ 8 ∧
    (oqShapeK k).cd ≤ (oqShapeK k).depth ∧
    oqCount (oqShapeK k).odd (oqShapeK k).base
      (lv.queries / (1 + if lvl = 0 then 1 else 0)) = lv.queries

instance (k : List ℕ) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Decidable (QshOkK k lvl lv fin) := by
  unfold QshOkK; infer_instance

instance (c : OsCfg) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Decidable (QshOk c lvl lv fin) :=
  decidable_of_iff (QshOkK (osOqKey c lvl lv) lvl lv fin) <| by
    unfold QshOk QshOkK
    rw [oqEntry_name_iff, oqShapeOf_osOqName]

theorem qshOk_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {fin : ℕ} (h : QshOk c lvl lv fin) :
    QShapeOk c lvl lv fin (oqLoopOf (osOqName c lvl lv)) (oqShapeOf (osOqName c lvl lv)) := by
  obtain ⟨he, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  set name := osOqName c lvl lv
  obtain ⟨e, hE, he1⟩ : ∃ e, oqEntry name = some e ∧ e.1 = name := by
    rcases hE : oqEntry name with _ | e
    · rw [hE] at he; simp at he
    · rw [hE] at he; simp at he; exact ⟨e, rfl, he⟩
  have heq : e = (name, oqLoopOf name, oqShapeOf name) := by
    obtain ⟨a, b, s⟩ := e
    simp only at he1
    simp [oqLoopOf, oqShapeOf, hE, he1]
  have hmem : e ∈ openingQueriesLoops := List.mem_of_find?_eq_some hE
  rw [heq] at hE hmem
  exact ⟨hmem, hE, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-! ## A level's helpers -/

/-- `level_positions`' specialization at the row, in `lpTable`, and its decoder in B1-a's. -/
def LpOk (lv : OsLv) : Prop :=
  (osPositionsName lv, lv.squeezes, lpLoopOf (osPositionsName lv), lv.depth, lv.capDepth) ∈ lpTable ∧
    (dqwName lv.depth lv.capDepth, lv.depth, lv.capDepth) ∈ queryWindowsShapes

instance (lv : OsLv) : Decidable (LpOk lv) :=
  decidable_of_iff ((lv.squeezes, lpLoopK lv, lv.depth, lv.capDepth) ∈ lpTable.map (·.2) ∧
      (dqwName lv.depth lv.capDepth, lv.depth, lv.capDepth) ∈ queryWindowsShapes) <| by
    unfold LpOk
    rw [lp_mem, lpLoopOf_eq]

/-- `level_queries`' specialization at level `lvl`'s row, in `lqTable`. -/
def LqOk (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop :=
  (osQueriesName c lvl lv, lv.queries, lvBase lvl, lv.folds, lv.leafCells, lv.depth, lv.capDepth,
    (if lvl = c.yrLevel then lv.logCols else 0), (if lvl = c.yrLevel then c.yrLen + lv.folds else 0),
    (if lvl = c.yrLevel then c.yrLog + 1 else 0), (if lvl = c.yrLevel then 1 else 0)) ∈ lqTable

instance (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Decidable (LqOk c lvl lv) :=
  decidable_of_iff _ (lq_mem c lvl lv).symm

/-- `level_residual`'s specialization at the row, in `lrTable`, its query count in range. -/
def LrOk (lv : OsLv) : Prop :=
  (osResidualName lv, lv.queries, lv.logCols, lv.folds, lv.highBits,
    (lrLoopsOf (osResidualName lv)).1, (lrLoopsOf (osResidualName lv)).2) ∈ lrTable ∧
    resBatch ≤ lv.queries ∧ lv.queries < ordG

instance (lv : OsLv) : Decidable (LrOk lv) :=
  decidable_of_iff ((lv.queries, lv.logCols, lv.folds, lv.highBits, (lrLoopsK lv).1, (lrLoopsK lv).2) ∈
      lrTable.map (·.2) ∧ resBatch ≤ lv.queries ∧ lv.queries < ordG) <| by
    unfold LrOk
    rw [lr_mem, lrLoopsOf_eq]

theorem lpOk_fn {lv : OsLv} (h : LpOk lv) :
    FnIs (osPositionsName lv) (osParams 9)
        (lpBody lv.squeezes lv.depth lv.capDepth (lpLoopOf (osPositionsName lv))) ∧
      FnIs (lpLoopOf (osPositionsName lv)) (osParams 6)
        (lpLoopBody lv.depth lv.capDepth (lpLoopOf (osPositionsName lv))) := by
  have := lpTable_ok _ h.1
  exact this

theorem lqOk_fn {c : OsCfg} {lvl : ℕ} {lv : OsLv} (h : LqOk c lvl lv) :
    FnIs (osQueriesName c lvl lv) (osParams 6) (osLqBody c lvl lv) := by
  have := lqTable_ok _ h
  exact this

theorem lrOk_fn {lv : OsLv} (h : LrOk lv) :
    FnIs (osResidualName lv) (osParams 4)
        (lrBody lv.queries (lrLoopsOf (osResidualName lv)).1 (lrLoopsOf (osResidualName lv)).2) ∧
      FnIs (lrLoopsOf (osResidualName lv)).1 (osParams 7)
        (lrLoop1Body lv.logCols lv.folds lv.highBits (lrLoopsOf (osResidualName lv)).1) ∧
      (lv.queries % resBatch ≠ 0 → FnIs (lrLoopsOf (osResidualName lv)).2 (osParams 7)
        (lrLoop2Body lv.logCols lv.folds lv.highBits (lrLoopsOf (osResidualName lv)).2)) := by
  have := lrTable_ok _ h.1
  exact this

/-! ## A level's facts -/

/-- A non-final level's facts, checked. -/
def MidOk (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level next : Whir.Level) (lv' : OsLv) : Prop :=
  lvl ≠ c.yrLevel ∧ level.fold = lv.folds ∧ logN - (lv.foldsOff + lv.folds) = lv.logCols ∧
  1 ≤ lv.logCols ∧ lv.depth = lv.logCols + level.logInvRate ∧ level.queries = lv.queries ∧
  0 < lv.queries ∧ lv.queries < u128Bound ∧ 1 ≤ 128 / lv.depth ∧
  lv.squeezes = sqCount (128 / lv.depth) lv.queries ∧
  digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth ∧
  digitsVal (osPowDigits lv.queries) 1 = lv.queries ∧ lv.posOff < u128Bound ∧ 1 ≤ lv.squeezes ∧
  lv.squeezes < ordG ∧ lv.squeezes * 5 < u128Bound ∧ 2 * (lv.foldsOff + lv.folds) < u128Bound ∧
  (lvl + 1) * ligColsCap < u128Bound ∧ lvl * hsStride < u128Bound ∧
  levelShape lv.logCols next (2 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv') ∧
  lv'.foldsOff = lv.foldsOff + lv.folds ∧ QshOk c lvl lv 0 ∧
  lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧ lv.queries / (1 + lvBase lvl) < u128Bound ∧
  -- the callees' names
  (2 + lv.folds, 1) ∈ omDeployed ∧
  omName (2 + lv.folds, 1) = "opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1" ∧
  lv.logCols ∈ spfDeployed ∧ spfName lv.logCols = "squeeze_point_from__L" ++ natStr lv.logCols ∧
  LpOk lv ∧ LqOk c lvl lv ∧
  ("verify_merkle_cap__L" ++ natStr lv.capDepth, lv.capDepth) ∈ merkleCapNames ∧ LrOk lv ∧
  -- the finish's
  lv.prefixLen + c.yrLog = lv.logCols ∧ lv.resFoldOff = lv.foldsOff + lv.folds ∧
  lv.foldsOff + lv.folds ≤ c.nFolds ∧ c.nFolds - (lv.foldsOff + lv.folds) + c.yrLog = lv.logCols ∧
  lv.logCols < 64 ∧ 1 ≤ lv.folds ∧ lv.highBits ≤ 3 ∧ lv.highBits ≤ lv.logCols + 1 ∧
  lv.folds ≤ 2 ^ lv.highBits ∧ lv.vanish = lv.logCols * (lv.logCols + 1) / 2

instance (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level next : Whir.Level) (lv' : OsLv) :
    Decidable (MidOk c logN lvl lv level next lv') := by
  unfold MidOk; infer_instance

/-- The final level's facts, checked. -/
def FinOkF (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level : Whir.Level) : Prop :=
  lvl = c.yrLevel ∧ level.fold = lv.folds ∧ logN - (lv.foldsOff + lv.folds) = c.yrLog ∧
  2 ^ c.yrLog = c.yrLen ∧ lv.depth = c.yrLog + level.logInvRate ∧ level.queries = lv.queries ∧
  0 < lv.queries ∧ lv.queries < u128Bound ∧ 1 ≤ 128 / lv.depth ∧
  lv.squeezes = sqCount (128 / lv.depth) lv.queries ∧
  digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth ∧ lv.posOff < u128Bound ∧
  1 ≤ lv.squeezes ∧ lv.squeezes < ordG ∧ lv.squeezes * 5 < u128Bound ∧
  2 * (lv.foldsOff + lv.folds) < u128Bound ∧ lvl * hsStride < u128Bound ∧
  lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧ lv.queries / (1 + lvBase lvl) < u128Bound ∧
  digitsVal (osPowDigits lv.queries) 1 = lv.queries ∧
  QshOk c lvl lv 1 ∧ (oqShapeOf (osOqName c lvl lv)).nHs = c.yrLen + lv.folds ∧
  (oqShapeOf (osOqName c lvl lv)).hsBits = c.yrLog + 1 ∧
  (oqShapeOf (osOqName c lvl lv)).vs = (List.range c.yrLog).map (fun t ↦ vanishVal (lv.vanish + t)) ∧
  c.yrLog < 64 ∧ c.yrLen + lv.folds ≤ 2 ^ (c.yrLog + 1) ∧ lv.logCols = c.yrLog ∧
  -- the callees' names
  (c.yrLen + lv.folds, 1) ∈ omDeployed ∧
  omName (c.yrLen + lv.folds, 1) = "opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1" ∧
  LpOk lv ∧ LqOk c lvl lv ∧
  ("verify_merkle_cap__L" ++ natStr lv.capDepth, lv.capDepth) ∈ merkleCapNames

instance (c : OsCfg) (logN lvl : ℕ) (lv : OsLv) (level : Whir.Level) :
    Decidable (FinOkF c logN lvl lv level) := by
  unfold FinOkF; infer_instance

/-- Every level's facts, from level `lvl`. -/
def levelsB (c : OsCfg) (logN : ℕ) : ℕ → List OsLv → List Whir.Level → Bool
  | lvl, [lv], [level] => decide (FinOkF c logN lvl lv level)
  | lvl, lv :: lv' :: lvs, level :: next :: cfg =>
      decide (MidOk c logN lvl lv level next lv') && levelsB c logN (lvl + 1) (lv' :: lvs) (next :: cfg)
  | _, _, _ => false

/-- **A size's facts at a rate.** -/
def CandOk (m ri μ r : ℕ) (cfg : List Whir.Level) : Prop :=
  let c := osCfgR m ri
  c.nFolds + c.yrLog = μ ∧
    stackShape μ r = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default)) ∧
    (c.levels.headD default).foldsOff = 0 ∧
    (cfg.head?.map (·.fold)).getD 0 = (c.levels.headD default).folds ∧
    2 ≤ c.levels.length ∧ c.yrLevel = c.levels.length - 1 ∧ 1 ≤ c.yrLog ∧ 2 ^ c.yrLog = c.yrLen ∧
    lvsFolds c.levels = c.nFolds ∧ (c.levels.headD default).folds ≤ c.nFolds ∧
    c.nFolds + c.yrLog ≤ pointCap ∧
    ("fold_final_msg__L" ++ natStr c.yrLog, c.yrLog) ∈ foldFinalMsgNames ∧
    c.levels.length ≤ 64 ∧ levelsB c μ 0 c.levels cfg = true

instance (m ri μ r : ℕ) (cfg : List Whir.Level) : Decidable (CandOk m ri μ r cfg) := by
  unfold CandOk; infer_instance

/-- Size `m`'s facts at rate `ri`, checked: at `μ = m + minOpenLog`, `r = ri + 1`. -/
def candB (m ri : ℕ) : Bool :=
  match Whir.ladder (m + minOpenLog) (ri + 1) with
  | none => false
  | some cfg => decide (CandOk m ri (m + minOpenLog) (ri + 1) cfg)

theorem candB_sound {m ri : ℕ} (h : candB m ri = true) :
    ∃ cfg, Whir.ladder (m + minOpenLog) (ri + 1) = some cfg ∧
      CandOk m ri (m + minOpenLog) (ri + 1) cfg := by
  unfold candB at h
  split at h
  · exact absurd h (by simp)
  · rename_i cfg hdc
    exact ⟨cfg, hdc, of_decide_eq_true h⟩

end
end LeanVM.Guest.B1.Whir
