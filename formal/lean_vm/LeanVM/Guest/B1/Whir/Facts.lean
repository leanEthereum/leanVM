/-
  LeanVM.Guest.B1.Whir.Facts

  A candidate's static facts as one decidable proposition, for the kernel to decide, and what
  they give.
-/

module

public import LeanVM.Guest.B1.Whir.Levels
public import LeanVM.Guest.B1.Fs.Message
public import LeanVM.Guest.B1.Eq.Meaning
public import LeanVM.Guest.B1.Merkle.Meaning

/-!
# A candidate's facts, decided

`CandOk m μ r cfg`: the configuration `Whir.ladder μ r = cfg` against candidate `m`'s rows level
by level (`MidOk`, `FinOkF`: the arithmetic `MidFacts`, `FinFacts`, `LvFin` and the finish need,
the names of the level's callees in B1-a's tables, the `opening_queries` specialization's shape),
and the template's `opening_queries` calls those of its levels. `candB m μ r` decides it;
`Whir/Facts{m}.lean` decide it, one candidate a module.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-! ## A level's `opening_queries` shape -/

/-- The level's `opening_queries` entry and its shape, checked. -/
def QshOk (c : OsCfg) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Prop :=
  (oqEntry (osQueriesName c lvl lv)).map (·.1) = some (osQueriesName c lvl lv) ∧
    (oqShapeOf (osQueriesName c lvl lv)).odd = lv.queries % 2 * (if lvl = 0 then 1 else 0) ∧
    (oqShapeOf (osQueriesName c lvl lv)).base = (if lvl = 0 then 1 else 0) ∧
    (oqShapeOf (osQueriesName c lvl lv)).folds = lv.folds ∧
    (oqShapeOf (osQueriesName c lvl lv)).depth = lv.depth ∧
    (oqShapeOf (osQueriesName c lvl lv)).cd = lv.capDepth ∧
    (oqShapeOf (osQueriesName c lvl lv)).final = fin ∧
    2 ≤ (oqShapeOf (osQueriesName c lvl lv)).cd ∧ (oqShapeOf (osQueriesName c lvl lv)).cd ≤ 8 ∧
    (oqShapeOf (osQueriesName c lvl lv)).cd ≤ (oqShapeOf (osQueriesName c lvl lv)).depth ∧
    oqCount (oqShapeOf (osQueriesName c lvl lv)).odd (oqShapeOf (osQueriesName c lvl lv)).base
      (lv.queries / (1 + if lvl = 0 then 1 else 0)) = lv.queries

instance (c : OsCfg) (lvl : ℕ) (lv : OsLv) (fin : ℕ) : Decidable (QshOk c lvl lv fin) := by
  unfold QshOk; infer_instance

theorem qshOk_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {fin : ℕ} (h : QshOk c lvl lv fin) :
    QShapeOk c lvl lv fin (oqLoopOf (osQueriesName c lvl lv)) (oqShapeOf (osQueriesName c lvl lv)) := by
  obtain ⟨he, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  set name := osQueriesName c lvl lv
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
  (lvl + 1) * ligColsCap < u128Bound ∧ 4 * lv.capOff < u128Bound ∧
  lvl * hsStride < u128Bound ∧
  levelShape lv.logCols next (2 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv') ∧
  lv'.foldsOff = lv.foldsOff + lv.folds ∧ QshOk c lvl lv 0 ∧
  lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
  -- the callees' names
  (2 + lv.folds, 1) ∈ omDeployed ∧
  omName (2 + lv.folds, 1) = "opening_message__L" ++ natStr (2 + lv.folds) ++ "_L1" ∧
  lv.logCols ∈ spfDeployed ∧ spfName lv.logCols = "squeeze_point_from__L" ++ natStr lv.logCols ∧
  (decName lv, lv.depth, lv.capDepth) ∈ queryWindowsShapes ∧
  ("verify_merkle_cap__L" ++ natStr lv.capDepth, lv.capDepth) ∈ merkleCapNames ∧
  -- the finish's
  lv.prefixLen + c.yrLog = lv.logCols ∧ lv.resFoldOff = lv.foldsOff + lv.folds ∧
  lv.foldsOff + lv.folds ≤ c.nFolds ∧ c.nFolds - (lv.foldsOff + lv.folds) + c.yrLog = lv.logCols ∧
  lv.logCols < 64 ∧ 1 ≤ lv.folds ∧ lv.highBits ≤ 3 ∧ lv.highBits ≤ lv.logCols + 1 ∧
  lv.folds ≤ 2 ^ lv.highBits ∧ lv.queries / resBatch < ordG ∧ lv.queries / resBatch < u128Bound

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
  2 * (lv.foldsOff + lv.folds) < u128Bound ∧ 4 * lv.capOff < u128Bound ∧
  lvl * hsStride < u128Bound ∧ lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG ∧
  QshOk c lvl lv 1 ∧ (oqShapeOf (osQueriesName c lvl lv)).nHs = c.yrLen + lv.folds ∧
  (oqShapeOf (osQueriesName c lvl lv)).hsBits = c.yrLog + 1 ∧
  (oqShapeOf (osQueriesName c lvl lv)).vs = (List.range c.yrLog).map (fun t ↦ vanishVal (lv.vanish + t)) ∧
  c.yrLog < 64 ∧ c.yrLen + lv.folds ≤ 2 ^ (c.yrLog + 1) ∧ lv.logCols = c.yrLog ∧
  -- the callees' names
  (c.yrLen + lv.folds, 1) ∈ omDeployed ∧
  omName (c.yrLen + lv.folds, 1) = "opening_message__L" ++ natStr (c.yrLen + lv.folds) ++ "_L1" ∧
  (decName lv, lv.depth, lv.capDepth) ∈ queryWindowsShapes ∧
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

/-- **A candidate's facts.** -/
def CandOk (m μ r : ℕ) (cfg : List Whir.Level) : Prop :=
  let c := osCfg m
  c.nFolds + c.yrLog = μ ∧
    stackShape μ r = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default)) ∧
    (c.levels.headD default).foldsOff = 0 ∧
    (cfg.head?.map (·.fold)).getD 0 = (c.levels.headD default).folds ∧
    2 ≤ c.levels.length ∧ c.yrLevel = c.levels.length - 1 ∧ 1 ≤ c.yrLog ∧ 2 ^ c.yrLog = c.yrLen ∧
    lvsFolds c.levels = c.nFolds ∧ (c.levels.headD default).folds ≤ c.nFolds ∧
    c.nFolds + c.yrLog ≤ pointCap ∧
    ("fold_final_msg__L" ++ natStr c.yrLog, c.yrLog) ∈ foldFinalMsgNames ∧
    levelsB c μ 0 c.levels cfg = true

instance (m μ r : ℕ) (cfg : List Whir.Level) : Decidable (CandOk m μ r cfg) := by
  unfold CandOk; infer_instance

/-- The candidate's facts, checked. -/
def candB (m μ r : ℕ) : Bool :=
  match Whir.ladder μ r with
  | none => false
  | some cfg => decide (CandOk m μ r cfg)

theorem candB_sound {m μ r : ℕ} (h : candB m μ r = true) :
    ∃ cfg, Whir.ladder μ r = some cfg ∧ CandOk m μ r cfg := by
  unfold candB at h
  split at h
  · exact absurd h (by simp)
  · rename_i cfg hdc
    exact ⟨cfg, hdc, of_decide_eq_true h⟩

/-- The template's `opening_queries` calls are its levels', checked. -/
def qcallsB (m : ℕ) : Bool :=
  decide (osQCalls (osCfg m) = osQCallsL (osCfg m) 0 (osCfg m).levels (osHead (osCfg m)).2)

end
end LeanVM.Guest.B1.Whir
