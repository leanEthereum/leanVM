/-
  LeanVM.Guest.B1.Whir.Facts

  A candidate's facts as one boolean check, for the kernel to decide.
-/

module

public import LeanVM.Guest.B1.Whir.Open
public import LeanVM.Guest.B1.Whir.RootsN
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.B1.Opening.OodPointHi
public import LeanVM.Guest.B1.Bits.Meaning
public import LeanVM.Guest.B1.Merkle.Meaning

/-!
# A size's facts at a rate, decided

`candB m ri` checks, by computation, everything `open_generic` asks of size `m` at the rate
`ri + 1`, at the configuration `osCfgR m ri` (`CandFacts`: the configuration
`Whir.ladder (m + minOpenLog) (ri + 1)` against the `LIG_*` rows level by level, the vanishing tables) and
the names of its callees in B1-a's and the helpers' tables (`NamesOk`); `candB_sound` turns it into
the propositions. `Whir/Facts{m}.lean` decide it, one size (its four rates) a module.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `LvB`, checked. -/
def lvBB (_c : OsCfg) (lvl : ℕ) (lv : OsLv) (level : Whir.Level) (ml : ℕ) : Bool :=
  decide (lv.depth = ml + level.logInvRate) && decide (level.queries = lv.queries) &&
  decide (2 ≤ lv.queries) && decide (digitsVal (osPowDigits lv.queries) 1 = lv.queries) &&
  decide (1 ≤ 192 / lv.depth) &&
  decide (lv.squeezes = ceilDiv lv.queries (192 / lv.depth)) &&
  decide (digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth) &&
  decide (lv.posOff < u128Bound) && decide (0 < lv.squeezes) && decide (lv.squeezes < ordG) &&
  decide (lv.squeezes * 5 < u128Bound) &&
  decide (lv.folds = if lvl = 0 then 6 else 4) && decide (lv.interleave = if lvl = 0 then 64 else 16) &&
  decide (2 ≤ lv.capDepth) && decide (lv.capDepth ≤ 8) && decide (lv.capDepth ≤ lv.depth) &&
  decide (lv.foldsOff < u128Bound) &&
  decide (lv.queries / (1 + if lvl = 0 then 1 else 0) < ordG) &&
  decide (lv.queries / (1 + if lvl = 0 then 1 else 0) < u128Bound)

theorem lvBB_sound {c : OsCfg} {lvl : ℕ} {lv : OsLv} {level : Whir.Level} {ml : ℕ}
    (h : lvBB c lvl lv level ml = true) : LvB c lvl lv level ml := by
  simp only [lvBB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, hqd⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, hc8⟩, h14⟩, h15⟩, h18⟩, h19⟩ := h
  exact ⟨h1, h2, h3, hqd, h4, h5, h6, h7, h8, h9, h10, ⟨h11, h12⟩, h13, hc8, h14,
    ⟨h15, h7, h18, h19⟩⟩

/-- `LevelsOk`, checked. -/
def levelsOkB (c : OsCfg) (logN : ℕ) : ℕ → List OsLv → List Whir.Level → Bool
  | lvl, [lv], [level] => lvBB c lvl lv level lv.logCols && decide (level.fold = lv.folds) &&
      decide (1 ≤ lv.folds) && decide (logN - (lv.foldsOff + lv.folds) = lv.logCols) &&
      decide (2 ^ lv.logCols = c.yrLen) && decide (lvl = c.yrLevel)
  | lvl, lv :: lv' :: lvs, level :: next :: cfg => lvBB c lvl lv level lv.logCols &&
      decide (level.fold = lv.folds) && decide (1 ≤ lv.folds) &&
      decide (logN - (lv.foldsOff + lv.folds) = lv.logCols) && decide (1 ≤ lv.logCols) &&
      decide ((lvl + 1) * ligColsCap < u128Bound) && decide (lvl ≠ c.yrLevel) &&
      decide (lv'.foldsOff = lv.foldsOff + lv.folds) &&
      decide (levelShape lv.logCols next (3 * 2 ^ next.fold) = (lv'.depth, lvWidth (lvl + 1) lv')) &&
      levelsOkB c logN (lvl + 1) (lv' :: lvs) (next :: cfg)
  | _, _, _ => false

theorem levelsOkB_sound {c : OsCfg} {logN : ℕ} : ∀ {lvl : ℕ} {lvs : List OsLv}
    {cfg : List Whir.Level}, levelsOkB c logN lvl lvs cfg = true → LevelsOk c logN lvl lvs cfg
  | lvl, [lv], [level], h => by
    simp only [levelsOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    exact ⟨lvBB_sound h1, h2, h3, h4, h5, h6⟩
  | lvl, lv :: lv' :: lvs, level :: next :: cfg, h => by
    simp only [levelsOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    exact ⟨lvBB_sound h1, h2, h3, h4, h5, h6, h7, h8, h9, levelsOkB_sound h10⟩
  | _, [], _, h => by simp [levelsOkB] at h
  | _, [_], [], h => by simp [levelsOkB] at h
  | _, [_], _ :: _ :: _, h => by simp [levelsOkB] at h
  | _, _ :: _ :: _, [], h => by simp [levelsOkB] at h
  | _, _ :: _ :: _, [_], h => by simp [levelsOkB] at h

/-- `LvStatic`, checked. -/
def lvStaticB (c : OsCfg) (i : ℕ) (lv : OsLv) : Bool :=
  decide (1 ≤ lv.logCols) && decide (lv.posOff < u128Bound) &&
  decide (2 ≤ lv.queries) && decide (lv.queries / resBatch < ordG) &&
  decide (lv.queries / resBatch < u128Bound) &&
  decide (lv.prefixLen + c.yrLog = lv.logCols) && decide (lv.resFoldOff = lv.foldsOff + lv.folds) &&
  decide (lv.foldsOff + lv.folds ≤ c.nFolds) &&
  decide (c.nFolds - (lv.foldsOff + lv.folds) + c.yrLog = lv.logCols) &&
  vanishOkC lv.vanish lv.logCols && decide (i * ligColsCap < u128Bound) &&
  decide (lv.vanish = vanishOff lv.logCols)

theorem lvStaticB_sound {c : OsCfg} {i : ℕ} {lv : OsLv} (h : lvStaticB c i lv = true) :
    LvStatic c i lv := by
  simp only [lvStaticB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, hlc⟩, hvan⟩ := h
  exact ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, vanishOk_of_C h11, hlc, hvan⟩

/-- A level's callees are in B1-a's tables, at the rate's row `lv`. -/
def NamesOkA (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop :=
  (lvl ≠ c.yrLevel → ("opening_ood_point__L" ++ natStr lv.logCols, lv.logCols) ∈ oodPointNamesAll) ∧
  ("opening_final_message__L" ++ natStr c.yrLen, c.yrLen) ∈ finalMessageNames ∧
  "grind_check__L" ++ natStr lv.grind = "grind_check__L17" ∧
  ("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth, lv.depth, lv.capDepth) ∈
    queryWindowsShapes ∧
  ("verify_merkle_cap__L" ++ natStr lv.capDepth, lv.capDepth) ∈ merkleCapNames ∧
  (oqNameOf lvl lv, lv.queries % 2 * (if lvl = 0 then 1 else 0), (if lvl = 0 then 1 else 0),
    lv.interleave, lv.leafCells, lv.depth, lv.capDepth) ∈ openingQueriesShapes ∧
  ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0) =
    if lvl = 0 then "opening_row_weights__L6_L1" else "opening_row_weights__L4_L0") ∧
  (lv.folds = if lvl = 0 then 6 else 4)

instance (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Decidable (NamesOkA c lvl lv) := by
  unfold NamesOkA; infer_instance

/-- A level's helpers are in their tables, at the rate's row `lv`. -/
def NamesOkH (lvl : ℕ) (lv : OsLv) : Prop :=
  (osPositionsName lv, lv.squeezes, lpLoopOf (osPositionsName lv), lv.depth, lv.capDepth) ∈ lpTable ∧
  (osQueriesName lvl lv, lv.queries, (if lvl = 0 then 1 else 0), lv.interleave, lv.leafCells,
    lv.depth, lv.capDepth) ∈ lqTable ∧
  (osResidualName lv, lv.queries, lv.logCols, (lrLoopsOf (osResidualName lv)).1,
    (lrLoopsOf (osResidualName lv)).2) ∈ lrTable ∧
  (rbName lv.logCols, lv.logCols) ∈ rbTable ∧
  digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth ∧ 0 < lv.squeezes ∧
  lv.squeezes < ordG ∧ lv.squeezes * 5 < u128Bound ∧
  resBatch * (lv.queries / resBatch) < u128Bound

instance (lvl : ℕ) (lv : OsLv) : Decidable (NamesOkH lvl lv) := by
  unfold NamesOkH; infer_instance

/-- A level's callees and helpers are in their tables. -/
def NamesOk (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop := NamesOkA c lvl lv ∧ NamesOkH lvl lv

instance (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Decidable (NamesOk c lvl lv) := by
  unfold NamesOk; infer_instance

/-- Size `m`'s facts at the rate `ri + 1`, checked. -/
def candB (m ri : ℕ) : Bool :=
  match Whir.ladder (m + minOpenLog) (ri + 1) with
  | none => false
  | some cfg =>
    let μ := m + minOpenLog
    let r := ri + 1
    let c := osCfgR m ri
    levelsOkB c μ 0 c.levels cfg &&
    decide (stackShape μ r = ((c.levels.headD default).depth, lvWidth 0 (c.levels.headD default))) &&
    decide ((c.levels.headD default).foldsOff = 0) && decide (2 ≤ c.levels.length) &&
    decide (c.yrLevel = c.levels.length - 1) && decide (1 ≤ c.yrLog) &&
    decide ((c.levels.getLastD default).logCols = c.yrLog) &&
    decide ((c.levels.getLastD default).foldsOff + (c.levels.getLastD default).folds = c.nFolds) &&
    decide (2 ^ c.yrLog = c.yrLen) && decide (c.nFolds + c.yrLog = μ) && decide (μ ≤ pointCap) &&
    decide ((c.levels.headD default).folds ≤ c.nFolds) &&
    (List.range c.levels.length).all (fun i ↦ decide (i + 1 < c.levels.length →
      (c.levels.getD (i + 1) default).foldsOff =
        (c.levels.getD i default).foldsOff + (c.levels.getD i default).folds)) &&
    (List.range c.levels.length).all (fun i ↦ lvStaticB c i (c.levels.getD i default)) &&
    (List.range c.levels.length).all (fun i ↦ decide (NamesOk c i (c.levels.getD i default))) &&
    decide (("fold_final_msg__L" ++ natStr c.yrLog, c.yrLog) ∈ foldFinalMsgNames)

/-- **The check's meaning.** -/
theorem candB_sound {m ri : ℕ} (h : candB m ri = true) :
    ∃ cfg, CandFacts (osCfgR m ri) (m + minOpenLog) (ri + 1) cfg ∧
      (∀ i < (osCfgR m ri).levels.length,
        NamesOk (osCfgR m ri) i ((osCfgR m ri).levels.getD i default)) ∧
      ("fold_final_msg__L" ++ natStr (osCfgR m ri).yrLog, (osCfgR m ri).yrLog) ∈
        foldFinalMsgNames := by
  unfold candB at h
  split at h
  · exact absurd h (by simp)
  · rename_i cfg hdc
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
      h14⟩, h15⟩, h16⟩ := h
    exact ⟨cfg, ⟨hdc, levelsOkB_sound h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      fun i hi ↦ h13 i (by omega) hi,
      fun i hi ↦ lvStaticB_sound (h14 i hi)⟩, fun i hi ↦ by simpa using h15 i hi, h16⟩

end
end LeanVM.Guest.B1.Whir
