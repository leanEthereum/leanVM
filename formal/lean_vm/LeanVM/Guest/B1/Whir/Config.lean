/-
  LeanVM.Guest.B1.Whir.Config

  A candidate's row of the `LIG_*` tables, read from the guest's source data: the per-level
  configuration `open_stacked` is specialized at, and the names of its loop helpers.
-/

module

public import LeanVM.Guest.Data.Source
public import LeanVM.Guest.B1.Whir.MatPlan

/-!
# The `LIG_*` tables and a candidate's configuration (TRIAGE G #42)

`open_stacked(m_idx, …)` (`lean_ethereum.py:1430-1760` at leanVM `40f877dc`) reads, at compile
time, the row `m_idx` of the per-candidate tables (`LIG_N_LEVELS`, `LIG_YR_LEVEL`, …) and the rows
`ml = m_idx · LIG_MAX_LEVELS + lvl` of the per-level ones (`LIG_FOLDS`, `LIG_QUERIES`, …). The
tables are the deployed placeholders, as the source data holds them (`Data.arr_LIG_*`,
`Guest/Data/Source.lean`); nothing here is trusted: the template of the body built from them
(`Whir/Template.lean`) is checked equal to the core IR, and their facts against the Spec are
decided (`Whir/Facts.lean`).

* `lig a i`: entry `i` of the table `a`, its low limb (the tables hold integers, the vanishing
  tables words of `K`);
* `OsLv`, `OsCfg`, `osCfg m`: a level's row and the candidate's, with the names of the
  specialized callees;
* `loopBase m`: the compiler numbers the `mul_range` helpers in order of appearance; candidate
  `m`'s squeeze loops are `__loop{loopBase m + lvl}` and its residual loops follow them.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Entry `i` of a constant array, its low limb. -/
def lig (a : List (Nat × Nat × Nat)) (i : Nat) : Nat := (a.getD i (0, 0, 0)).1

/-- `LIG_MAX_LEVELS`: the rows of a candidate in the per-level tables. -/
abbrev ligMaxLevels : Nat := 6

/-- `LIG_LOG_MSG_COLS_CAP`: the stride of a level's row in `ood_z` and `basis_d`. -/
abbrev ligColsCap : Nat := 22

/-- `LIG_MAX_VANISH_LEN`: the stride of a candidate's block in the vanishing tables. -/
abbrev ligVanishLen : Nat := 78

/-- `OOD_SLOTS`: the stride of a sample in `ood`. -/
abbrev oodSlots : Nat := 4

/-- `YR_LOG_CAP`: the length of `tail_challenges`. -/
abbrev yrLogCap : Nat := 5

/-- One level's row of the tables, `ml = m · 6 + lvl`. -/
structure OsLv where
  /-- `LIG_FOLDS`: the level's sumcheck rounds. -/
  folds : Nat
  /-- `LIG_FOLDS_OFF`: the folds before the level. -/
  foldsOff : Nat
  /-- `LIG_QUERIES`. -/
  queries : Nat
  /-- `LIG_TREE_DEPTH`: the height of the level's commitment. -/
  depth : Nat
  /-- `LIG_INTERLEAVE`: the words of a row (`K` words at level 0, `E` words deeper). -/
  interleave : Nat
  /-- `LIG_LEAF_CELLS`: the cells a leaf hashes. -/
  leafCells : Nat
  /-- `LIG_POSITIONS_OFF`: the level's first slot in `query_positions`. -/
  posOff : Nat
  /-- `LIG_CAP_DEPTH`. -/
  capDepth : Nat
  /-- `LIG_CAP_OFF`: the level's cap in `merkle_caps` (four cells a node) and its flags. -/
  capOff : Nat
  /-- `LIG_SQUEEZES`: the squeezes the query positions take. -/
  squeezes : Nat
  /-- `LIG_LOG_MSG_COLS`: the message log after the level's folds. -/
  logCols : Nat
  /-- `LIG_OOD_SAMPLES` of this level: the samples of its own commitment. -/
  oodHere : Nat
  /-- `LIG_OOD_SAMPLES` of the next level: the samples of the commitment read here. -/
  oodNext : Nat
  /-- `LIG_QUERY_GRIND_BITS`. -/
  grind : Nat
  /-- `LIG_RESIDUAL_PREFIX_LEN`: the fold challenges of the level's induced weight. -/
  prefixLen : Nat
  /-- `LIG_RESIDUAL_FOLD_OFF`: the first of them. -/
  resFoldOff : Nat
  /-- The level's first entry in the vanishing tables, `m · 78 + LIG_VANISH_OFF`. -/
  vanish : Nat
  deriving Repr, Inhabited, DecidableEq

/-- A candidate's row of the tables and its levels. -/
structure OsCfg where
  /-- The candidate. -/
  m : Nat
  /-- Its levels. -/
  levels : List OsLv
  /-- `LIG_YR_LEVEL`: the level that reads the final message. -/
  yrLevel : Nat
  /-- `LIG_YR_LOG_LEN`: the final message's log length, the tail's rounds. -/
  yrLog : Nat
  /-- `LIG_YR_LEN`. -/
  yrLen : Nat
  /-- `LIG_TOTAL_FOLDS`. -/
  nFolds : Nat
  /-- `LIG_MAX_SQUEEZES`. -/
  maxSq : Nat
  /-- `LIG_MAX_INTERLEAVE`. -/
  maxIl : Nat
  /-- `LIG_POSITIONS_LEN`. -/
  posLen : Nat
  /-- `LIG_CAP_LEN`. -/
  capLen : Nat
  /-- The first loop helper's number. -/
  loopBase : Nat
  /-- The compiler's choices of a shifted pointer's source (`osMatPlan`). -/
  plan : List (Nat × Nat × Nat)
  deriving Repr, Inhabited

/-- Level `lvl`'s row of candidate `m`. -/
def osLv (m lvl : Nat) : OsLv :=
  let i := m * ligMaxLevels + lvl
  { folds := lig Data.arr_LIG_FOLDS i, foldsOff := lig Data.arr_LIG_FOLDS_OFF i,
    queries := lig Data.arr_LIG_QUERIES i, depth := lig Data.arr_LIG_TREE_DEPTH i,
    interleave := lig Data.arr_LIG_INTERLEAVE i, leafCells := lig Data.arr_LIG_LEAF_CELLS i,
    posOff := lig Data.arr_LIG_POSITIONS_OFF i, capDepth := lig Data.arr_LIG_CAP_DEPTH i,
    capOff := lig Data.arr_LIG_CAP_OFF i, squeezes := lig Data.arr_LIG_SQUEEZES i,
    logCols := lig Data.arr_LIG_LOG_MSG_COLS i, oodHere := lig Data.arr_LIG_OOD_SAMPLES i,
    oodNext := lig Data.arr_LIG_OOD_SAMPLES (i + 1),
    grind := lig Data.arr_LIG_QUERY_GRIND_BITS i,
    prefixLen := lig Data.arr_LIG_RESIDUAL_PREFIX_LEN i,
    resFoldOff := lig Data.arr_LIG_RESIDUAL_FOLD_OFF i,
    vanish := m * ligVanishLen + lig Data.arr_LIG_VANISH_OFF i }

/-- The number of levels of candidate `m`. -/
def osNLevels (m : Nat) : Nat := lig Data.arr_LIG_N_LEVELS m

/-- The first loop helper of candidate `m`: the helpers are numbered in order, two per level
(the squeeze loops, then the residual loops), from `__loop41`. -/
def loopBase (m : Nat) : Nat := 41 + 2 * ((List.range m).map osNLevels).sum

/-- Candidate `m`'s configuration. -/
def osCfg (m : Nat) : OsCfg :=
  { m, levels := (List.range (osNLevels m)).map (osLv m),
    yrLevel := lig Data.arr_LIG_YR_LEVEL m, yrLog := lig Data.arr_LIG_YR_LOG_LEN m,
    yrLen := lig Data.arr_LIG_YR_LEN m, nFolds := lig Data.arr_LIG_TOTAL_FOLDS m,
    maxSq := lig Data.arr_LIG_MAX_SQUEEZES m,
    maxIl := lig Data.arr_LIG_MAX_INTERLEAVE m, posLen := lig Data.arr_LIG_POSITIONS_LEN m,
    capLen := lig Data.arr_LIG_CAP_LEN m, loopBase := loopBase m, plan := osMatPlan m }

/-- The vanishing value `LIG_VANISH_VALS[i]` (a word of `K`, its low limb). -/
def vanishVal (i : Nat) : Nat := lig Data.arr_LIG_VANISH_VALS i

/-- The vanishing inverse `LIG_VANISH_INVS[i]`. -/
def vanishInv (i : Nat) : Nat := lig Data.arr_LIG_VANISH_INVS i

/-! ## Names -/

/-- A decimal digit's character. -/
def digitLit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | _ => '9'

/-- The decimal digits of `n`, at most `fuel` of them. -/
def natStrAux : Nat → Nat → String
  | 0, _ => ""
  | f + 1, n => if n < 10 then String.singleton (digitLit n)
      else natStrAux f (n / 10) ++ String.singleton (digitLit (n % 10))

/-- `toString n`, by a definition the kernel evaluates (`toString` on `Nat` is not exposed to
importing modules); `natStr_eq` proves them equal. -/
def natStr (n : Nat) : String := natStrAux (n + 1) n

/-- The name of the loop helper `__loop{n}`. -/
def loopName (n : Nat) : String := "__loop" ++ natStr n

/-- Level `lvl`'s squeeze loop. -/
def OsCfg.sqLoop (c : OsCfg) (lvl : Nat) : String := loopName (c.loopBase + lvl)

/-- Level `lvl`'s residual loop. -/
def OsCfg.resLoop (c : OsCfg) (lvl : Nat) : String :=
  loopName (c.loopBase + c.levels.length + lvl)

end
end LeanVM.Guest.B1.Whir
