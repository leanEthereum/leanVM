/-
  LeanVM.Guest.B1.Whir.Config

  A size's rows of the `LIG_*` tables at a rate, read from the guest's source data: the per-level
  configuration `open_stacked` is specialized at, and the rows its dispatches' arms take.
-/

module

public import LeanVM.Guest.Data.Source
public import LeanVM.Guest.B1.Whir.MatPlan

/-!
# The `LIG_*` tables and a size's configuration (TRIAGE G #42)

`open_stacked(m_idx, rate_sel, …)` (`lean_ethereum.py`, `open_stacked`) is specialized on the
committed log-size alone, `m_idx = μ - 20`, and reads the rate `g^rate_sel` at runtime. At compile
time it reads the row `m_idx` of the per-size tables (`LIG_N_LEVELS`, `LIG_YR_LEVEL`, …), the rows
`ml = m_idx · LIG_MAX_LEVELS + lvl` of the per-level ones that no rate changes (`LIG_FOLDS`,
`LIG_LOG_MSG_COLS`, …), and, through a `match` on the rate, the rows
`(r · LIG_N_LOG_SIZES + m_idx) · LIG_MAX_LEVELS + lvl` of those a rate changes (`LIG_QUERIES`,
`LIG_TREE_DEPTH`, `LIG_CAP_DEPTH`, `LIG_SQUEEZES`). The tables are the deployed placeholders, as
the source data holds them (`Data.arr_LIG_*`, `Guest/Data/Source.lean`); nothing here is trusted:
the template of the body built from them (`Whir/Template.lean`) is checked equal to the core IR,
and their facts against the Spec are decided (`Whir/Facts.lean`).

* `lig a i`: entry `i` of the table `a`, its low limb (the tables hold integers, the vanishing
  tables words of `K`);
* `OsLv`, `osLvR m r lvl`: level `lvl`'s row of size `m` at rate `r`, the rate-free columns from
  the size's first row; `OsCfg`, `osCfg m`: the size's configuration, its levels at the first rate
  (the columns the body reads) and every rate's (the dispatches' arms, `OsCfg.lvAt`).
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Entry `i` of a constant array, its low limb. -/
def lig (a : List (Nat × Nat)) (i : Nat) : Nat := (a.getD i (0, 0)).1

/-- `LIG_MAX_LEVELS`: the rows of a size in the per-level tables. -/
abbrev ligMaxLevels : Nat := 6

/-- `LIG_N_LOG_SIZES`: the sizes a rate's rows cover. -/
abbrev ligNSizes : Nat := 11

/-- `LIG_N_RATES`. -/
abbrev ligNRates : Nat := 4

/-- `LIG_LEVEL_POSITIONS_CAP`: a level's slots in `query_positions` and `query_win_ptrs`. -/
abbrev ligPosCap : Nat := 224

/-- `LIG_LOG_MSG_COLS_CAP`: the stride of a sample's row in `ood_z` and of a level's in
`basis_d`. -/
abbrev ligColsCap : Nat := 24

/-- `YR_LOG_CAP`: the length of `tail_challenges`. -/
abbrev yrLogCap : Nat := 5

/-- `2 ^ HIGH_BITS_CAP`: the stride of a level's high part in `level_hs`. -/
abbrev hsStride : Nat := 8

/-- One level's row of the tables. -/
structure OsLv where
  /-- `LIG_FOLDS`: the level's fold rounds. -/
  folds : Nat
  /-- `LIG_FOLDS_OFF`: the fold rounds before the level. -/
  foldsOff : Nat
  /-- `LIG_QUERIES`, at the rate. -/
  queries : Nat
  /-- `LIG_TREE_DEPTH`, at the rate: the height of the level's commitment. -/
  depth : Nat
  /-- `LIG_LEAF_CELLS`: the cells a leaf hashes. -/
  leafCells : Nat
  /-- The level's first slot in `query_positions`, `lvl · LIG_LEVEL_POSITIONS_CAP`. -/
  posOff : Nat
  /-- `LIG_CAP_DEPTH`, at the rate. -/
  capDepth : Nat
  /-- `LIG_SQUEEZES`, at the rate: the squeezes the query positions take. -/
  squeezes : Nat
  /-- `LIG_LOG_MSG_COLS`: the message log after the level's folds. -/
  logCols : Nat
  /-- `LIG_HIGH_BITS`: the index bits of the level's high part. -/
  highBits : Nat
  /-- `LIG_RESIDUAL_PREFIX_LEN`: the fold challenges of the level's induced weight. -/
  prefixLen : Nat
  /-- `LIG_RESIDUAL_FOLD_OFF`: the first of them. -/
  resFoldOff : Nat
  /-- The level's first entry in the vanishing tables, `n(n+1)/2` for `n` message columns. -/
  vanish : Nat
  deriving Repr, Inhabited, DecidableEq

/-- The row of level `lvl` of size `m` at rate `r` in the tables a rate changes. -/
def ligRow (m r lvl : Nat) : Nat := (r * ligNSizes + m) * ligMaxLevels + lvl

/-- Level `lvl`'s row of size `m` at rate `r`. -/
def osLvR (m r lvl : Nat) : OsLv :=
  let i := m * ligMaxLevels + lvl
  let j := ligRow m r lvl
  let cols := lig Data.arr_LIG_LOG_MSG_COLS i
  { folds := lig Data.arr_LIG_FOLDS i, foldsOff := lig Data.arr_LIG_FOLDS_OFF i,
    queries := lig Data.arr_LIG_QUERIES j, depth := lig Data.arr_LIG_TREE_DEPTH j,
    leafCells := lig Data.arr_LIG_LEAF_CELLS i, posOff := lvl * ligPosCap,
    capDepth := lig Data.arr_LIG_CAP_DEPTH j, squeezes := lig Data.arr_LIG_SQUEEZES j,
    logCols := cols, highBits := lig Data.arr_LIG_HIGH_BITS i,
    prefixLen := lig Data.arr_LIG_RESIDUAL_PREFIX_LEN i,
    resFoldOff := lig Data.arr_LIG_RESIDUAL_FOLD_OFF i, vanish := cols * (cols + 1) / 2 }

/-- A size's configuration. -/
structure OsCfg where
  /-- The size, `μ - 20`, `minOpenLog` in `Interface`. -/
  m : Nat
  /-- Its levels, at the first rate: the columns no rate changes, which the body reads. -/
  levels : List OsLv
  /-- Its levels at every rate, by rate: the arms of the dispatches. -/
  levelsAt : List (List OsLv)
  /-- `LIG_YR_LEVEL`: the final level, the last. -/
  yrLevel : Nat
  /-- `LIG_YR_LOG_LEN`: the final lane's low part's log length, the closing rounds. -/
  yrLog : Nat
  /-- `LIG_YR_LEN`. -/
  yrLen : Nat
  /-- `LIG_TOTAL_FOLDS`. -/
  nFolds : Nat
  /-- The compiler's choices of a shifted pointer's source (`osMatPlan`). -/
  plan : List (Nat × Nat × Nat)
  deriving Repr, Inhabited

/-- The number of levels of size `m`. -/
def osNLevels (m : Nat) : Nat := lig Data.arr_LIG_N_LEVELS m

/-- Size `m`'s levels at rate `r`. -/
def osLevelsR (m r : Nat) : List OsLv := (List.range (osNLevels m)).map (osLvR m r)

/-- Size `m`'s configuration. -/
def osCfg (m : Nat) : OsCfg :=
  { m, levels := osLevelsR m 0, levelsAt := (List.range ligNRates).map (osLevelsR m),
    yrLevel := lig Data.arr_LIG_YR_LEVEL m, yrLog := lig Data.arr_LIG_YR_LOG_LEN m,
    yrLen := lig Data.arr_LIG_YR_LEN m, nFolds := lig Data.arr_LIG_TOTAL_FOLDS m,
    plan := osMatPlan m }

/-- The configuration with the levels `L`. -/
abbrev OsCfg.withLevels (c : OsCfg) (L : List OsLv) : OsCfg := { c with levels := L }

/-- Size `m`'s configuration with its levels at rate `ri`. -/
def osCfgR (m ri : Nat) : OsCfg := (osCfg m).withLevels (osLevelsR m ri)

/-- Level `lvl` at every rate, by rate: the rows the dispatches' arms specialize on. -/
def OsCfg.lvAt (c : OsCfg) (lvl : Nat) : List OsLv :=
  c.levelsAt.map fun ls ↦ ls.getD lvl default

/-- The vanishing value `VANISH_BY_COLS[i]` (a word of `K`, its low limb). -/
def vanishVal (i : Nat) : Nat := lig Data.arr_VANISH_BY_COLS i

/-- The vanishing inverse `VANISH_INVS_BY_COLS[i]`. -/
def vanishInv (i : Nat) : Nat := lig Data.arr_VANISH_INVS_BY_COLS i

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

end
end LeanVM.Guest.B1.Whir
