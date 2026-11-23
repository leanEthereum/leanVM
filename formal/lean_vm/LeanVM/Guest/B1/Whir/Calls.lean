/-
  LeanVM.Guest.B1.Whir.Calls

  `open_stacked`'s template's `level_queries` dispatches and the stream words it reads, from the
  templates alone: what `scripts/whir-tables.lean` reads before the proofs are built.
-/

module

public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Opening.QueriesLoops

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-- The stream words level `lvl` reads. -/
def lvWords (c : OsCfg) (lvl : ℕ) (lv : OsLv) : ℕ :=
  5 * lv.folds + if lvl = c.yrLevel then c.yrLen + lv.folds + 1 else lv.folds + 5

/-- The stream words candidate `c` reads. -/
def osWordsLen (c : OsCfg) : ℕ :=
  (c.levels.zipIdx.map fun (lv, l) ↦ lvWords c l lv).sum + 2 * c.yrLog

/-- The state before a level's queries. -/
def osPreQ (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsSt :=
  let fin := lvl = c.yrLevel
  let rt := osRates c lvl s
  let f := osRounds true lv.foldsOff lv.folds rt.2
  let m := if fin then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  let gr := osQGrind m.2
  let sq := osPositions c lvl gr.2
  let la := if fin then (([] : List Stmt), sq.2) else osLam sq.2
  let h := if fin then osHsFinal c lv la.2 else osHsMid lvl lv la.2
  h.2

/-- The arguments and returns of `osQueries c lvl lv s`'s dispatch into `level_queries`. -/
def osQCallOf (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List V × List V :=
  let fin := lvl = c.yrLevel
  let li : List Stmt × ℕ × ℕ × OsSt :=
    if fin then ([osCst s.k (word 0 0), osCst (s.k + 1) (word 0 0)], s.k, s.k + 1, { s with k := s.k + 2 })
    else ([], s.lam, s.lamInv, s)
  let cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2.2
  let hp : List Stmt × ℕ × OsSt :=
    if fin then ([], s.hs, cf.2.2) else osMatS c.plan osHs (lvl * hsStride) cf.2.2
  ([li.2.1, li.2.2.1, cf.2.1, hp.2.1, s.lp, s.lw].map V.n, osRun hp.2.2.k 4)

/-- The base of level `lvl`'s rows: `1` at level `0`. -/
abbrev lvBase (lvl : ℕ) : ℕ := if lvl = 0 then 1 else 0

/-- The `opening_queries` specialization level `lvl`'s `level_queries` calls. -/
def osOqName (c : OsCfg) (lvl : ℕ) (lv : OsLv) : String :=
  let fin := lvl = c.yrLevel
  oqName (lvBase lvl) lv.folds lv.leafCells (lv.depth - lv.capDepth)
    (if fin then lv.logCols else 0) (if fin then c.yrLen + lv.folds else 0)
    (if fin then c.yrLog + 1 else 0) (if fin then 1 else 0)

/-- `level_queries`' body at level `lvl`. -/
def osLqBody (c : OsCfg) (lvl : ℕ) (lv : OsLv) : List Stmt :=
  let fin := lvl = c.yrLevel
  lqBody lv.queries (lvBase lvl) lv.folds lv.leafCells lv.depth lv.capDepth
    (if fin then lv.logCols else 0) (if fin then c.yrLen + lv.folds else 0)
    (if fin then c.yrLog + 1 else 0) (if fin then 1 else 0)

/-- A deployed `opening_queries` specialization's entry `(name, loop, shape)`. -/
def oqEntry (name : String) : Option (String × String × OqShape) :=
  openingQueriesLoops.find? (·.1 == name)

/-- The loop helper of the specialization `name`. -/
def oqLoopOf (name : String) : String := ((oqEntry name).map (·.2.1)).getD ""

/-- The shape of no specialization. -/
def oqShapeZero : OqShape := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩

/-- The shape of the specialization `name`. -/
def oqShapeOf (name : String) : OqShape := ((oqEntry name).map (·.2.2)).getD oqShapeZero

/-- The shape of entry `i` of `openingQueriesLoops`. -/
def oqShapeAt (i : ℕ) : OqShape := (openingQueriesLoops[i]?.map (·.2.2)).getD oqShapeZero

end
end LeanVM.Guest.B1.Whir
