/-
  LeanVM.Guest.WalkOsDefs

  `open_stacked`'s body up to a level's window pointers (`osPre`), and the check that its
  certificate assumes its window table and asks, at each level's `opening_queries` call, the walk's
  obligation there.
-/

module

public import LeanVM.Guest.Glob
public import LeanVM.Guest.B1.Whir.Loops
public import LeanVM.Guest.B1.Bits.QueryWindowsT

/-!
# `open_stacked`'s cuts, checked

A light module: the template's prefixes (`osPre`, `osPreBp`) and Bool checks on the certificates
(`osOk`) and the candidates' numbers (`osLvB`), so their kernel checks import no proof.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1

@[expose] public section

/-! ## A level up to its window pointers -/

/-- A level's queries block before its call's constant (`osQueries`): the cap, its flags, `1/λ`,
the round coefficients, the high part, the positions, the window pointers. -/
def osQueriesA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × ℕ :=
  let fin := lvl = c.yrLevel
  let cp := osMatS c.plan osCaps (4 * lv.capOff) s
  let fl := osMatS c.plan osFlags lv.capOff cp.2.2
  let li : List Stmt × ℕ × OsSt :=
    if fin then ([osCst fl.2.2.k (word 0 0)], fl.2.2.k, { fl.2.2 with k := fl.2.2.k + 1 })
    else ([], s.lamInv, fl.2.2)
  let cf := osMatS c.plan osCoefs (2 * lv.foldsOff) li.2.2
  let hp : List Stmt × ℕ × OsSt :=
    if fin then ([], s.hs, cf.2.2) else osMatS c.plan osHs (lvl * hsStride) cf.2.2
  let qp := osMatS c.plan osQpos lv.posOff hp.2.2
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  (cp.1 ++ fl.1 ++ li.1 ++ cf.1 ++ hp.1 ++ qp.1 ++ wp.1, wp.2.1)

/-- A level's state entering its queries block (`Level.osPreQ`). -/
def osQState (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsSt :=
  let fin := lvl = c.yrLevel
  let f := osRounds c.plan lv.foldsOff lv.folds s
  let m := if fin then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  let sq := osSqueezes c lvl lv m.2
  let la := if fin then (([] : List Stmt), sq.2) else osLam sq.2
  let cp := osCap c lvl lv la.2
  let h := if fin then osHsFinal c lv cp.2 else osHsMid lvl lv cp.2
  h.2

/-- **A level up to its window pointers** (`osLevel`'s blocks before the queries' constant). -/
def osLevelPre (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let fin := lvl = c.yrLevel
  let f := osRounds c.plan lv.foldsOff lv.folds s
  let m := if fin then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  let gr : List Stmt := [.call ("grind_check__L" ++ natStr queryGrind) [.n m.2.pow0, .n osTabs] []]
  let sq := osSqueezes c lvl lv m.2
  let la := if fin then (([] : List Stmt), sq.2) else osLam sq.2
  let cp := osCap c lvl lv la.2
  let h := if fin then osHsFinal c lv cp.2 else osHsMid lvl lv cp.2
  f.1 ++ m.1 ++ gr ++ sq.1 ++ la.1 ++ cp.1 ++ h.1 ++ (osQueriesA c lvl lv h.2).1

/-! ## The body up to a level's window pointers -/

/-- The state entering level `ℓ`. -/
def osStAt (c : OsCfg) (ℓ : ℕ) : OsSt := (osLevels c 0 (c.levels.take ℓ) (osHead c).2).2

/-- **`open_stacked`'s body up to level `ℓ`'s window pointers.** -/
def osPre (c : OsCfg) (ℓ : ℕ) : List Stmt :=
  (osHead c).1 ++ ((osLevels c 0 (c.levels.take ℓ) (osHead c).2).1 ++
    osLevelPre c ℓ (c.levels.getD ℓ default) (osStAt c ℓ))

/-- Level `ℓ`'s window pointers' value. -/
def osPreBp (c : OsCfg) (ℓ : ℕ) : ℕ :=
  (osQueriesA c ℓ (c.levels.getD ℓ default)
    (osQState c ℓ (c.levels.getD ℓ default) (osStAt c ℓ))).2

/-- The bounds a level's materializations need. -/
def LvMatB (lvl : ℕ) (lv : OsLv) : Prop :=
  2 * (lv.foldsOff + lv.folds) < u128Bound ∧
    (lvl + 1) * ligColsCap < u128Bound ∧ 4 * lv.capOff < u128Bound ∧
    lvl * hsStride < u128Bound ∧ lv.posOff < u128Bound

instance (lvl : ℕ) (lv : OsLv) : Decidable (LvMatB lvl lv) := by unfold LvMatB; infer_instance

/-- A candidate's numbers the walk's obligation needs at every level (`OsWalkLv`): the squeeze
loop's power and bounds, the queries the squeezes decode, the materializations' bounds, the
decode's shape. -/
def osLvB (c : OsCfg) : Bool :=
  (List.range c.levels.length).all fun ℓ ↦
    let lv := c.levels.getD ℓ default
    decide (digitsVal (osPowDigits (128 / lv.depth)) 1 = 128 / lv.depth) &&
    decide (1 ≤ 128 / lv.depth) && decide (lv.queries ≤ lv.squeezes * (128 / lv.depth)) &&
    decide (1 ≤ lv.squeezes) && decide (lv.squeezes < ordG) &&
    decide (lv.squeezes * 5 < u128Bound) && decide (LvMatB ℓ lv) &&
    decide (("decode_query_windows__L" ++ natStr lv.depth ++ "_L" ++ natStr lv.capDepth, lv.depth,
      lv.capDepth) ∈ queryWindowsShapes)

end
end LeanVM.Guest.B1.Whir

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Guest.B1
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- A tuple of `open_stacked`'s cut at statement `start`: level `ℓ`'s walk (`OqMainWins`, tag
`walkTag (2 + base)`) on its window pointers' cell and `n_iters_g`'s, conditional on `n_iters_g`'s
cell holding the one-limb word `g^(queries / (1 + base))` (`impTag … 1 l`), the cut past the
window pointers (`osPre`). -/
def osSemOk (C : Cert) (c : OsCfg) (start : ℕ) (t : ℕ × List ℕ) : Bool :=
  (List.range c.levels.length).any fun ℓ ↦
    let lv := c.levels.getD ℓ default
    let base := if ℓ = 0 then 1 else 0
    let tW := walkTag (2 + base) (lv.queries % 2 * base) lv.depth lv.capDepth
    let N := lv.queries / (1 + base)
    t.1 == impTag tW 1 (impImm t.1) && decide (tW < tagGkr) && decide (lv.capDepth < 64) &&
      decide (N < u128Bound) && decide (K.ofBits (impImm t.1) = gpowK N) &&
      t.2.length == 2 && t.2.getD 0 0 == C.locs.getD (osPreBp c ℓ) 0 &&
      Nat.ble (osPre c ℓ).length start

/-- An `open_stacked` cut: no bound, its tuples the levels' walks (`osSemOk`). -/
def osCutOk (C : Cert) (c : OsCfg) (cut : Cut) : Bool :=
  cut.known.isEmpty && cut.knownIf.isEmpty && cut.sems.all (osSemOk C c cut.start)

/-- **`open_stacked`'s certificate** (function `j`, candidate configuration `c`): the window table
`tabs` (value `9`) assumed (`tagTabs`), every cut an `osCutOk`. -/
noncomputable def osOk (j : ℕ) (c : OsCfg) : Bool :=
  (certOf j).sem == [(tagTabs, [(certOf j).locs.getD osTabs 0])] &&
    (certOf j).cuts.all (osCutOk (certOf j) c)

end
end LeanVM.Guest.End
