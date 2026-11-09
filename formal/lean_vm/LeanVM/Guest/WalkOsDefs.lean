/-
  LeanVM.Guest.WalkOsDefs

  `open_stacked`'s body up to a level's window pointers (`osPre`), and the check that its
  certificate's cuts ask, at each level's `opening_queries` call, the walk's obligation there.
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

/-- A level's queries block before its call's constant (`osQueries`): the weights' buffer, the row
weights, the cap's root, the window pointers' materialization. -/
def osQueriesA (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  let k := s.k
  let P := c.plan
  let m0 := s.mats
  let fp := osMatP P m0 osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P m0 osFch lv.foldsOff (k + 2)
  let cp := osMatP P m1 osCaps (4 * lv.capOff) fp.2.2
  let m2 := osMatsAfter P m1 osCaps (4 * lv.capOff) fp.2.2
  let flp := osMatP P m2 osFlags lv.capOff cp.2.2
  let m3 := osMatsAfter P m2 osFlags lv.capOff cp.2.2
  let r := flp.2.2
  let cp2 := osMatP P m3 osCaps (4 * lv.capOff) (r + 2)
  let flp2 := osMatP P m3 osFlags lv.capOff cp2.2.2
  let bp := osMatP P m3 osQbp lv.posOff flp2.2.2
  osHeap c.maxIl k ++ fp.1 ++
    [.call ("opening_row_weights__L" ++ natStr lv.folds ++ "_L" ++ natStr (if lvl = 0 then 1 else 0))
      [.n fp.2.1, .n (k + 1)] []] ++
    cp.1 ++ flp.1 ++
    [.call ("verify_merkle_cap__L" ++ natStr lv.capDepth) [.n cp.2.1, .n flp.2.1] [.n r, .n (r + 1)],
      .atom (.load (.n r) (.n osRoots) (2 * lvl)), .atom (.load (.n (r + 1)) (.n osRoots) (2 * lvl + 1))] ++
    cp2.1 ++ flp2.1 ++ bp.1

/-- The materializations before the window pointers' (`osQueries`' `m3`). -/
def osQueriesM3 (c : OsCfg) (lv : OsLv) (s : OsSt) : List OsMat :=
  let k := s.k
  let P := c.plan
  let fp := osMatP P s.mats osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P s.mats osFch lv.foldsOff (k + 2)
  let cp := osMatP P m1 osCaps (4 * lv.capOff) fp.2.2
  let m2 := osMatsAfter P m1 osCaps (4 * lv.capOff) fp.2.2
  osMatsAfter P m2 osFlags lv.capOff cp.2.2

/-- The window pointers' materialization (`osQueries`' `bp`). -/
def osQueriesBpS (c : OsCfg) (lv : OsLv) (s : OsSt) : List Stmt × ℕ × ℕ :=
  let k := s.k
  let P := c.plan
  let fp := osMatP P s.mats osFch lv.foldsOff (k + 2)
  let m1 := osMatsAfter P s.mats osFch lv.foldsOff (k + 2)
  let cp := osMatP P m1 osCaps (4 * lv.capOff) fp.2.2
  let m2 := osMatsAfter P m1 osCaps (4 * lv.capOff) fp.2.2
  let flp := osMatP P m2 osFlags lv.capOff cp.2.2
  let m3 := osMatsAfter P m2 osFlags lv.capOff cp.2.2
  let r := flp.2.2
  let cp2 := osMatP P m3 osCaps (4 * lv.capOff) (r + 2)
  let flp2 := osMatP P m3 osFlags lv.capOff cp2.2.2
  osMatP P m3 osQbp lv.posOff flp2.2.2

/-- A level's commitment (or final message). -/
def osLevelM (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt × OsSt × ℕ :=
  if lvl = c.yrLevel then osFinal c (osFolds osFch lv.foldsOff lv.folds s).2
  else osCommit c.plan lvl lv (osFolds osFch lv.foldsOff lv.folds s).2

/-- A level's state entering its queries block. -/
def osLevelQ (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsSt :=
  { (osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2 with
    k := (osLamPow lvl ((osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k - 1) lv.queries
      (osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k).2.2 }

/-- **A level up to its window pointers**: its folds, commitment (or final message), grinding,
squeezes, `lam^q`, and its queries block before the call's constant. -/
def osLevelPre (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : List Stmt :=
  (osFolds osFch lv.foldsOff lv.folds s).1 ++ (osLevelM c lvl lv s).1 ++
    [.call ("grind_check__L" ++ natStr lv.grind) [.n (osLevelM c lvl lv s).2.2] []] ++
    (osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).1 ++
    (osLamPow lvl ((osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k - 1) lv.queries
      (osSqueezes c lvl lv (osLevelM c lvl lv s).2.1).2.k).1 ++
    osQueriesA c lvl lv (osLevelQ c lvl lv s)

/-! ## The body up to a level's window pointers -/

/-- The state entering level `ℓ`. -/
def osStAt (c : OsCfg) (ℓ : ℕ) : OsSt := (osLevels c 0 (c.levels.take ℓ) (osHead c).2).2

/-- **`open_stacked`'s body up to level `ℓ`'s window pointers.** -/
def osPre (c : OsCfg) (ℓ : ℕ) : List Stmt :=
  (osHead c).1 ++ ((osLevels c 0 (c.levels.take ℓ) (osHead c).2).1 ++
    osLevelPre c ℓ (c.levels.getD ℓ default) (osStAt c ℓ))

/-- Level `ℓ`'s window pointers' value. -/
def osPreBp (c : OsCfg) (ℓ : ℕ) : ℕ :=
  (osQueriesBpS c (c.levels.getD ℓ default)
    (osLevelQ c ℓ (c.levels.getD ℓ default) (osStAt c ℓ))).2.1

/-- The bounds a level's materializations need. -/
def LvMatB (lvl : ℕ) (lv : OsLv) : Prop :=
  (lvl + 1) * ligColsCap < u128Bound ∧ lv.foldsOff < u128Bound ∧ 4 * lv.capOff < u128Bound ∧
    lv.capOff < u128Bound ∧ lv.posOff < u128Bound

instance (lvl : ℕ) (lv : OsLv) : Decidable (LvMatB lvl lv) := by unfold LvMatB; infer_instance

/-- A candidate's numbers the walk's obligation needs at every level (`OsWalkLv`): the squeeze
loop's power and bounds, the queries the squeezes decode, the materializations' bounds, the
decode's shape. -/
def osLvB (c : OsCfg) : Bool :=
  (List.range c.levels.length).all fun ℓ ↦
    let lv := c.levels.getD ℓ default
    decide (digitsVal (osPowDigits (192 / lv.depth)) 1 = 192 / lv.depth) &&
    decide (1 ≤ 192 / lv.depth) && decide (lv.queries ≤ lv.squeezes * (192 / lv.depth)) &&
    decide (0 < lv.squeezes) && decide (lv.squeezes < ordG) && decide (LvMatB ℓ lv) &&
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

/-- **`open_stacked`'s certificate** (function `j`, candidate configuration `c`): every cut an
`osCutOk`. -/
noncomputable def osOk (j : ℕ) (c : OsCfg) : Bool := (certOf j).cuts.all (osCutOk (certOf j) c)

end
end LeanVM.Guest.End
