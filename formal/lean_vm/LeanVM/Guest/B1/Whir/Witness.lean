/-
  LeanVM.Guest.B1.Whir.Witness

  `open_stacked`'s witness: the stream words it reads, and its levels' `opening_queries` calls,
  inside their `level_queries` calls, whose frames hold the openings.
-/

module

public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Opening.Witness

/-!
# `open_stacked`'s witness

The witness convention (`B1/Main/Frames.lean`): a function of the function's own valuation `σ`
and the frame map `V`, reading words only.

* `osWordsLen c`: the stream words candidate `c` reads at its cursor: each level's rounds (seven
  words a round: two nonces and five scalars, `opening_round`), a non-final level's message
  (the next root and the high part, `2 + folds`), its two out-of-domain values, its query nonce and
  its batching nonce, the final level's lane (`yrLen + folds`) and query nonce, and the closing
  rounds' two words each (no grind: `grindingBits 2 = 0`);
* `osQCallOf c lvl lv s`: the arguments and returns of level `lvl`'s `level_queries` dispatch
  from the state `s` before it (`osPreQ`); its `opening_queries` call is in the callee's frame
  (`osOqArgs`: the cap and flags its hints, then its own arguments but `λ`);
* `open_stacked_osW rd m r σ V`: at the rate `r`'s configuration `osCfgR m (r - 1)`, the words at
  the cursor `σ 9`, and each level's openings off its `opening_queries` call (`osLevelW`: S1b's
  `oqsOf` with the cap's siblings, `toOpening`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The stream words level `lvl` reads. -/
def lvWords (c : OsCfg) (lvl : ℕ) (lv : OsLv) : ℕ :=
  5 * lv.folds + if lvl = c.yrLevel then c.yrLen + lv.folds + 1 else lv.folds + 5

/-- The stream words candidate `c` reads. -/
def osWordsLen (c : OsCfg) : ℕ :=
  (c.levels.zipIdx.map fun (lv, l) ↦ lvWords c l lv).sum + 2 * c.yrLog

/-- The memory's word at `p·g^off` (`0` where it has none). -/
def osMemRead (rd : Reader) (p : E) (off : ℕ) : E := (rd (p.limb 0 * addressOfIndex off)).getD 0

/-- The `n` words at `p`. -/
def osReadN (rd : Reader) (p : E) (n : ℕ) : List E := (List.range n).map (osMemRead rd p)

/-! ## The levels' `level_queries` calls -/

/-- The state before a level's queries. -/
def osPreQ (c : OsCfg) (lvl : ℕ) (lv : OsLv) (s : OsSt) : OsSt :=
  let fin := lvl = c.yrLevel
  let f := osRounds c.plan lv.foldsOff lv.folds s
  let m := if fin then osFinalMsg c lv f.2 else osCommit c lvl lv f.2
  let sq := osPositions c lvl lv m.2
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
  let qp := osMatS c.plan osQpos lv.posOff hp.2.2
  let wp := osMatS c.plan osQbp lv.posOff qp.2.2
  ([li.2.1, li.2.2.1, cf.2.1, hp.2.1, qp.2.1, wp.2.1].map V.n, osRun wp.2.2.k 4)

/-- The base of level `lvl`'s rows: `1` at level `0`. -/
abbrev lvBase (lvl : ℕ) : ℕ := if lvl = 0 then 1 else 0

/-- The `opening_queries` specialization level `lvl`'s `level_queries` calls. -/
def osOqName (c : OsCfg) (lvl : ℕ) (lv : OsLv) : String :=
  let fin := lvl = c.yrLevel
  oqName lv.queries (lvBase lvl) lv.folds lv.leafCells lv.depth lv.capDepth
    (if fin then lv.logCols else 0) (if fin then c.yrLen + lv.folds else 0)
    (if fin then c.yrLog + 1 else 0) (if fin then 1 else 0)

/-- `level_queries`' body at level `lvl`. -/
def osLqBody (c : OsCfg) (lvl : ℕ) (lv : OsLv) : List Stmt :=
  let fin := lvl = c.yrLevel
  lqBody lv.queries (lvBase lvl) lv.folds lv.leafCells lv.depth lv.capDepth
    (if fin then lv.logCols else 0) (if fin then c.yrLen + lv.folds else 0)
    (if fin then c.yrLog + 1 else 0) (if fin then 1 else 0)

/-- The `opening_queries` call's arguments in `level_queries`' frame `Vq` on the arguments `A`:
the cap and its flags (cells `7`, `9`), `A` but `λ`, `g^N`. -/
def osOqArgs (Vq : Val) (A : List E) (N : ℕ) : List E :=
  [Vq (.n 7), Vq (.n 9), A.getD 1 0, A.getD 2 0, A.getD 3 0, A.getD 4 0, A.getD 5 0, gen ^ N]

/-! ## The openings -/

/-- A deployed `opening_queries` specialization's entry `(name, loop, shape)`. -/
def oqEntry (name : String) : Option (String × String × OqShape) :=
  openingQueriesLoops.find? (·.1 == name)

/-- The loop helper of the specialization `name`. -/
def oqLoopOf (name : String) : String := ((oqEntry name).map (·.2.1)).getD ""

/-- The shape of no specialization. -/
def oqShapeZero : OqShape := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, []⟩

/-- The shape of the specialization `name`. -/
def oqShapeOf (name : String) : OqShape := ((oqEntry name).map (·.2.2)).getD oqShapeZero

/-- The shape of entry `i` of `openingQueriesLoops`. -/
def oqShapeAt (i : ℕ) : OqShape := (openingQueriesLoops[i]?.map (·.2.2)).getD oqShapeZero

/-- The sibling of the cap's node `2^(D - j) + p / 2^j` (the ancestor `j` levels up of the cap's
leaf `p`). -/
def capSib (D p j : ℕ) : ℕ :=
  if p / 2 ^ j % 2 = 0 then 2 ^ (D - j) + p / 2 ^ j + 1 else 2 ^ (D - j) + p / 2 ^ j - 1

/-- **The cap's siblings** of its leaf `p` (of `2^D`), from the cap's cells at `cap` (node `v`'s
cells `2v`, `2v + 1`). -/
def capSibsOf (rd : Reader) (cap : E) (D p : ℕ) : List Digest :=
  (List.range D).map fun j ↦
    digestOfCells (memRead rd cap (2 * capSib D p j)) (memRead rd cap (2 * capSib D p j + 1))

/-- A query's opening: its position, its row, its siblings below the cap, then the cap's. -/
def toOpening (rd : Reader) (cap : E) (cd depth : ℕ) (w : QW) : Opening :=
  ⟨w.1, w.2.1, w.2.2 ++ capSibsOf rd cap cd (w.1 / 2 ^ (depth - cd))⟩

/-- **Level `lvl`'s openings** from its `level_queries` call on the words `args`, `rets`: the
queries read off its `opening_queries` call's frame and its loop's frames (`oqsOf`), each with
the cap's siblings from the memory. -/
def osLevelW (rd : Reader) (V : FrameMap) (c : OsCfg) (lvl : ℕ) (lv : OsLv) (args rets : List E) :
    List Opening :=
  let Vq := V (osQueriesName c lvl lv) args rets
  let n := osOqName c lvl lv
  let N := lv.queries / (1 + lvBase lvl)
  (oqsOf (oqShapeOf n).oq (oqShapeOf n).odd (oqLoopOf n) N rd
      (V n (osOqArgs Vq args N) [Vq (.n 13)]) V).map
    (toOpening rd (Vq (.n 7)) lv.capDepth lv.depth)

/-- **The witness's openings** of the levels from `lvl`: each level's at its `level_queries`
call. -/
def osLevelsW (rd : Reader) (V : FrameMap) (σ : Val) (c : OsCfg) :
    ℕ → List OsLv → OsSt → List (List Opening)
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    osLevelW rd V c lvl lv ((osQCallOf c lvl lv (osPreQ c lvl lv s)).1.map σ)
        ((osQCallOf c lvl lv (osPreQ c lvl lv s)).2.map σ) ::
      osLevelsW rd V σ c (lvl + 1) rest (osLevel c lvl lv s).2

/-- **`open_stacked`'s witness** at the size `m` and the rate `r`, from its valuation `σ` and
the frames `V`: the stream words at the cursor `σ 9`, and each level's openings (`osLevelW`). -/
def open_stacked_osW (rd : Reader) (m r : ℕ) (σ : Val) (V : FrameMap) :
    List E × List (List Opening) :=
  let c := osCfgR m (r - 1)
  (osReadN rd (σ (.n 9)) (osWordsLen c), osLevelsW rd V σ c 0 c.levels (osHead c).2)

end
end LeanVM.Guest.B1.Whir
