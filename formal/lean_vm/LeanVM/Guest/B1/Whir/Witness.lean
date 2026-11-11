/-
  LeanVM.Guest.B1.Whir.Witness

  `open_stacked`'s witness: the stream words it reads, and its `opening_queries` calls, whose
  frames hold the openings.
-/

module

public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Whir.Template
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
* `osQCalls c`: the template's `opening_queries` calls, one a level, in order;
* `open_stacked_osW rd m σ V`: the words at the cursor `σ 8`, and each level's openings off its
  `opening_queries` call (`osLevelW`: S1b's `oqsOf` with the cap's siblings, `toOpening`).
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

/-- The names of candidate `c`'s `opening_queries` specializations. -/
def osQNames (c : OsCfg) : List String := c.levels.zipIdx.map fun (lv, l) ↦ osQueriesName c l lv

/-- An `opening_queries` call of the body: its name, arguments and returns. -/
def oqCallOf (names : List String) : Stmt → Option (String × List V × List V)
  | .call f args rets => if names.contains f then some (f, args, rets) else none
  | _ => none

/-- **The template's `opening_queries` calls**, one a level, in order. -/
def osQCalls (c : OsCfg) : List (String × List V × List V) :=
  (osBody c).filterMap (oqCallOf (osQNames c))

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

/-- **Level `lvl`'s openings** from its `opening_queries` call `name` on the words `args`,
`rets`: the queries read off the callee's frame and its loop's frames (`oqsOf`), each with the
cap's siblings from the memory. -/
def osLevelW (rd : Reader) (V : FrameMap) (lvl : ℕ) (lv : OsLv) (name : String)
    (args rets : List E) : List Opening :=
  (oqsOf (oqShapeOf name).oq (oqShapeOf name).odd (oqLoopOf name)
      (lv.queries / (1 + if lvl = 0 then 1 else 0)) rd (V name args rets) V).map
    (toOpening rd (args.headD 0) lv.capDepth lv.depth)

/-- **`open_stacked`'s witness** at the candidate `m`, from its valuation `σ` and the frames `V`:
the stream words at the cursor `σ 8`, and each level's openings (`osLevelW`) off its
`opening_queries` call. -/
def open_stacked_osW (rd : Reader) (m : ℕ) (σ : Val) (V : FrameMap) :
    List E × List (List Opening) :=
  (osReadN rd (σ (.n 8)) (osWordsLen (osCfg m)),
    (osQCalls (osCfg m)).zipIdx.map fun ((name, args, rets), l) ↦
      osLevelW rd V l ((osCfg m).levels.getD l default) name (args.map σ) (rets.map σ))

end
end LeanVM.Guest.B1.Whir
