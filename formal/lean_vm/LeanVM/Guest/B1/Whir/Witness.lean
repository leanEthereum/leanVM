/-
  LeanVM.Guest.B1.Whir.Witness

  `open_stacked`'s witness: the stream words it reads, and its `opening_queries` calls, whose
  frames hold the openings.
-/

module

public import LeanVM.Guest.B1.Whir.InterfaceW
public import LeanVM.Guest.B1.Whir.Template

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
* `osWitness W rd m σ V`: the words at the cursor `σ 8`, and each level's openings `W` reads off
  its `opening_queries` call (`W` is the queries' witness, `B1/Opening`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The stream words level `lvl` reads. -/
def lvWords (c : OsCfg) (lvl : ℕ) (lv : OsLv) : ℕ :=
  7 * lv.folds + if lvl = c.yrLevel then c.yrLen + lv.folds + 1 else lv.folds + 6

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

/-- **`open_stacked`'s witness** at the candidate `m`, from its valuation `σ` and the frames `V`:
the stream words at the cursor, and level `l`'s openings `W rd V l` of its `opening_queries`
call's name and words. -/
def osWitness (W : Reader → FrameMap → ℕ → String → List E → List E → List Opening)
    (rd : Reader) (m : ℕ) (σ : Val) (V : FrameMap) : List E × List (List Opening) :=
  (osReadN rd (σ (.n 8)) (osWordsLen (osCfg m)),
    (osQCalls (osCfg m)).zipIdx.map fun ((name, args, rets), l) ↦
      W rd V l name (args.map σ) (rets.map σ))

end
end LeanVM.Guest.B1.Whir
