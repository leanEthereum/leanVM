/-
  LeanVM.Guest.CoreMode.Fam.TermDefs

  The dimension facts' family: a claim's low point inside its chain, by a function's dimension facts; and the
  callers' registries the facts carried down read.
-/

module

public import LeanVM.Guest.CoreMode.Fam.FamDefs
public import LeanVM.Guest.CoreMode.Fam.ParamRef
public import LeanVM.Guest.CoreMode.Gen.FnData
public import LeanVM.Guest.B1.Terminal.InterfaceP
public import LeanVM.Guest.B1.Selectors.ColumnSelector
import LeanVM.Guest.Data.Consts

/-!
# The dimension facts' family

`dimFacts`: function, base parameter, bound parameter, pairs `(k, c)`: the word at `[base]·g^k` is
`g^e`, the bound's `g^m`, `e + c ≤ m` (`FnReg.dimFacts`, each function's own
data). `dimB j w`: the point `[T]·B·g^d` inside `[T]·g^i`, `i` below `[M]`'s exponent
plus `t ≥ 1`, `B` the word at `[K]·g^k` (or a product of it and a constant `g^c` the code writes),
`(k, c + d)` a pair of such a fact on `K`, `M`.
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B2C (cellJ fsN)

@[expose] public section

/-! ## The claims' low dimensions -/

/-- **Dimension facts at listed parameters**: function, base parameter, bound parameter, pairs; each function's own
(`FnReg.dimFacts`). -/
abbrev dimFacts : List (String × ℕ × ℕ × List (ℕ × ℕ)) := CoreMode.FnReg.dimFacts

/-- The shape `dimB` reads: `[T]·B` and `[T]` up to `[o] + t`, as `(B, o, t)`. -/
def dimShape (a b : Mode.Rng) : Option (Mode.Base × ℕ × ℕ) :=
  match a.q.bs, b.q.bs, b.hi with
  | [(.fr T, 1), (B, 1)], [(.fr T', 1)], .ex (.fr o) t => if T = T' then some (B, o, t) else none
  | _, _, _ => none

/-- **Base `B` is the word at `[pk]·g^k` times `g^c`**, `ok k c`: `B` read there (`c = 0`), or a frame
cell a top-level product writes of a value a top-level load reads there and a constant `g^c`. -/
noncomputable def lowOk (j : ℕ) (w : Wit) (pk : V) (B : Mode.Base) (ok : ℕ → ℕ → Bool) : Bool :=
  match B with
  | .hp q k => inFr j q && cellJ j pk == q && ok k 0
  | .fr P => inFr j P && w.as.any fun
      | .mul P' y z => cellJ j P' == P && w.as.any fun
          | .load y' p k => decide (y' = y) && decide (p = pk) &&
              match (constOf w.as z).bind powOf with
              | some c => ok k c
              | none => false
          | _ => false
      | _ => false

/-- **A claim's low point inside its chain**: `[T]·B·g^d` inside `[T]·g^i`, `i` below `[o] + t`,
`B` the word at `[K]·g^k` times `g^c` (`lowOk`), `(k, c + d)` a pair of a dimension fact on the
parameters `K` and the one of cell `o`. -/
noncomputable def dimB (j : ℕ) (w : Wit) : Mode.Res → Bool
  | .sub a [b] => match dimShape a b with
    | some (B, o, t) =>
      a.lo == .num 0 && a.hi == .num 1 && a.d == 0 && b.lo == .num 0 && b.S == 1 && b.d == 0 &&
        a.q.fp == b.q.fp && decide (b.q.k ≤ a.q.k) && decide (1 ≤ t) && inFr j o &&
        dimFacts.any fun c ↦ c.1 == (coreOf j).name &&
          match (coreOf j).params[c.2.1]?, (coreOf j).params[c.2.2.1]? with
          | some pk, some pb => cellJ j pb == o &&
              lowOk j w pk B fun k c' ↦ c.2.2.2.contains (k, c' + (a.q.k - b.q.k))
          | _, _ => false
    | none => false
  | _ => false

/-! ## The callers -/

/-- **The callees whose facts are carried and their callers** (`Res.callersG`), each callee's own
(`FnReg.stCallers`). -/
abbrev termCallers : List (String × String) := CoreMode.FnReg.stCallers

/-- **The callees whose facts are carried and their callers** (`Res.callersM`), each callee's own
(`FnReg.glCallers`). -/
abbrev glCallers : List (String × List String) := CoreMode.FnReg.glCallers

end

end LeanVM.Guest.Res
