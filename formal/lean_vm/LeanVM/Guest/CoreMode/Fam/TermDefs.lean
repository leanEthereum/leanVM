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
data).
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

/-- The shape of a dimension residual: `[T]·B` and `[T]` up to `[o] + t`, as `(B, o, t)`. -/
def dimShape (a b : Mode.Rng) : Option (Mode.Base × ℕ × ℕ) :=
  match a.q.bs, b.q.bs, b.hi with
  | [(.fr T, 1), (B, 1)], [(.fr T', 1)], .ex (.fr o) t => if T = T' then some (B, o, t) else none
  | _, _, _ => none

/-! ## The callers -/

/-- **The callees whose facts are carried and their callers** (`Res.callersG`), each callee's own
(`FnReg.stCallers`). -/
abbrev termCallers : List (String × String) := CoreMode.FnReg.stCallers

/-- **The callees whose facts are carried and their callers** (`Res.callersM`), each callee's own
(`FnReg.glCallers`). -/
abbrev glCallers : List (String × List String) := CoreMode.FnReg.glCallers

end

end LeanVM.Guest.Res
