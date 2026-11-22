/-
  LeanVM.Guest.ValRef

  `val% f "name"` and `pos% f "name"`: a core value's number, and a top-level statement's position,
  by the value's source name or expansion path, elaborated to the numeral.
-/

module

public meta import Lean.Elab.Term

/-!
# Core values by name

The core IR numbers a function's values densely (`Fn.renumber`): value `n` is `V.n n`, and a
compiler change renumbers them. A proof names a value instead:

* by its source name, the zkDSL variable it is first bound to (`Expand.rebind`): `acc` when no
  other value of the function is named `acc` first, else `g.acc` through `g`, the innermost function
  inlined there, when that is unique, else `acc@2`, the second value named `acc` (cells of a buffer
  `buf[3]`, parameters by their names);
* else by its expansion path, the position of its statement in the source
  (`s3.i3:verify_lean_xmss.s8#0`: statement 3, inlined `verify_lean_xmss`, its statement 8).

`lake exe guest-core --names` lists both.

* `val% f "name"`: the number of the value `name` of the function of stable name `f`;
  `val% f g … "name"`, of the functions `f`, `g`, … that one template is tied to, their common
  number (an error when they differ);
* `valf% f "name"`: the common number of `name` in every specialization `f__L…` of the source
  function `f`, `valf% f «_loop0» "name"` in their loops `f__L…_loop0` (written to
  `Data/ValNames/«f__L».lean`, `«f__L_loop0».lean`, only when they agree);
* `pos% f "name"`: the position in `f`'s body of the top-level statement that names `name` first
  (`ret`: the body's final `ret`; `name+d`: the statement `d` past `name`'s, a statement that names
  no new value); `span% f "a" "b"`, the number of statements from `a`'s to `b`'s.

All four elaborate to the numeral the generated `Data/ValNames/«f».lean` gives them
(`scripts/val-names/gen.py`, which writes the names the proofs cite, from `guest-core --names`), so
a proof reads as one that spelled the numeral, and a renumbering changes no proof. A module that
cites them imports `LeanVM.Guest.Data.ValNames.«f»`, privately: only its importers rebuild when
`f` is renumbered.
-/

public meta section

namespace LeanVM.Guest.ValRef

open Lean Elab Term

/-- The value of `LeanVM.Guest.Data.ValNames.{ns}.«f/name»`. -/
def lookup (ns : Name) (f : Ident) (n : TSyntax `str) : TermElabM Expr := do
  let c := `LeanVM.Guest.Data.ValNames ++ ns ++ .mkSimple s!"{f.getId}/{n.getString}"
  -- a numeral, so a template's exposed body may cite a name its module imports privately
  let some (.defnInfo d) := (← withoutExporting getEnv).find? c |
    throwErrorAt n "no {ns} {n.getString} of {f.getId} ({c}): import LeanVM.Guest.Data.ValNames.«{f.getId}» (`«{f.getId}__L»` for `valf%`) and run scripts/val-names/gen.py"
  return d.value

/-- The natural number a generated numeral denotes. -/
def natOf (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then e.appFn!.appArg!.rawNatLit? else e.rawNatLit?

/-- `val% f "name"`: the number of the value `name` of the core function of stable name `f`;
`val% f g … "name"`: the common number of `name` in the functions `f`, `g`, …. -/
elab:max "val% " fs:ident+ n:str : term => do
  let es ← fs.mapM (lookup `V · n)
  for (f, e) in fs.zip es do
    unless natOf e == natOf es[0]! do
      throwErrorAt n "{n.getString} is value {natOf e} of {f.getId} but {natOf es[0]!} of {fs[0]!.getId}"
  return es[0]!

/-- `valf% f "name"`: the common number of the value `name` in every specialization `f__L…` of the
source function `f`; `valf% f «_loop0» "name"`, in each one's loop `f__L…_loop0`. -/
elab:max "valf% " f:ident s:(ident)? n:str : term => do
  let key := s!"{f.getId}__L" ++ (s.map (·.getId.toString)).getD ""
  lookup `F (mkIdentFrom f (.mkSimple key)) n

/-- `pos% f "name"`: the position in the body of the core function of stable name `f` of the
top-level statement that names the value `name` first. -/
elab:max "pos% " f:ident n:str : term => lookup `S f n

/-- `span% f "a" "b"`: the number of top-level statements of `f`'s body from the one `pos% f "a"`
names up to the one `pos% f "b"` names, a numeral (a slice's length, as `take` reads it). -/
elab:max "span% " f:ident a:str b:str : term => do
  let some i := natOf (← lookup `S f a) | throwErrorAt a "not a numeral"
  let some j := natOf (← lookup `S f b) | throwErrorAt b "not a numeral"
  unless i ≤ j do throwErrorAt b "{b.getString} (statement {j}) is before {a.getString} (statement {i})"
  return mkNatLit (j - i)

end LeanVM.Guest.ValRef
