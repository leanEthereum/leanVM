/-
  LeanVM.Guest.CoreMode.FrameLit

  `frame_fn%`: the declarations `scripts/core-mode/frame_gen.py` writes for each function on the core
  route checked whole, written once here so that the generated modules state them in a line or two.
-/

module

public meta import Lean.Elab.Command

/-!
# A routed function's frame walk in one line

`frame_fn% «k» n [«m₀», …]` followed by optional clauses is

* `noncomputable def Fn.«k».envC : Mode.Env := CoreMode.envOf [Fn.«m₀».csig, …]`, its callees;
* `noncomputable def Fn.«k».funC : Mode.Fun := ⟨Fn.«k».entry, n, Fn.«k».csig, .nil, fnz, .nil, main, .nil⟩`;
* `noncomputable def Fn.«k».frameFun : CoreMode.FFun`, its frame walk's data: facts
  `{ env := env, fpOne := fpOne, pows := fpows, scaled := scaled }`, entry, length `n`, signature,
  the callees' signatures `sigs` (the callees' by default, `.nil` for none), the halting pc, the
  hints `advice.2.2`, `nzr`, `tidx`, `arms`, `calls`, the pairing's oracle `pairO` and stores
  `pairS`, no cut;
* `theorem Fn.«k».frameOk : CoreMode.frameOk frameFun code.chunks.flatten = true`, by the kernel.

The clauses, each when it is not the default: `sigs [«m₀», …]`, `env e`, `fpOne`, `scaled l`,
`nzr t`, `tidx t`, `arms t`, `calls t`, `fnz t` (`.nil` by default), `main` (`false`). Unhygienic:
it expands to the text the generator wrote before, its names resolved where it is written (in
`namespace LeanVM.Guest`), so its elaboration is the same.
-/

public section

namespace LeanVM.Guest.FrameLit

open Lean

/-- `Fn.«k».s`. -/
meta def fnDot (k : TSyntax `ident) (s : Name) : TSyntax `ident := mkIdent (`Fn ++ k.getId ++ s)

/-- `frame_fn% «k» n [«m₀», …] clauses`: `k`'s frame interface, frame walk data and the kernel's
check of its walk. -/
syntax (name := frameFn) "frame_fn% " ident num "[" ident,* "]" (&" sigs" "[" ident,* "]")?
  (&" env" term:max)? (&" fpOne")? (&" scaled" term:max)? (&" nzr" term:max)? (&" tidx" term:max)?
  (&" arms" term:max)? (&" calls" term:max)? (&" fnz" term:max)? (&" main")? : command

set_option hygiene false in
macro_rules
  | `(frame_fn% $k $n [$ms,*] $[sigs [$ss,*]]? $[env $e]? $[fpOne%$fp]? $[scaled $sc]? $[nzr $nz]? $[tidx $ti]?
      $[arms $ar]? $[calls $ca]? $[fnz $fz]? $[main%$mn]?) => do
    let csig (m : TSyntax `ident) := fnDot m `csig
    let ms := ms.getElems
    let ss := (ss.map (·.getElems)).getD ms
    let sigsT ← if ss.isEmpty then `(.nil) else `((CoreMode.sigTrie [$(ss.map csig),*]))
    let nil ← `(.nil)
    let e ← e.getDM `([])
    let sc ← sc.getDM `([])
    let fpT ← if fp.isSome then `(true) else `(false)
    let mainT ← if mn.isSome then `(true) else `(false)
    `(noncomputable def $(fnDot k `envC) : Mode.Env := CoreMode.envOf [$(ms.map csig),*]
      noncomputable def $(fnDot k `funC) : Mode.Fun :=
        ⟨$(fnDot k `entry), $n, $(fnDot k `csig), .nil, $(fz.getD nil), .nil, $mainT, .nil⟩
      noncomputable def $(fnDot k `frameFun) : CoreMode.FFun :=
        ⟨{ env := $e, fpOne := $fpT, pows := fpows, scaled := $sc }, $(fnDot k `entry), $n, $(fnDot k `csig),
          $sigsT, CoreMode.haltPc, advice.2.2, $(nz.getD nil), $(ti.getD nil), $(ar.getD nil), $(ca.getD nil),
          $(fnDot k `pairO), $(fnDot k `pairS), .nil⟩
      theorem $(fnDot k `frameOk) : CoreMode.frameOk frameFun code.chunks.flatten = true := by
        decide +kernel)

end LeanVM.Guest.FrameLit

end
