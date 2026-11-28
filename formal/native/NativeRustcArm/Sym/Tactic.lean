module

public import NativeRustcArm.Sym.Exec
public meta import Lean.Elab.Command
public meta import NativeRustcArm.Sym.Exec

/-!
# Running the symbolic executor on a block

`sym_block name := exec ds S` runs the executor (compiled code, an untrusted oracle) on the block
`ds` from `S` and adds the theorem `name : exec ds S = r` with `r` the result as a literal
(`some (S', x)`, with `S'` explicit), checked by the kernel alone: its proof is `Eq.refl r`, the
kernel evaluating `exec ds S` to `r`. It reports the kernel's time.
-/

namespace NativeRustcArm.Sym

open Lean Elab Command Meta

/-- Adds the theorem `name : t = toExpr v`, `t` the term `src`, proved by `Eq.refl` and checked
by the kernel. -/
public meta def addBlockThm (name : Name) (src : String) (v : Option (SState × Exit)) :
    CommandElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError "sym_block: cannot parse the block term: {e}"
  let declName := (← getCurrNamespace) ++ name
  liftTermElabM do
    let ty := mkApp (mkConst ``Option [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``SState) (mkConst ``Exit))
    let lhs ← instantiateMVars (← Term.elabTermAndSynthesize stx ty)
    let rhs := toExpr v
    let type ← mkEq lhs rhs
    let value ← mkEqRefl rhs
    let t0 ← IO.monoMsNow
    addDecl (.thmDecl { name := declName, levelParams := [], type, value })
    let t1 ← IO.monoMsNow
    let res := match v with
      | some (_, .fall) => "falls through"
      | some (_, .jump l) => s!"jumps to {l}"
      | some (_, .cond _ l) => s!"branches to {l} or falls through"
      | some (_, .call l) => s!"calls {l}"
      | some (_, .ret) => "returns"
      | none => "fails"
    logInfo m!"sym_block {declName}: {res}; kernel check {t1 - t0} ms"

/-- `sym_block name := t`, `t : Option (SState × Exit)` (typically `exec ds S`): the theorem
`name : t = r`, `r` the literal value of `t`, checked by the kernel. -/
syntax (name := symBlock) "sym_block " ident " := " term : command

macro_rules
  | `(sym_block $n := $t) =>
    `(#eval show Lean.Elab.Command.CommandElabM Unit from
        NativeRustcArm.Sym.addBlockThm $(quote n.getId) $(quote t.raw.reprint.get!) ($t))

end NativeRustcArm.Sym
