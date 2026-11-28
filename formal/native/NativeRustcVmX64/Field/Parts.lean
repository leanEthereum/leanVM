module

public import NativeRustcVmX64.Field.LinSound
public meta import Lean.Elab.Command
public meta import NativeRustcX64.Sym.Exec

/-!
# Blocks in parts

rustc's `kmul` and `EW::mul` reuse each bit-reversal and each product several times, so the
symbolic value of a whole block repeats them as a tree (millions of nodes). They are run in parts
(`slice`, its place in the program `IsInfixAt.slice`), each part's result named (`sym_part`), and
between two parts a register replaced by a variable of the environment equal to its value
(`Match.abs`, `Match.absRev`, by `Lin.check`, `Lin.checkRev`): the next part sees the variable.

`sym_part p := exec ds S`: the definitions `p.out` and `p.exit`, the executor's result as literals,
and the theorem `p.run : exec ds S = some (p.out, p.exit)`, checked by the kernel alone.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym Lean Elab Command Meta

/-- Adds `name.out`, `name.exit` and `name.run : t = some (name.out, name.exit)`, `t` the term `src`
of value `v`. -/
public meta def addPart (name : Name) (src : String) (v : Option (SState × Exit)) :
    CommandElabM Unit := do
  let some (S, x) := v | throwError "sym_part: the executor fails"
  let stx ← match Parser.runParserCategory (← getEnv) `term src with
    | .ok s => pure s
    | .error e => throwError "sym_part: cannot parse the block term: {e}"
  let base := (← getCurrNamespace) ++ name
  liftTermElabM do
    let ty := mkApp (mkConst ``Option [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``NativeRustcX64.Sym.SState) (mkConst ``NativeRustcX64.Sym.Exit))
    let lhs ← instantiateMVars (← Term.elabTermAndSynthesize stx ty)
    addDecl (.defnDecl (mkDefinitionValEx (Name.str base "out") []
      (mkConst ``NativeRustcX64.Sym.SState) (toExpr S) .abbrev .safe []))
    addDecl (.defnDecl (mkDefinitionValEx (Name.str base "exit") []
      (mkConst ``NativeRustcX64.Sym.Exit) (toExpr x) .abbrev .safe []))
    compileDecls #[Name.str base "out", Name.str base "exit"]
    let rhs := mkApp2 (mkConst ``Option.some [0])
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``NativeRustcX64.Sym.SState) (mkConst ``NativeRustcX64.Sym.Exit))
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``NativeRustcX64.Sym.SState) (mkConst ``NativeRustcX64.Sym.Exit)
        (mkConst (Name.str base "out")) (mkConst (Name.str base "exit")))
    let type ← mkEq lhs rhs
    let value ← mkEqRefl rhs
    let runName := Name.str base "run"
    let t0 ← IO.monoMsNow
    addDecl (.thmDecl { name := runName, levelParams := [], type, value })
    let t1 ← IO.monoMsNow
    logInfo m!"sym_part {base}: kernel check {t1 - t0} ms"

/-- `sym_part p := t`, `t : Option (SState × Exit)` (typically `exec ds S`): `p.out`, `p.exit` and
`p.run : t = some (p.out, p.exit)`, checked by the kernel. -/
syntax (name := symPart) "sym_part " ident " := " term : command

macro_rules
  | `(sym_part $n := $t) =>
    `(#eval show Lean.Elab.Command.CommandElabM Unit from
        NativeRustcVmX64.Field.addPart $(quote n.getId) $(quote t.raw.reprint.get!) ($t))

@[expose] public section

/-- The `n` directives of `ds` from its `i`th. -/
def slice (ds : List Directive) (i n : Nat) : List Directive := (ds.drop i).take n

end

public section

/-- A slice of a block is at the block's place plus its start. -/
theorem _root_.List.IsInfixAt.slice {ds P : List Directive} {k : Nat} (h : ds.IsInfixAt P k)
    (i n : Nat) (hi : i ≤ ds.length) : (Field.slice ds i n).IsInfixAt P (k + i) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨(ds.drop i).drop n ++ t, ?_⟩
  rw [Field.slice, ← List.append_assoc, List.take_append_drop, ← List.drop_drop, ← ht,
    List.drop_append_of_le_length hi]

/-- **A register abstracted**: a register whose value `check` finds equal to `t`'s may be
replaced by a variable holding `t`'s value. -/
theorem _root_.NativeRustcX64.Sym.Match.abs [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : Reg64} {fuel i : Nat} {t : Sym}
    (hc : (S.reg r).map (fun v ↦ Lin.check fuel v t) = some true) (ht : t.eval env = env.vars i) :
    Match env (S.setReg r (some (.var i))) m := by
  obtain ⟨v, hv, hcv⟩ := Option.map_eq_some_iff.mp hc
  refine hm.withReg ?_
  rw [hm.regs r v hv, Lin.eval_eq_of_check hcv env, ht]
  rfl

/-- **A register abstracted**, its value the reversal of `t`'s. -/
theorem _root_.NativeRustcX64.Sym.Match.absRev [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : Reg64} {fuel i : Nat} {t : Sym}
    (hc : (S.reg r).map (fun v ↦ Lin.checkRev fuel v t) = some true)
    (ht : (t.eval env).reverse = env.vars i) :
    Match env (S.setReg r (some (.var i))) m := by
  obtain ⟨v, hv, hcv⟩ := Option.map_eq_some_iff.mp hc
  refine hm.withReg ?_
  rw [hm.regs r v hv, Lin.eval_eq_of_checkRev hcv env, ht]
  rfl

/-- A register's value, by `check`. -/
theorem _root_.NativeRustcX64.Sym.Match.reg_check [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {r : Reg64} {fuel : Nat} {t : Sym}
    (hc : (S.reg r).map (fun v ↦ Lin.check fuel v t) = some true) :
    m.regs.get64 r = t.eval env := by
  obtain ⟨v, hv, hcv⟩ := Option.map_eq_some_iff.mp hc
  rw [hm.regs r v hv, Lin.eval_eq_of_check hcv env]

end

end NativeRustcVmX64.Field
