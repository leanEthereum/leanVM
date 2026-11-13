/-
  LeanVM.Guest.CoreRef

  `fn% s`, `idx% s`, `name% s`, `core% s m` and `core_eq% s m`: a core function by its stable name
  `s`, elaborated to what its index names.
-/

module

public meta import Lean.Elab.Term
public meta import Lean.Meta.Eqns

/-!
# Core functions by stable name

The generated `Data/Names.lean` and `Data/NameStrings.lean` give each core function a stable name
`s` (`Data.F.«s»`, `Data.I.«s»`, `Data.N.«s»`), which no added or removed function changes. A proof
names a function through them, and the terms it elaborates to are those its index gives: the
constant `Data.core{j}`, the numeral `j`, the string literal. So a proof reads exactly as one that
spelled the index, and a renumbering changes no proof.

* `fn% s`: `Data.core{j}`; `idx% s`: `j`; `name% s`: the function's name; `core_count%`: the
  number of core functions; `fn_idx% s`: `j + 1`, its index among the compiled functions
  (`coreOf`, `certOf`); `fn_count%`: their number (`nFns`), the entry's included;
* `core% s m`: the definition `Data.core{j}.m` of its generated layout (`body`, chunk `c3`, block
  `s40_e`);
* `core_eq% s`, `core_eq% s m`: the defining equation of `Data.core{j}` or of `Data.core{j}.m`, a
  rule for `simp` and `rw`.
-/

public meta section

namespace LeanVM.Guest.CoreRef

open Lean Elab Term Meta

/-- The value of `LeanVM.Guest.Data.{ns}.«s»`. -/
def valueOf (ns : Name) (s : Ident) : TermElabM Expr := do
  let n := `LeanVM.Guest.Data ++ ns ++ s.getId
  let some (.defnInfo d) := (← getEnv).find? n | throwErrorAt s "no stable name {s.getId} ({n})"
  return d.value

/-- The generated constant of the function of stable name `s`, or its member `m`. -/
def target (s : Ident) (m : Option Ident) : TermElabM Name := do
  let .const c _ ← valueOf `F s | throwErrorAt s "{s.getId} is not a generated function"
  return match m with
    | some m => c ++ m.getId
    | none => c

/-- `fn% s`: the core function of stable name `s`. -/
elab:max "fn% " s:ident : term => valueOf `F s

/-- `idx% s`: the index in `coreProgram` of the function of stable name `s`. -/
elab:max "idx% " s:ident : term => valueOf `I s

/-- `name% s`: the name of the function of stable name `s`. -/
elab:max "name% " s:ident : term => valueOf `N s

/-- `core_count%`: the number of core functions. -/
elab:max "core_count%" : term => do
  let some (.defnInfo d) := (← getEnv).find?
      `LeanVM.Guest.Data.coreCount | throwError "no coreCount"
  return d.value

/-- The numeral one past the numeral `v`. -/
def succLit (v : Expr) : TermElabM Expr := do
  let v ← instantiateMVars v
  let n? := if v.isAppOfArity ``OfNat.ofNat 3 then v.appFn!.appArg!.rawNatLit? else v.rawNatLit?
  let some n := n? | throwError "not a numeral: {v}"
  return mkNatLit (n + 1)

/-- `fn_count%`: the number of compiled functions, the core functions and the entry, a numeral
(`nFns`). -/
elab:max "fn_count%" : term => do
  let some (.defnInfo d) := (← getEnv).find? `LeanVM.Guest.Data.coreCount | throwError "no coreCount"
  succLit d.value

/-- `fn_idx% s`: the compiled index of the function of stable name `s`, one past its index in
`coreProgram` (`coreOf`, `certOf`, `CutsKnown`), a numeral. -/
elab:max "fn_idx% " s:ident : term => do succLit (← valueOf `I s)

/-- `core% s m`: the member `m` of the generated function of stable name `s`. -/
elab:max "core% " s:ident m:ident : term => do
  let c ← target s m
  unless (← getEnv).contains c do throwErrorAt m "no {c}"
  return mkConst c

/-- `core_eq% s` and `core_eq% s m`: the defining equation of the generated function of stable
name `s`, or of its member `m`. -/
elab "core_eq% " s:ident m:(ident)? : term => do
  let c ← target s m
  let some eqs ← getEqnsFor? c | throwError "no equation for {c}"
  return mkConst eqs[0]!

end LeanVM.Guest.CoreRef
