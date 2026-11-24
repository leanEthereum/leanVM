/-
  LeanVM.Guest.CodeLit

  `code% [i₀, …]`: a list of instructions written as the elaborator writes it, without elaborating
  each instruction.
-/

module

public import Statement.LeanIsa
public meta import Lean.Elab.Term

/-!
# Instruction lists as terms

A pack's copy of a function's code (`Pack/*/Bundle.lean`, `lake exe guest-cert`) is thousands of
instructions of literals. The elaborator takes about two milliseconds for each: it elaborates every
constructor application and numeral. `code% [(.set 60 1 0), (.deref 59 0 63 .cell), …]` reads the
same text and builds the term directly: each instruction its constructor applied to numerals as the
elaborator writes them (`OfNat.ofNat ℕ n (instOfNatNat n)`), the list its `List.cons`es. Nothing is
trusted: the term is the definition's value, which the kernel checks against the statement's code
(`Checked/Link*`).
-/

namespace LeanVM.Guest.CodeLit

open Lean Elab Term Meta LeanVM.Semantics

public meta section

/-- `code% [i₀, …]`: the instructions, each `(.xor a b c)`, `(.mul a b c)`, `(.set o k₀ k₁)`,
`(.deref a b c .cell)` (`.pc`, `.fp`), `(.jump a b c)` or
`(.keccak m₀ m₁ m₂ m₃ t b₈ c o inOdd outOdd .one)` (`.two`, `.all`), with numerals and `true`,
`false`. -/
syntax (name := codeLit) "code% " "[" term,* "]" : term

/-- A numeral, as the elaborator writes it at type `ℕ`. -/
def natE (stx : Syntax) : TermElabM Expr := do
  match stx.isNatLit? with
  | some n => return mkNatLit n
  | none => throwErrorAt stx "code%: not a numeral"

def boolE (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(true) => return Lean.mkConst ``Bool.true
  | `(false) => return Lean.mkConst ``Bool.false
  | _ => throwErrorAt stx "code%: not a Bool"

def modeE (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(.cell) => return Lean.mkConst ``DerefMode.cell
  | `(.pc) => return Lean.mkConst ``DerefMode.pc
  | `(.fp) => return Lean.mkConst ``DerefMode.fp
  | _ => throwErrorAt stx "code%: not a DerefMode"

def cellsE (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(.one) => return Lean.mkConst ``KeccakOutputCells.one
  | `(.two) => return Lean.mkConst ``KeccakOutputCells.two
  | `(.all) => return Lean.mkConst ``KeccakOutputCells.all
  | _ => throwErrorAt stx "code%: not a KeccakOutputCells"

/-- An instruction. -/
partial def insE (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(($i:term)) => insE i
  | `(.xor $a $b $c) => return mkApp3 (Lean.mkConst ``OffsetInstruction.xor) (← natE a) (← natE b) (← natE c)
  | `(.mul $a $b $c) => return mkApp3 (Lean.mkConst ``OffsetInstruction.mul) (← natE a) (← natE b) (← natE c)
  | `(.set $a $b $c) => return mkApp3 (Lean.mkConst ``OffsetInstruction.set) (← natE a) (← natE b) (← natE c)
  | `(.jump $a $b $c) => return mkApp3 (Lean.mkConst ``OffsetInstruction.jump) (← natE a) (← natE b) (← natE c)
  | `(.deref $a $b $c $m) =>
    return mkApp4 (Lean.mkConst ``OffsetInstruction.deref) (← natE a) (← natE b) (← natE c) (← modeE m)
  | `(.keccak $m0 $m1 $m2 $m3 $t $b8 $cp $o $i $j $n) =>
    return mkAppN (Lean.mkConst ``OffsetInstruction.keccak) #[← natE m0, ← natE m1, ← natE m2, ← natE m3,
      ← natE t, ← natE b8, ← natE cp, ← natE o, ← boolE i, ← boolE j, ← cellsE n]
  | _ => throwErrorAt stx "code%: not an instruction"

@[term_elab codeLit] def elabCodeLit : TermElab := fun stx _ => do
  let ty := Lean.mkConst ``OffsetInstruction
  let elems := stx[2].getSepArgs
  let mut l := mkApp (Lean.mkConst ``List.nil [Level.zero]) ty
  for e in elems.reverse do
    l := mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty (← insE e) l
  return l

end

end LeanVM.Guest.CodeLit
