/-
  LeanVM.Guest.B2C.WinLit

  `win_lit`: a split window's common part (`winPre`), its executor run in compiled code, written
  as a value the kernel checks.
-/

module

public import LeanVM.Guest.B2C.SplitPre
public meta import LeanVM.Guest.ExecC
public meta import LeanVM.Guest.KernelLit
public meta import Lean.ToExpr

/-!
# A window's common part, computed once

`kernel_lit x : WinPre := winPre j i` finds the normal form of `winPre j i` by the kernel's weak
head normal form, field by field: it runs the executor on the window inside `Kernel.whnf`, as slow
as the kernel's own check of it. `win_lit x j i` runs the executor (`Exec.pass`, whose
compiled form is `passC` by `@[csimp]`) in compiled code instead, on the window's code, facts and
environment read off their normal forms (`ofE`), indexes and links the segments the same way
(`index`, `linkedWeak`), and writes the result back as a term (`ToExpr`); the other fields are the
kernel's normal forms (`KernelLit.nf`). It adds, as `kernel_lit` does,

* `def x : WinPre := v`, `v` constructors and literals only;
* `theorem x_eq : winPre j i = x`, by `rfl`,

and the kernel checks both: compiled code only proposes `v`, which a wrong value fails.
-/

open Lean Elab Command Meta

namespace LeanVM.Guest.Exec

/-! ## Values as terms -/

public meta section

/-- A natural number as a raw literal, as the kernel's normal forms have it. -/
local instance (priority := high) natToExpr : ToExpr ℕ := ⟨mkRawNatLit, mkConst ``Nat⟩

deriving instance ToExpr for LeanVM.Semantics.DerefMode
deriving instance ToExpr for LeanVM.Semantics.KeccakOutputCells
deriving instance ToExpr for LeanVM.Guest.OffsetInstruction
deriving instance ToExpr for Sym
deriving instance ToExpr for Tgt
deriving instance ToExpr for Trie
deriving instance ToExpr for Atom
deriving instance ToExpr for Kind
deriving instance ToExpr for Exit
deriving instance ToExpr for Item
deriving instance ToExpr for Seg

/-! ## Terms as values

A term is read back as the value it denotes, lazily: a constructor application or a literal as it
stands (a numeral `OfNat.ofNat ℕ n _` as `n`), anything else first put in weak head normal form by
the kernel (`hnf`), so that data written out as constructors costs no kernel call. -/

/-- `e` with a constructor or a literal at its head. -/
def hnf (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if e.isLit then return e
  if e.isAppOfArity ``OfNat.ofNat 3 && e.appArg!.isAppOf ``instOfNatNat then
    if let .lit (.natVal n) := (e.getArg! 1).consumeMData then return mkRawNatLit n
  if let .const c _ := e.getAppFn then
    if let some (.ctorInfo ci) := (← getEnv).find? c then
      if e.getAppNumArgs == ci.numParams + ci.numFields then return e
  match Kernel.whnf (← getEnv) {} e with
  | .ok w => return w
  | .error _ => throwError "win_lit: the kernel's weak head normal form failed"

/-- The constructor at the head of `e`, and its fields. -/
def ctorOf (e : Expr) (nparams : ℕ) : MetaM (Name × Array Expr) := do
  let e ← hnf e
  let .const c _ := e.getAppFn | throwError "win_lit: no constructor at the head of {e}"
  return (c, e.getAppArgs.extract nparams)

def natOf (e : Expr) : MetaM ℕ := do
  match ← hnf e with
  | .lit (.natVal n) => return n
  | e => throwError "win_lit: not a literal: {e}"

def boolOf (e : Expr) : MetaM Bool := do
  match (← ctorOf e 0).1 with
  | ``Bool.true => return true
  | ``Bool.false => return false
  | _ => throwError "win_lit: not a Bool: {e}"

partial def listOf {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM (List α) := do
  let (c, xs) ← ctorOf e 1
  match c with
  | ``List.nil => return []
  | ``List.cons => return (← f xs[0]!) :: (← listOf f xs[1]!)
  | _ => throwError "win_lit: not a list: {e}"

def pairOf {α β : Type} (f : Expr → MetaM α) (g : Expr → MetaM β) (e : Expr) : MetaM (α × β) := do
  let (_, xs) ← ctorOf e 2
  return (← f xs[0]!, ← g xs[1]!)

def optionOf {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM (Option α) := do
  let (c, xs) ← ctorOf e 1
  if c == ``Option.some then return some (← f xs[0]!) else return none

def symOf (e : Expr) : MetaM Sym := do
  let (c, xs) ← ctorOf e 0
  match c with
  | ``Sym.zero => return .zero
  | ``Sym.gp => return .gp (← natOf xs[0]!)
  | ``Sym.fpg => return .fpg (← natOf xs[0]!)
  | _ => throwError "win_lit: not a Sym: {e}"

/-- A trie, each value read once however many entries share its term (a table's arms). -/
partial def trieOf {α : Type} (f : Expr → MetaM α) (e : Expr) : MetaM (Trie α) :=
  go e |>.run' {}
where
  go (e : Expr) : StateT (Std.HashMap Expr α) MetaM (Trie α) := do
    let (c, xs) ← ctorOf e 1
    match c with
    | ``Trie.nil => return .nil
    | ``Trie.node =>
      let v ← match ← ctorOf xs[0]! 1 with
        | (``Option.some, ys) => match (← get)[ys[0]!]? with
          | some a => pure (some a)
          | none => do
            let a ← f ys[0]!
            modify (·.insert ys[0]! a)
            pure (some a)
        | _ => pure none
      return .node v (← go xs[1]!) (← go xs[2]!)
    | _ => throwError "win_lit: not a Trie: {e}"

partial def powTreeOf (e : Expr) : MetaM PowTree := do
  let (c, xs) ← ctorOf e 0
  match c with
  | ``PowTree.leaf => return .leaf
  | ``PowTree.node =>
    return .node (← natOf xs[0]!) (← natOf xs[1]!) (← powTreeOf xs[2]!) (← powTreeOf xs[3]!)
  | _ => throwError "win_lit: not a PowTree: {e}"

def factsOf (e : Expr) : MetaM Facts := do
  let (_, xs) ← ctorOf e 0
  return ⟨← listOf (pairOf natOf symOf) xs[0]!, ← boolOf xs[1]!, ← powTreeOf xs[2]!,
    ← listOf (pairOf natOf (listOf natOf)) xs[3]!, ← trieOf (listOf natOf) xs[4]!,
    ← listOf natOf xs[5]!⟩

open LeanVM.Semantics in
def insOf (e : Expr) : MetaM LeanVM.Guest.OffsetInstruction := do
  let (c, xs) ← ctorOf e 0
  let n (k : ℕ) := natOf xs[k]!
  match c with
  | ``OffsetInstruction.xor => return .xor (← n 0) (← n 1) (← n 2)
  | ``OffsetInstruction.mul => return .mul (← n 0) (← n 1) (← n 2)
  | ``OffsetInstruction.set => return .set (← n 0) (← n 1) (← n 2)
  | ``OffsetInstruction.deref =>
    let mode ← match (← ctorOf xs[3]! 0).1 with
      | ``DerefMode.cell => pure DerefMode.cell
      | ``DerefMode.pc => pure DerefMode.pc
      | ``DerefMode.fp => pure DerefMode.fp
      | _ => throwError "win_lit: not a DerefMode: {xs[3]!}"
    return .deref (← n 0) (← n 1) (← n 2) mode
  | ``OffsetInstruction.jump => return .jump (← n 0) (← n 1) (← n 2)
  | ``OffsetInstruction.keccak =>
    let cells ← match (← ctorOf xs[10]! 0).1 with
      | ``KeccakOutputCells.one => pure KeccakOutputCells.one
      | ``KeccakOutputCells.two => pure KeccakOutputCells.two
      | ``KeccakOutputCells.all => pure KeccakOutputCells.all
      | _ => throwError "win_lit: not a KeccakOutputCells: {xs[10]!}"
    return .keccak (← n 0) (← n 1) (← n 2) (← n 3) (← n 4) (← n 5) (← n 6) (← n 7)
      (← boolOf xs[8]!) (← boolOf xs[9]!) cells
  | _ => throwError "win_lit: not an instruction: {e}"

/-! ## The window -/

/-- `Check.linkedWeak`, its trie read by `Trie.get`. -/
def linkedWeakC (idx : Trie Seg) (segs : List Seg) (wJ : ℕ) (wenv : Trie Sym) : Bool :=
  segs.all fun s ↦ s.exits.all fun x ↦ x.succ.all fun t ↦
    match idx.get t with
    | some s' => s'.start == t && s'.env.sub Sym.beq x.env
    | none => !(t == wJ) || wenv.sub Sym.beq x.env

/-- A trie as a term, its values' terms given. -/
def trieE {α : Type} (ty : Expr) (f : α → Expr) : Trie α → Expr
  | .nil => mkApp (mkConst ``Trie.nil) ty
  | .node v l r =>
    mkApp4 (mkConst ``Trie.node) ty
      (match v with
        | some a => mkApp2 (mkConst ``Option.some [Level.zero]) ty (f a)
        | none => mkApp (mkConst ``Option.none [Level.zero]) ty)
      (trieE ty f l) (trieE ty f r)

end

end LeanVM.Guest.Exec

namespace LeanVM.Guest.B2C

open LeanVM.Guest.Exec

public meta section

/-- The term `stx`, elaborated. -/
def termOf (stx : Term) : TermElabM Expr := do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The kernel's normal form (`KernelLit.nf`) of the term `stx`. -/
def nfOf (stx : Term) : TermElabM Expr := do
  (KernelLit.nf (← termOf stx)).run' {}

/-- `win_lit x j i` adds `def x : WinPre`, `winPre j i` computed with the executor in compiled
code, and `theorem x_eq : winPre j i = x`, by `rfl`; the kernel checks both. -/
syntax (name := winLit) (docComment)? "win_lit " ident ppSpace num ppSpace num : command

@[command_elab winLit] def elabWinLit : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[2].getId
  let j : TSyntax `num := ⟨stx[3]⟩
  let i : TSyntax `num := ⟨stx[4]⟩
  let (e, v) ← liftTermElabM do
    -- the executor's input, read back
    let F ← factsOf (← termOf (← `((certOf $j).facts)))
    let entry ← natOf (← termOf (← `((fnOf $j).entryPc)))
    let len ← natOf (← termOf (← `((fnOf $j).instructionCount)))
    let a ← natOf (← termOf (← `(((certOf $j).cutAt $i).J)))
    let b ← natOf (← termOf (← `((certOf $j).endAt (fnOf $j) $i)))
    let code ← listOf insOf (← termOf (← `((codeFrom (fnOf $j) $(quote a)).take $(quote (b - a)))))
    let env ← listOf (pairOf natOf symOf) (← termOf (← `(((certOf $j).cutAt $i).env)))
    let seeds ← listOf natOf (← termOf (← `(((certOf $j).succAt $i).drop 1)))
    let wJ ← natOf (← termOf (← `(bif Nat.blt $i (certOf $j).cuts.length then
      ((certOf $j).cutAt ($i + 1)).J else 0)))
    let wenv ← listOf (pairOf natOf symOf) (← termOf (← `(bif Nat.blt $i (certOf $j).cuts.length then
      ((certOf $j).cutAt ($i + 1)).env else [])))
    -- the run, compiled (`execWinCS`), its index and links
    let env0 := envOf env
    let segs := (pass F entry len code a (some (Cur.init a env0)) (seeds.map fun t ↦ (t, env0)) [] 0).segs
    let idx := index segs
    let lw := linkedWeakC idx segs wJ (envOf wenv)
    -- the value, each segment's term shared by the list and the index
    let segTy := mkConst ``Seg
    let segE := segs.map fun s ↦ (s.start, toExpr s)
    let byStart : Std.HashMap ℕ Expr := segE.foldl (fun m p ↦ m.insert p.1 p.2) {}
    let segsE := segE.foldr (fun p l ↦ mkApp3 (mkConst ``List.cons [Level.zero]) segTy p.2 l)
      (mkApp (mkConst ``List.nil [Level.zero]) segTy)
    let idxE := trieE segTy (fun s ↦ byStart.getD s.start (toExpr s)) idx
    let field (f : Name) : TermElabM Expr := do
      nfOf (← `(($(mkIdent f) (winPre $j $i))))
    let v := mkAppN (mkConst ``WinPre.mk) #[segsE, idxE, ← field ``WinPre.stat, ← field ``WinPre.nv,
      ← field ``WinPre.pst, ← field ``WinPre.wst, toExpr lw]
    let e ← Term.elabTerm (← `(winPre $j $i)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    return (← instantiateMVars e, v)
  let ty := mkConst ``WinPre
  liftCoreM <| addDecl (forceExpose := true)
    (.defnDecl (mkDefinitionValEx name [] ty v .abbrev .safe []))
  if let some doc := stx[0].getOptional? then
    liftTermElabM <| addDocString name (mkNullNode #[]) ⟨doc⟩
  let c := mkConst name
  liftCoreM <| addDecl
    (.thmDecl (mkTheoremValEx (name.appendAfter "_eq") [] (mkApp3 (mkConst ``Eq [1]) ty e c)
      (mkApp2 (mkConst ``Eq.refl [1]) ty c) []))

end

end LeanVM.Guest.B2C
