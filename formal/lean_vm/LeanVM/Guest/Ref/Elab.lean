/-
  LeanVM.Guest.Ref.Elab

  A link's map computed at elaboration time and written into a definition, so that the kernel
  only checks it.
-/

module

public meta import LeanVM.Guest.Ref.Link
public meta import Lean.Meta.Basic

/-!
# Maps computed once

The link of a core function and its reference function is checked against a map (`Map.check`).
The kernel can infer the map too (`Linked`), but for a large function, checked in pieces in
declarations of their own (`Map.Pieces`), each piece would infer it again. So a function's module
computes it here, at elaboration, and writes it into a definition as literal data:

* `decFn n`: the core function the constant `n` holds, read off its definition's term (the
  generated packs' constructors, lists, appends and the definitions they name);
* `mapE`: the term of a map, its entries in chunks.

Nothing here is trusted: the kernel checks the map written, and a wrong entry can only make a
check fail.
-/

public meta section

namespace LeanVM.Guest.Ref.Elab

open Lean Meta LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

/-- A numeral. -/
partial def decNat (e : Expr) : MetaM Nat := do
  match e with
  | .lit (.natVal n) => return n
  | .mdata _ e => decNat e
  | _ => match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => decNat n
    | _ => throwError "decNat: {e}"

private def decBool (e : Expr) : MetaM Bool := do
  if e.isConstOf ``Bool.true then return true
  if e.isConstOf ``Bool.false then return false
  throwError "decBool: {e}"

private def decV (e : Expr) : MetaM V := do
  match e.getAppFnArgs with
  | (``V.n, #[k]) => return V.n (← decNat k)
  | _ => throwError "decV: {e}"

private def decE (e : Expr) : MetaM E := do
  match e.getAppFnArgs with
  | (``word, #[a, b]) => return word (← decNat a) (← decNat b)
  | _ => throwError "decE: {e}"

/-- The elements of a list term, through appends and the definitions it names. -/
partial def decList {α : Type} (d : Expr → MetaM α) (e : Expr) : MetaM (List α) := do
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return (← d h) :: (← decList d t)
  | (``List.nil, #[_]) => return []
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) => return (← decList d a) ++ (← decList d b)
  | _ => match e with
    | .const n _ =>
        let some v := (← getEnv).find? n |>.bind (·.value?) | throwError "decList: {n}"
        decList d v
    | .mdata _ e => decList d e
    | _ => throwError "decList: {e.getAppFn}"

/-- An atom; a hint's contents are dropped (the check reads none). -/
def decAtom (e : Expr) : MetaM Atom := do
  match e.getAppFnArgs with
  | (``Atom.const, #[d, c]) => return .const (← decV d) (← decE c)
  | (``Atom.add, #[d, a, b]) => return .add (← decV d) (← decV a) (← decV b)
  | (``Atom.mul, #[d, a, b]) => return .mul (← decV d) (← decV a) (← decV b)
  | (``Atom.copy, #[d, s]) => return .copy (← decV d) (← decV s)
  | (``Atom.load, #[d, p, o]) => return .load (← decV d) (← decV p) (← decNat o)
  | (``Atom.assertEq, #[a, b]) => return .assertEq (← decV a) (← decV b)
  | (``Atom.rangeCheck, #[x, y, t1, t2, k]) =>
      return .rangeCheck (← decV x) (← decV y) (← decV t1) (← decV t2) (← decV k)
  | (``Atom.keccak, #[i, o, a, b]) =>
      return .keccak (← decList decV i) (← decList decV o) (← decBool a) (← decBool b)
  | (``Atom.hint, #[_]) => return .hint (.witness "" (.stack []))
  | _ => throwError "decAtom: {e.getAppFn}"

private partial def decStmt (e : Expr) : MetaM Stmt := do
  match e.getAppFnArgs with
  | (``Stmt.atom, #[a]) => return .atom (← decAtom a)
  | (``Stmt.match_, #[x, arms]) => return .match_ (← decV x) (← decList (decList decStmt) arms)
  | (``Stmt.ite, #[c, z, n]) => return .ite (← decV c) (← decList decStmt z) (← decList decStmt n)
  | (``Stmt.ret, #[vs]) => return .ret (← decList decV vs)
  | _ => throwError "decStmt: {e.getAppFn}"

/-- The core function the constant `n` holds. -/
def decFn (n : Name) : MetaM Fn := do
  let some v := (← getEnv).find? n |>.bind (·.value?) | throwError "decFn: {n}"
  match v.getAppFnArgs with
  | (``Fn.mk, #[.lit (.strVal s), ps, b]) => return ⟨s, ← decList decV ps, ← decList decStmt b⟩
  | _ => throwError "decFn: {v.getAppFn}"

/-- The term of a word, by its limbs. -/
def eE (w : E) : Expr :=
  mkApp2 (mkConst ``word) (mkNatLit (w.limb 0).toBitVec.toNat) (mkNatLit (w.limb 1).toBitVec.toNat)

/-- The term of a term over names. -/
def tmE {X : Type} [ToExpr X] : Tm X → Expr
  | .v x => mkApp2 (mkConst ``Tm.v) (toTypeExpr X) (toExpr x)
  | .const w => mkApp2 (mkConst ``Tm.const) (toTypeExpr X) (eE w)
  | .add a b => mkApp3 (mkConst ``Tm.add) (toTypeExpr X) (tmE a) (tmE b)
  | .mul a b => mkApp3 (mkConst ``Tm.mul) (toTypeExpr X) (tmE a) (tmE b)

/-- The term of a list of type `ty`: itself up to `4096` elements, else chunks of `4096`,
flattened, so that no term is deeper. -/
def listE (ty : Expr) (l : List Expr) : Expr :=
  let cons (t : Expr) (x acc : Expr) := mkApp3 (mkConst ``List.cons [.zero]) t x acc
  let nil (t : Expr) := mkApp (mkConst ``List.nil [.zero]) t
  let rec chunks : Nat → List Expr → List (List Expr)
    | 0, _ => []
    | f + 1, xs => if xs.isEmpty then [] else xs.take 4096 :: chunks f (xs.drop 4096)
  let lty := mkApp (mkConst ``List [.zero]) ty
  match (chunks (l.length + 1) l).map fun c => c.foldr (cons ty) (nil ty) with
  | [c] => c
  | cs => mkApp2 (mkConst ``List.flatten [.zero]) ty (cs.foldr (cons lty) (nil lty))

/-- The term of a map. -/
def mapE {X : Type} [ToExpr X] (m : Map X) : Expr :=
  let tmTy := mkApp (mkConst ``Tm) (toTypeExpr X)
  let ety := mkApp2 (mkConst ``Prod [.zero, .zero]) tmTy (mkConst ``Bool)
  mkApp2 (mkConst ``Map.mk) (toTypeExpr X) (listE ety (m.ent.map fun (t, b) =>
    mkApp4 (mkConst ``Prod.mk [.zero, .zero]) tmTy (mkConst ``Bool) (tmE t) (toExpr b)))

end LeanVM.Guest.Ref.Elab
