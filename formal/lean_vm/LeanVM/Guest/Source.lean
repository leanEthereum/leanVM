/-
  LeanVM.Guest.Source

  The zkDSL source AST of a program after placeholder substitution, as the Rust parser builds it
  (`crates/lean_compiler/src/ast.rs`), and the syntactic passes the compiler runs on it before
  lowering: substitution, free variables, the inline-safety test.
-/

module

public import Init

/-!
# The zkDSL source AST

A transcription of `crates/lean_compiler/src/ast.rs`: what `lean_compiler::parse_with_replacements`
returns. Placeholders and scalar global constants are already substituted textually, `match`
arms are already expanded per integer, and `x OP= e` is already `x = x OP (e)`; constant arrays
stay named (`Program.constArrays`). A keyword argument `key=value` is the call
`__kw_key(value)`, as the parser writes it. The guest's AST is generated data
(`LeanVM.Guest.Data.Source`), not trusted: a parser bug can only make a later proof fail.

The passes below are those of `ast.rs` and `parser/subst.rs`, used by the expansion
(`LeanVM.Guest.Expand`): `Stmt.substList` (`subst_stmts`), `freeVarsStmt` (`free_vars_stmt`),
`bindsAnywhere`, `containsReturn` and `inlineSafe` (`body_inlinable`).
-/

namespace LeanVM.Guest.Source

@[expose] public section

/-- An expression (`ast.rs`, `Expr`). Integer literals are the raw 128-bit patterns of the
source; arithmetic means integer or field arithmetic by position, decided at expansion. -/
inductive Expr where
  /-- An integer literal, below `2^128`. -/
  | lit (n : Nat)
  /-- `GEN`. -/
  | gen
  /-- The constant `g^k`, folded by the parser from `GEN ** k`. -/
  | gpow (k : Nat)
  /-- `GEN ** e` with `e` not a parse-time integer. -/
  | genPow (e : Expr)
  /-- `b ** e`, a non-`GEN` base. -/
  | pow (b e : Expr)
  /-- A name. -/
  | var (x : String)
  /-- `a + b`. -/
  | add (a b : Expr)
  /-- `a * b`. -/
  | mul (a b : Expr)
  /-- `a - b`, compile-time only. -/
  | sub (a b : Expr)
  /-- `a // b`, compile-time only. -/
  | div (a b : Expr)
  /-- `a % b`, compile-time only. -/
  | mod (a b : Expr)
  /-- `a / b`, runtime field division. -/
  | fdiv (a b : Expr)
  /-- A call, of a function or a builtin. -/
  | call (f : String) (args : List Expr)
  /-- `HeapBuf(n)`, a parse-time size. -/
  | heapBuf (n : Nat)
  /-- `HeapBuf(e)`, a size carried in the exponent. -/
  | heapBufDyn (e : Expr)
  /-- `StackBuf(n)`. -/
  | stackBuf (n : Nat)
  /-- `a[i]`. -/
  | index (a i : Expr)
  /-- `a[lo:hi]`. -/
  | slice (a lo hi : Expr)
  /-- `[a, b, ...]`. -/
  | list (es : List Expr)
  deriving Repr, Inhabited, BEq

/-- A range-check bound (`LtBound`): a compile-time exponent, or a runtime `g^n`. -/
inductive LtBound where
  | const (k : Nat)
  | runtime (e : Expr)
  deriving Repr, Inhabited

/-- A `mul_range` stop (`ForBound`): a compile-time exponent, or a runtime g-power. -/
inductive ForBound where
  | const (k : Nat)
  | runtime (e : Expr)
  deriving Repr, Inhabited

mutual
/-- A statement and its source line (`Stmt`). -/
inductive Stmt where
  | mk (line : Nat) (kind : StmtKind)

/-- What a statement does (`StmtKind`). -/
inductive StmtKind where
  /-- `x = e`. -/
  | let_ (x : String) (e : Expr)
  /-- `x, y = f(args)`. -/
  | letTuple (xs : List String) (f : String) (args : List Expr)
  /-- `assert a == b`. -/
  | assertEq (a b : Expr)
  /-- `assert a != b`. -/
  | assertNe (a b : Expr)
  /-- `assert log e < bound`. -/
  | assertLt (e : Expr) (bound : LtBound)
  /-- `f(args)` as a statement. -/
  | call (f : String) (args : List Expr)
  /-- `hint_witness(dest, "stream")`. -/
  | hintWitness (dest : Expr) (stream : String)
  /-- `x = hint_witness("stream")`. -/
  | letHintWitness (x stream : String)
  /-- `print("label", value)`. -/
  | print (label : String) (value : Expr)
  /-- `if lhs == rhs` (`eq`) or `if lhs != rhs`, `if const(...)` when `forceConst`. -/
  | ite (eq : Bool) (lhs rhs : Expr) (thn els : List Stmt) (forceConst : Bool)
  /-- `targets = match(log(x), ...)`, one arm expression per integer. -/
  | match_ (targets : List Expr) (x : Expr) (arms : List Expr)
  /-- `arr[idx] = val`. -/
  | store (arr idx val : Expr)
  /-- `for var in mul_range(GEN ** lo, hi)`. -/
  | for_ (var : String) (lo : Nat) (hi : ForBound) (body : List Stmt)
  /-- `for var in unroll(lo, hi)`. -/
  | unroll (var : String) (lo hi : Expr) (body : List Stmt)
  /-- `return es`. -/
  | ret (es : List Expr)
  /-- Internal, from loop lowering: `if a != b: f(args)`. -/
  | callIfNe (a b : Expr) (f : String) (args : List Expr)
end

deriving instance Repr for Stmt, StmtKind

instance : Inhabited StmtKind := ⟨.ret []⟩
instance : Inhabited Stmt := ⟨.mk 0 default⟩

/-- The line of a statement. -/
def Stmt.line : Stmt → Nat
  | .mk l _ => l

/-- The kind of a statement. -/
def Stmt.kind : Stmt → StmtKind
  | .mk _ k => k

/-- The compile-time shape of a runtime value (`Shape`). -/
inductive Shape where
  | scalar
  | stackBuf (n : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The number of frame cells a shape occupies. -/
def Shape.cells : Shape → Nat
  | .scalar => 1
  | .stackBuf n => n

/-- A parameter's calling convention (`ParamKind`). -/
inductive ParamKind where
  | const
  | runtime (s : Shape)
  deriving Repr, Inhabited, DecidableEq

/-- A parameter. -/
structure Param where
  name : String
  kind : ParamKind
  deriving Repr, Inhabited

/-- The shape of a parameter, a `Const` one counting as a scalar (`Param::shape`). -/
def Param.shape (p : Param) : Shape :=
  match p.kind with
  | .const => .scalar
  | .runtime s => s

/-- A function definition (`Func`). -/
structure Func where
  name : String
  params : List Param
  /-- The inferred shape of each returned value. -/
  returnShapes : List Shape
  body : List Stmt
  /-- `@inline`. -/
  inline : Bool
  deriving Repr, Inhabited

/-- Whether a function is a `Const` template. -/
def Func.hasConstParams (f : Func) : Bool :=
  f.params.any fun p => p.kind == .const

/-- A whole program (`Ast`): the functions, and the constant arrays by name, each element the
three limbs of a word. -/
structure Program where
  funcs : List Func
  constArrays : List (String × List (Nat × Nat × Nat))
  deriving Repr, Inhabited

/-! ## Substitution (`parser/subst.rs`) -/

/-- `e` with `var x` replaced by `r` (`subst_var`). -/
def Expr.subst : Expr → String → Expr → Expr
  | .var y, x, r => if y == x then r else .var y
  | .add a b, x, r => .add (a.subst x r) (b.subst x r)
  | .mul a b, x, r => .mul (a.subst x r) (b.subst x r)
  | .sub a b, x, r => .sub (a.subst x r) (b.subst x r)
  | .div a b, x, r => .div (a.subst x r) (b.subst x r)
  | .fdiv a b, x, r => .fdiv (a.subst x r) (b.subst x r)
  | .mod a b, x, r => .mod (a.subst x r) (b.subst x r)
  | .index a b, x, r => .index (a.subst x r) (b.subst x r)
  | .slice a lo hi, x, r => .slice (a.subst x r) (lo.subst x r) (hi.subst x r)
  | .genPow e, x, r => .genPow (e.subst x r)
  | .pow a b, x, r => .pow (a.subst x r) (b.subst x r)
  | .heapBufDyn e, x, r => .heapBufDyn (e.subst x r)
  | .list es, x, r => .list (es.map (·.subst x r))
  | .call f args, x, r => .call f (args.map (·.subst x r))
  | e, _, _ => e

/-- A `LtBound` under substitution. -/
def LtBound.subst (x : String) (r : Expr) : LtBound → LtBound
  | .const k => .const k
  | .runtime e => .runtime (e.subst x r)

/-- A `ForBound` under substitution. -/
def ForBound.subst (x : String) (r : Expr) : ForBound → ForBound
  | .const k => .const k
  | .runtime e => .runtime (e.subst x r)

/-- Whether a `match` target is a name. -/
def Expr.isVar : Expr → Bool
  | .var _ => true
  | _ => false

/-- Whether a `match` target is the name `x`. -/
def Expr.isVarNamed (x : String) : Expr → Bool
  | .var y => y == x
  | _ => false

mutual
/-- One statement under substitution, and whether it rebinds the name (`subst_kind`). -/
def Stmt.subst1 (x : String) (r : Expr) : Stmt → Stmt × Bool
  | .mk l k => let (k', b) := StmtKind.subst1 x r k; (.mk l k', b)

/-- `subst_kind`. -/
def StmtKind.subst1 (x : String) (r : Expr) : StmtKind → StmtKind × Bool
  | .let_ n e => (.let_ n (e.subst x r), n == x)
  | .letTuple ns f args => (.letTuple ns f (args.map (·.subst x r)), ns.contains x)
  | .assertEq a b => (.assertEq (a.subst x r) (b.subst x r), false)
  | .assertNe a b => (.assertNe (a.subst x r) (b.subst x r), false)
  | .assertLt a bd => (.assertLt (a.subst x r) (bd.subst x r), false)
  | .call f args => (.call f (args.map (·.subst x r)), false)
  | .print l v => (.print l (v.subst x r), false)
  | .letHintWitness n s => (.letHintWitness n s, n == x)
  | .hintWitness d s => (.hintWitness (d.subst x r) s, false)
  | .store a i v => (.store (a.subst x r) (i.subst x r) (v.subst x r), false)
  | .ret es => (.ret (es.map (·.subst x r)), false)
  | .callIfNe a b f args =>
      (.callIfNe (a.subst x r) (b.subst x r) f (args.map (·.subst x r)), false)
  | .for_ v lo hi body =>
      (.for_ v lo (hi.subst x r) (if v == x then body else Stmt.substList x r body), false)
  | .unroll v lo hi body =>
      (.unroll v (lo.subst x r) (hi.subst x r) (if v == x then body else Stmt.substList x r body),
        false)
  | .ite eq lhs rhs thn els fc =>
      (.ite eq (lhs.subst x r) (rhs.subst x r) (Stmt.substList x r thn) (Stmt.substList x r els) fc,
        false)
  | .match_ targets e arms =>
      (.match_ (targets.map fun t => if t.isVar then t else t.subst x r) (e.subst x r)
        (arms.map (·.subst x r)), targets.any (Expr.isVarNamed x))

/-- `subst_stmts`: substitute through a block, stopping after a statement that rebinds the
name. -/
def Stmt.substList (x : String) (r : Expr) : List Stmt → List Stmt
  | [] => []
  | s :: ss =>
      let (s', rebinds) := Stmt.subst1 x r s
      s' :: (if rebinds then ss else Stmt.substList x r ss)
end

/-- `substitute_body`: the substitutions in order. -/
def substBody (body : List Stmt) (substs : List (String × Expr)) : List Stmt :=
  substs.foldl (fun b (x, r) => Stmt.substList x r b) body

/-! ## Free variables (`ast.rs`) -/

mutual
/-- The variable references of `e`, in source order, appended to `acc` (`free_vars_expr`). -/
def Expr.freeVars : Expr → List String → List String
  | .var v, acc => acc ++ [v]
  | .add a b, acc | .mul a b, acc | .sub a b, acc | .div a b, acc | .fdiv a b, acc
  | .mod a b, acc | .index a b, acc | .pow a b, acc => b.freeVars (a.freeVars acc)
  | .slice a lo hi, acc => hi.freeVars (lo.freeVars (a.freeVars acc))
  | .call _ args, acc | .list args, acc => Expr.freeVarsList args acc
  | .heapBufDyn e, acc | .genPow e, acc => e.freeVars acc
  | _, acc => acc

/-- The references of a list of expressions, in order. -/
def Expr.freeVarsList : List Expr → List String → List String
  | [], acc => acc
  | e :: es, acc => Expr.freeVarsList es (e.freeVars acc)
end

/-- Both sides literals: the syntactic half of a folded `if`. -/
def bothLits : Expr → Expr → Bool
  | .lit _, .lit _ => true
  | _, _ => false

mutual
/-- `free_vars_stmt`: the references of a statement appended to `refs`, and the names it binds
added to the scoped set `bound`. -/
def Stmt.freeVars : Stmt → List String × List String → List String × List String
  | .mk _ k, st => StmtKind.freeVars k st

/-- `free_vars_stmt` on a kind. -/
def StmtKind.freeVars : StmtKind → List String × List String → List String × List String
  | .let_ n e, (refs, bound) => (e.freeVars refs, n :: bound)
  | .letTuple ns _ args, (refs, bound) => (Expr.freeVarsList args refs, ns ++ bound)
  | .assertEq a b, (refs, bound) | .assertNe a b, (refs, bound) =>
      (b.freeVars (a.freeVars refs), bound)
  | .assertLt e bd, (refs, bound) =>
      let refs := e.freeVars refs
      match bd with
      | .runtime b => (b.freeVars refs, bound)
      | .const _ => (refs, bound)
  | .hintWitness d _, (refs, bound) => (d.freeVars refs, bound)
  | .letHintWitness n _, (refs, bound) => (refs, n :: bound)
  | .print _ v, (refs, bound) => (v.freeVars refs, bound)
  | .ite _ lhs rhs thn els fc, (refs, bound) =>
      let refs := rhs.freeVars (lhs.freeVars refs)
      if fc || bothLits lhs rhs then
        Stmt.freeVarsList els (Stmt.freeVarsList thn (refs, bound))
      else
        let refs := (Stmt.freeVarsList thn (refs, [])).1
        let refs := (Stmt.freeVarsList els (refs, [])).1
        (refs, bound)
  | .match_ targets x arms, (refs, bound) =>
      let refs := Expr.freeVarsList arms (x.freeVars refs)
      targets.foldl (fun (refs, bound) t =>
        match t with
        | .var n => (refs, n :: bound)
        | other => (other.freeVars refs, bound)) (refs, bound)
  | .callIfNe a b _ args, (refs, bound) =>
      (Expr.freeVarsList args (b.freeVars (a.freeVars refs)), bound)
  | .call _ args, (refs, bound) => (Expr.freeVarsList args refs, bound)
  | .store a i v, (refs, bound) => (v.freeVars (i.freeVars (a.freeVars refs)), bound)
  | .ret es, (refs, bound) => (Expr.freeVarsList es refs, bound)
  | .for_ _ _ hi body, (refs, bound) =>
      let refs := match hi with
        | .runtime b => b.freeVars refs
        | .const _ => refs
      ((Stmt.freeVarsList body (refs, [])).1, bound)
  | .unroll v lo hi body, (refs, bound) =>
      Stmt.freeVarsList body (hi.freeVars (lo.freeVars refs), v :: bound)

/-- `free_vars_stmt` over a block, sharing `bound`. -/
def Stmt.freeVarsList : List Stmt → List String × List String → List String × List String
  | [], st => st
  | s :: ss, st => Stmt.freeVarsList ss (Stmt.freeVars s st)
end

mutual
/-- `binds_anywhere`: every name a statement binds, ignoring scope. -/
def Stmt.binds : Stmt → List String
  | .mk _ k => StmtKind.binds k

/-- `binds_anywhere` on a kind. -/
def StmtKind.binds : StmtKind → List String
  | .let_ n _ | .letHintWitness n _ => [n]
  | .letTuple ns _ _ => ns
  | .match_ targets _ _ => targets.filterMap fun
      | .var n => some n
      | _ => none
  | .ite _ _ _ thn els _ => Stmt.bindsList thn ++ Stmt.bindsList els
  | .for_ v _ _ body | .unroll v _ _ body => v :: Stmt.bindsList body
  | _ => []

/-- `binds_anywhere` over a block. -/
def Stmt.bindsList : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.binds s ++ Stmt.bindsList ss
end

mutual
/-- `contains_return`. -/
def Stmt.hasRet : Stmt → Bool
  | .mk _ k => StmtKind.hasRet k

/-- `contains_return` on a kind. -/
def StmtKind.hasRet : StmtKind → Bool
  | .ret _ => true
  | .ite _ _ _ thn els _ => Stmt.hasRetList thn || Stmt.hasRetList els
  | .for_ _ _ _ body | .unroll _ _ _ body => Stmt.hasRetList body
  | _ => false

/-- `contains_return` over a block. -/
def Stmt.hasRetList : List Stmt → Bool
  | [] => false
  | s :: ss => Stmt.hasRet s || Stmt.hasRetList ss
end

mutual
/-- `stmt_inline_safe`: what an `@inline` body may hold before its tail return. -/
def Stmt.inlineSafe : Stmt → Bool
  | .mk _ k => StmtKind.inlineSafe k

/-- `stmt_inline_safe` on a kind. -/
def StmtKind.inlineSafe : StmtKind → Bool
  | .let_ .. | .store .. | .hintWitness .. | .letHintWitness .. | .print .. | .assertEq ..
  | .assertNe .. | .assertLt .. | .call .. => true
  | .ite _ _ _ thn els _ => Stmt.inlineSafeList thn && Stmt.inlineSafeList els
  | .unroll _ _ _ body => Stmt.inlineSafeList body
  | _ => false

/-- `stmt_inline_safe` over a block. -/
def Stmt.inlineSafeList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.inlineSafe s && Stmt.inlineSafeList ss
end

/-- `body_inlinable`: one tail return, preceded by inline-safe statements. -/
def bodyInlinable (body : List Stmt) : Bool :=
  match body.getLast? with
  | some (.mk _ (.ret _)) => Stmt.inlineSafeList body.dropLast
  | _ => false

end
end LeanVM.Guest.Source
