/-
  LeanVM.Guest.Source

  The zkDSL source AST of a program after placeholder substitution, as the Rust parser builds it
  (`crates/zkdsl_compiler/src/ast.rs`), and the syntactic passes the compiler runs on it before
  lowering: substitution, free variables, the inline-safety test.
-/

module

public import Init

/-!
# The zkDSL source AST

A transcription of `crates/zkdsl_compiler/src/ast.rs`: what
`zkdsl_compiler::parse_with_replacements` returns. Placeholders and scalar global constants are
already substituted textually, `match` arms are already expanded per integer, and `x OP= e` is
already `x = x OP (e)`; constant arrays stay named (`Program.constArrays`). A keyword argument
`key=value` is the call `__kw_key(value)`, as the parser writes it. The guest's AST is generated data
(`LeanVM.Guest.Data.Source`), not trusted: a parser bug can only make a later proof fail.

The passes below are those of `ast.rs`, `parser/subst.rs` and `parser/consts.rs`, used by the
expansion (`LeanVM.Guest.Expand`): `Stmt.substList` (`subst_stmts`), `Expr.constInt`
(`const_int_expr`), `freeVarsStmt` (`free_vars_stmt`), `bindsAnywhere`, `containsReturn` and
`splitTailReturn` (`split_tail_return`).
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
  /-- `[body for var in unroll(lo, hi)]`: the list of `body` at each integer `var` of `lo..hi`,
  only a `keccak_cells` argument (`ListComp`). `var` is bound in `body`. -/
  | listComp (body : Expr) (var : String) (lo hi : Expr)
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
two limbs of a word. -/
structure Program where
  funcs : List Func
  constArrays : List (String × List (Nat × Nat))
  deriving Repr, Inhabited

/-! ## Substitution (`parser/subst.rs`) -/

/-- `e` with `var x` replaced by `r` (`subst_var`); not under a list comprehension binding `x`. -/
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
  | .listComp body v lo hi, x, r =>
      .listComp (if v == x then body else body.subst x r) v (lo.subst x r) (hi.subst x r)
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

/-- `substitute_body`: the substitutions in order. The compiler makes them in one pass
(`subst_all`), the same since a `Const` call substitutes literals, which name no variable. -/
def substBody (body : List Stmt) (substs : List (String × Expr)) : List Stmt :=
  substs.foldl (fun b (x, r) => Stmt.substList x r b) body

/-! ## Parse-time integers (`parser/consts.rs`) -/

/-- `checked_pow` on `u128`. -/
def checkedPow128 (b e : Nat) : Option Nat :=
  if b ≤ 1 then some (b ^ e) else if 128 ≤ e then none
  else if b ^ e < 2 ^ 128 then some (b ^ e) else none

mutual
/-- `const_int_expr`: the value of an integer expression over literals, each operation checked in
`u128`; `none` when a leaf is no literal. -/
def Expr.constInt : Expr → Option Nat
  | .lit k => some k
  | .call f args => if f == "const" then Expr.constIntArg args else none
  | .add a b =>
      match a.constInt, b.constInt with
      | some x, some y => if x + y < 2 ^ 128 then some (x + y) else none
      | _, _ => none
  | .sub a b =>
      match a.constInt, b.constInt with
      | some x, some y => if y ≤ x then some (x - y) else none
      | _, _ => none
  | .mul a b =>
      match a.constInt, b.constInt with
      | some x, some y => if x * y < 2 ^ 128 then some (x * y) else none
      | _, _ => none
  | .div a b | .fdiv a b =>
      match a.constInt, b.constInt with
      | some x, some y => if y = 0 then none else some (x / y)
      | _, _ => none
  | .mod a b =>
      match a.constInt, b.constInt with
      | some x, some y => if y = 0 then none else some (x % y)
      | _, _ => none
  | .pow a b =>
      match a.constInt, b.constInt with
      | some x, some y => if y < 2 ^ 32 then checkedPow128 x y else none
      | _, _ => none
  | _ => none

/-- The one argument of a `const(...)`. -/
def Expr.constIntArg : List Expr → Option Nat
  | [e] => e.constInt
  | _ => none
end

/-! ## Free variables (`ast.rs`) -/

mutual
/-- `binds_through`: whether a statement binds `name` where the binding may outlive its block, at
its own level, in an `if` arm or in an `unroll` body. -/
def Stmt.bindsThrough (name : String) : Stmt → Bool
  | .mk _ k => StmtKind.bindsThrough name k

/-- `binds_through` on a kind. -/
def StmtKind.bindsThrough (name : String) : StmtKind → Bool
  | .let_ n _ | .letHintWitness n _ => n == name
  | .letTuple ns _ _ => ns.contains name
  | .match_ targets _ _ => targets.any fun
      | .var n => n == name
      | _ => false
  | .ite _ _ _ thn els _ => Stmt.bindsThroughList name thn || Stmt.bindsThroughList name els
  | .unroll _ _ _ body => Stmt.bindsThroughList name body
  | _ => false

/-- `binds_through` over a block. -/
def Stmt.bindsThroughList (name : String) : List Stmt → Bool
  | [] => false
  | s :: ss => Stmt.bindsThrough name s || Stmt.bindsThroughList name ss
end

mutual
/-- The variable references of `e`, in source order, appended to `acc` (`free_vars_expr`). -/
def Expr.freeVars : Expr → List String → List String
  | .var v, acc => acc ++ [v]
  | .add a b, acc | .mul a b, acc | .sub a b, acc | .div a b, acc | .fdiv a b, acc
  | .mod a b, acc | .index a b, acc | .pow a b, acc => b.freeVars (a.freeVars acc)
  | .slice a lo hi, acc => hi.freeVars (lo.freeVars (a.freeVars acc))
  | .call _ args, acc | .list args, acc => Expr.freeVarsList args acc
  | .listComp body v lo hi, acc =>
      hi.freeVars (lo.freeVars (acc ++ (body.freeVars []).filter (· != v)))
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

/-- `taken_arm`: which arm of an `if` that folds as written runs, when literals on both sides
decide it. -/
def takenArm (eq : Bool) (lhs rhs : Expr) (forceConst : Bool) : Option Bool :=
  if !forceConst && !bothLits lhs rhs then none
  else
    match lhs.constInt, rhs.constInt with
    | some a, some b => some ((a == b) == eq)
    | _, _ => none

/-- `empty_unroll`: whether literals say an `unroll` runs no copy of its body. -/
def emptyUnroll (lo hi : Expr) : Bool :=
  match lo.constInt, hi.constInt with
  | some a, some b => decide (b ≤ a)
  | _, _ => false

mutual
/-- `free_vars_stmt`: the references of a statement appended to `refs`, and the names it binds
added to the scoped set `bound`. With `live`, a block that never runs is left out, as in
`Stmt.binds`. -/
def Stmt.freeVars (live : Bool) : Stmt → List String × List String → List String × List String
  | .mk _ k, st => StmtKind.freeVars live k st

/-- `free_vars_stmt` on a kind. -/
def StmtKind.freeVars (live : Bool) :
    StmtKind → List String × List String → List String × List String
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
  | .ite eq lhs rhs thn els fc, (refs, bound) =>
      let refs := rhs.freeVars (lhs.freeVars refs)
      if fc || bothLits lhs rhs then
        let taken := if live then takenArm eq lhs rhs fc else none
        let st := if taken == some false then (refs, bound) else Stmt.freeVarsList live thn (refs, bound)
        if taken == some true then st else Stmt.freeVarsList live els st
      else
        let refs := (Stmt.freeVarsList live thn (refs, [])).1
        let refs := (Stmt.freeVarsList live els (refs, [])).1
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
      ((Stmt.freeVarsList live body (refs, [])).1, bound)
  | .unroll v lo hi body, (refs, bound) =>
      let refs := hi.freeVars (lo.freeVars refs)
      if live && emptyUnroll lo hi then (refs, bound)
      else
        -- The counter is bound inside the body only, so unless the body rebinds it, a read of the
        -- name after the loop is the enclosing one.
        let fresh := !bound.contains v
        let (refs, bound) := Stmt.freeVarsList live body (refs, v :: bound)
        if fresh && !Stmt.bindsThroughList v body then (refs, bound.filter (· != v)) else (refs, bound)

/-- `free_vars_stmt` over a block, sharing `bound`. -/
def Stmt.freeVarsList (live : Bool) :
    List Stmt → List String × List String → List String × List String
  | [], st => st
  | s :: ss, st => Stmt.freeVarsList live ss (Stmt.freeVars live s st)
end

mutual
/-- `binds_anywhere`: every name a statement binds, ignoring scope. With `live`, a block that
never runs is left out: the other arm of a compile-time `if`, an `unroll` over nothing. -/
def Stmt.binds (live : Bool) : Stmt → List String
  | .mk _ k => StmtKind.binds live k

/-- `binds_anywhere` on a kind. -/
def StmtKind.binds (live : Bool) : StmtKind → List String
  | .let_ n _ | .letHintWitness n _ => [n]
  | .letTuple ns _ _ => ns
  | .match_ targets _ _ => targets.filterMap fun
      | .var n => some n
      | _ => none
  | .ite eq lhs rhs thn els fc =>
      let taken := if live then takenArm eq lhs rhs fc else none
      (if taken == some false then [] else Stmt.bindsList live thn) ++
        (if taken == some true then [] else Stmt.bindsList live els)
  | .for_ v _ _ body => v :: Stmt.bindsList live body
  | .unroll v lo hi body =>
      if live && emptyUnroll lo hi then [] else v :: Stmt.bindsList live body
  | _ => []

/-- `binds_anywhere` over a block. -/
def Stmt.bindsList (live : Bool) : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.binds live s ++ Stmt.bindsList live ss
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
  | .assertNe .. | .assertLt .. | .call .. | .letTuple .. | .match_ .. => true
  | .ite _ _ _ thn els _ => Stmt.inlineSafeList thn && Stmt.inlineSafeList els
  | .unroll _ _ _ body => Stmt.inlineSafeList body
  | _ => false

/-- `stmt_inline_safe` over a block. -/
def Stmt.inlineSafeList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.inlineSafe s && Stmt.inlineSafeList ss
end

/-- `split_tail_return`: an inlinable body split at its single tail return, the statements before
it, each inline-safe, and the return's values. -/
def splitTailReturn (body : List Stmt) : Option (List Stmt × List Expr) :=
  match body.getLast? with
  | some (.mk _ (.ret es)) => if Stmt.inlineSafeList body.dropLast then some (body.dropLast, es) else none
  | _ => none

end
end LeanVM.Guest.Source
