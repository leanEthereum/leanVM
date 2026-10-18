/-
  LeanVM.Guest.Expand

  The zkDSL front end in Lean: a source function and its `Const` arguments to the core IR function
  the compiler lowers, by the compiler's own rules (`crates/lean_compiler/src/lower.rs` and
  `lower/*.rs`).
-/

module

public import LeanVM.Guest.Source
public import LeanVM.Guest.Core

/-!
# Expansion

`expandFn` lowers one source function to its core function, as `lower_func` lowers it to
bytecode, and `expandProgram` runs the compiler's queue (`lib.rs`, `compile`): `main`, then the
other functions in source order, then every `Const` specialization and `mul_range` helper in the
order lowering asks for them. Every decision the compiler makes on the source is made here the
same way, from the same readings:

* compile-time evaluation (`eval`, `lower/eval.rs`): an expression's integer reading (`u128`,
  checked), its field reading (`+` is `XOR`), and the address `cell·g^k` it denotes; `const(...)`
  reads its operators as integers and rejects a leaf whose two readings differ;
* virtual bindings: a g-power, a shifted pointer and a field constant bind no value, and fold into
  the `DEREF` offset or a `SET` where used (`FOLD_MAX`, the identities `x + 0`, `x · 1`);
* `Const` specialization (`f__L3_G1`), `@inline` expansion in the caller's frame, `unroll` by
  substitution, folded `if` (bindings persist) and its rejection rule, runtime `if` (bindings
  revert), `match` with fused dispatch when every arm calls one function on the same runtime
  arguments, `mul_range` lifted to a tail-recursive helper `__loopN` taking its captured values;
* `StackBuf` runs, slices, list literals and `addr`, heap addressing, `blake2s` operands and
  metadata, and the hints.

What the compiler shares (pure results, pooled constants, repeated loads) is not shared here: a
second occurrence is a second atom with a fresh name, on the same relation. A value's name is its
position (`Core.Seg`): statement index, `unroll` counter, branch, arm, inline call site.

The loop counter `__loopN` is the compiler's: one counter over the whole compilation, advanced
in lowering order, which `expandProgram` reproduces and `expandFn` takes as `loopBase`.

Two places do not reproduce the compiler exactly; neither changes a relation. An `addr` pointer
is a value of its own (`Atom.frameAddr`), where the compiler folds the frame offset into it, so
the compiler's `FOLD_MAX` test on such a pointer counts that offset and this one does not; and a
hint left pending at the end of a branch gets the compiler's anchor (`SET 0`) when no atom
followed it, which may differ where the compiler's sharing emitted nothing.
-/

namespace LeanVM.Guest.Expand

open LeanVM.Parameters LeanVM.Guest.Source
open LeanVM.Guest.Core (V Seg Atom Hint Dest)

@[expose] public section

/-- The β-immediate cap (`FOLD_MAX`, `1 << MIN_LOG_MEM`). -/
def foldMax : Nat := 2 ^ 16

/-- An address the compiler tracks (`GAddr`): `base·g^exp`, the constant `g^exp` without a base;
`run` is the length of the frame run an `addr` pointer names. -/
structure GAddr where
  base : Option V
  exp : Nat
  run : Option Nat
  deriving Inhabited, Repr

/-- The compile-time readings of an expression (`Known`). -/
structure Known where
  int : Option Nat := none
  field : Option E := none
  addr : Option GAddr := none
  deriving Inhabited

/-- What a name is bound to (`Binding`). -/
inductive Binding where
  | scalar (v : V)
  | stack (cells : List V)
  | gaddr (g : GAddr)
  | fconst (c : E)
  deriving Inhabited

/-- A binding and its compile-time integer reading (`Bound`). -/
structure Bound where
  val : Binding
  int : Option Nat
  deriving Inhabited

/-- How an inlined return binds in the caller (`RetBind`). -/
inductive RetBind where
  | stack (cells : List V)
  | gaddr (g : GAddr)
  | scalar
  deriving Inhabited

/-- A run of consecutive cells (`CellRun`). -/
inductive CellRun where
  | stack (cells : List V)
  | heap (ptr : V) (lo len : Nat)
  deriving Inhabited

/-- The function being lowered, and the program. -/
structure Ctx where
  defs : List Func
  arrays : List (String × List (Nat × Nat × Nat))
  fnName : String
  isMain : Bool
  returnShapes : List Shape
  deriving Inhabited

/-- The lowering state. -/
structure St where
  ctx : Ctx
  /-- The scope: one entry per name. -/
  names : List (String × Bound)
  /-- The declared size of each `HeapBuf`, by its pointer. -/
  heapSizes : List (V × Nat)
  path : List Seg
  tag : Nat
  out : Array Core.Stmt
  /-- A hint emitted since the last instruction. -/
  pending : Bool
  inlineRet : Option (List V)
  inlineStackRet : Option (List RetBind)
  inlineCalls : List String
  /-- Every function queued so far, originals first. -/
  queue : Array Func
  loopCtr : Nat
  deriving Inhabited

/-- The lowering monad. -/
abbrev M := StateT St (Except String)

/-! ## State -/

/-- A compile error, naming the function. -/
def fail {α : Type} (msg : String) : M α := do
  throw s!"in {(← get).ctx.fnName}: {msg}"

/-- The context. -/
def ctx : M Ctx := return (← get).ctx

/-- A fresh value at the current position. -/
def fresh : M V := do
  let st ← get
  set { st with tag := st.tag + 1 }
  return ⟨st.path, st.tag, 0⟩

/-- `n` fresh consecutive cells (`alloc_stack`). -/
def freshRun (n : Nat) : M (List V) := do
  let st ← get
  set { st with tag := st.tag + 1 }
  return (List.range n).map fun k => ⟨st.path, st.tag, k⟩

/-- Emit a statement: it carries instructions, so a pending hint fires on it. -/
def emit (s : Core.Stmt) : M Unit :=
  modify fun st => { st with out := st.out.push s, pending := false }

/-- Emit an atom. -/
def emitAtom (a : Atom) : M Unit := emit (.atom a)

/-- Emit a hint, pending until the next instruction. -/
def emitHint (h : Hint) : M Unit :=
  modify fun st => { st with out := st.out.push (.atom (.hint h)), pending := true }

/-- Emit an `addr`, which is no instruction of its own. -/
def emitFrameAddr (p : V) (run : List V) : M Unit :=
  modify fun st => { st with out := st.out.push (.atom (.frameAddr p run)) }

/-- Run `m` at the position `seg` below the current one. -/
def withSeg {α : Type} (seg : Seg) (m : M α) : M α := do
  let st ← get
  let (p, t) := (st.path, st.tag)
  set { st with path := seg :: p, tag := 0 }
  let r ← m
  modify fun st => { st with path := p, tag := t }
  return r

/-- Run `m` emitting into a fresh block, and return the block and whether it ends with a hint
pending. -/
def capture {α : Type} (m : M α) : M (α × Bool × List Core.Stmt) := do
  let st ← get
  let (o, pd) := (st.out, st.pending)
  set { st with out := #[], pending := false }
  let r ← m
  let st ← get
  set { st with out := o, pending := pd }
  return (r, st.pending, st.out.toList)

/-- Emit captured blocks in order, as if they had run here. -/
def appendBlocks : List (Bool × List Core.Stmt) → M Unit
  | [] => pure ()
  | (pd, b) :: bs => do
      modify fun st => { st with out := st.out ++ b.toArray,
                                 pending := if b.isEmpty then st.pending else pd }
      appendBlocks bs

/-- The binding of a name. -/
def lookup (n : String) : M (Option Bound) := do
  return ((← get).names.find? (·.1 == n)).map (·.2)

/-- The run a name is bound to. -/
def stackOfName (n : String) : M (Option (List V)) := do
  match ← lookup n with
  | some ⟨.stack cells, _⟩ => return some cells
  | _ => return none

/-- The run `e` names, if it is a `StackBuf` name (`stack_of`). -/
def stackOf (e : Expr) : M (Option (List V)) :=
  match e with
  | .var v => stackOfName v
  | _ => return none

/-- Reject a constant array's name as a binding (`check_not_reserved`). -/
def checkNotReserved (n : String) : M Unit := do
  if ((← ctx).arrays.any (·.1 == n)) then
    fail s!"`{n}` is a top-level constant array, so the name is reserved"

/-- Bind a name, clearing its integer reading (`rebind`). -/
def rebind (n : String) (b : Binding) : M Unit := do
  checkNotReserved n
  modify fun st => { st with names := (n, ⟨b, none⟩) :: st.names.filter (·.1 != n) }

/-- Attach an integer reading to a name's binding (`set_int`). -/
def setInt (n : String) (k : Nat) : M Unit :=
  modify fun st => { st with names := st.names.map fun (m, b) =>
    if m == n then (m, { b with int := some k }) else (m, b) }

/-! ## Compile-time arithmetic -/

/-- A checked `u128` result. -/
def chk (n : Nat) : Option Nat := if n < u128Bound then some n else none

/-- `checked_pow` on `u128`. -/
def checkedPow (b e : Nat) : Option Nat :=
  if b ≤ 1 then some (b ^ e) else if 128 ≤ e then none else chk (b ^ e)

/-- `n.is_power_of_two() && n < 2^64`. -/
def isPow2Below64 (n : Nat) : Bool := n != 0 && n < u64Bound && n &&& (n - 1) == 0

/-- The exponent of a power of two. -/
def log2Nat (n : Nat) : Nat := Nat.log2 n

/-- The readings of `g^exp` (`gpow` in `eval`). -/
def gpowKnown (exp : Nat) : Known :=
  { field := some (gpowE exp), addr := some ⟨none, exp, none⟩ }

/-- The readings of an integer (`int` in `eval`). -/
def intKnown (n : Nat) : Known := { int := some n, field := some (litField n) }

/-- Both readings, when they disagree (`diverging_readings`). -/
def Known.diverging (k : Known) : Option (Nat × E) :=
  match k.int, k.field with
  | some n, some f => if f = litField n then none else some (n, f)
  | _, _ => none

/-- `a·b` on addresses (`gmul`). -/
def gmul (a b : GAddr) : Option GAddr :=
  let base := match a.base, b.base with
    | none, x => some x
    | x, none => some x
    | some _, some _ => none
  match base, chk (a.exp + b.exp) with
  | some base, some exp => some ⟨base, exp, a.run.or b.run⟩
  | _, _ => none

/-- A constant array element's word. -/
def arrayWord (c : Nat × Nat × Nat) : E := word c.1 c.2.1 c.2.2

/-! ## Evaluation (`lower/eval.rs`) -/

mutual
/-- Every compile-time reading of `e` (`eval`). -/
def eval : Nat → Expr → M Known
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    match e with
    | .lit k =>
        return { intKnown k with
          addr := if isPow2Below64 k then some ⟨none, log2Nat k, none⟩ else none }
    | .gen => return gpowKnown 1
    | .gpow k => return gpowKnown k
    | .genPow x => do
        match (← eval n x).int with
        | some k => if k < u32Bound then return gpowKnown k else return {}
        | none => return {}
    | .var v => do
        match ← lookup v with
        | none => return {}
        | some b =>
            match b.val with
            | .fconst c => return { int := b.int, field := some c }
            | .gaddr ga =>
                return { int := b.int, field := if ga.base.isNone then some (gpowE ga.exp) else none,
                         addr := some ga }
            | .scalar c => return { int := b.int, addr := some ⟨some c, 0, none⟩ }
            | .stack _ => return { int := b.int }
    | .add a b | .sub a b | .mul a b | .div a b | .mod a b => do
        let x ← eval n a
        let y ← eval n b
        let isDiv := match e with | .div .. | .mod .. => true | _ => false
        if isDiv && y.int == some 0 then
          match e with
          | .div .. => fail "compile-time division by zero"
          | _ => fail "compile-time modulo by zero"
        let int : Option Nat := match x.int, y.int with
          | some p, some q =>
              match e with
              | .add .. => chk (p + q)
              | .sub .. => if q ≤ p then some (p - q) else none
              | .mul .. => chk (p * q)
              | .div .. => some (p / q)
              | _ => some (p % q)
          | _, _ => none
        let field : Option E := match e, x.field, y.field with
          | .add .., some f, some g => some (f + g)
          | .mul .., some f, some g => some (f * g)
          | _, _, _ => none
        let addr : Option GAddr := match e, x.addr, y.addr with
          | .mul .., some p, some q => gmul p q
          | _, _, _ => none
        return { int, field, addr }
    | .pow b x => do
        let base ← eval n b
        let exp := (← eval n x).int.bind fun k => if k < u32Bound then some k else none
        return { int := base.int.bind fun p => exp.bind fun k => checkedPow p k,
                 field := base.field.bind fun f => exp.map fun k => fieldPow f k }
    | .index (.var v) idx => do
        match (← ctx).arrays.find? (·.1 == v) with
        | none => return {}
        | some (_, arr) =>
            match (← eval n idx).int with
            | none => return {}
            | some i =>
                if u32Bound ≤ i then return {} else
                match arr[i]? with
                | none => fail s!"const array `{v}` index {i} out of bounds (len {arr.length})"
                | some c =>
                    return { int := if c.2.2 = 0 then some (c.1 + c.2.1 * u64Bound) else none,
                             field := some (arrayWord c) }
    | .call "f192" [a, b, c] =>
        let limb : Expr → Option Nat := fun
          | .lit k => if k < u64Bound then some k else none
          | _ => none
        let f : Option E := do
          let x ← limb a
          let y ← limb b
          let z ← limb c
          pure (word x y z)
        return { field := f }
    | .call "const" [a] => do
        checkConstLeaves n a
        match (← eval n a).int with
        | some k => return intKnown k
        | none => return {}
    | .call "len" [.var v] => do
        match (← ctx).arrays.find? (·.1 == v) with
        | some (_, arr) => return intKnown arr.length
        | none => return {}
    | _ => return {}

/-- Reject a `const(...)` leaf whose two readings differ (`check_const_leaves`). -/
def checkConstLeaves : Nat → Expr → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    match e with
    | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .pow a b => do
        checkConstLeaves n a
        checkConstLeaves n b
    | .call "const" [a] => checkConstLeaves n a
    | leaf => do
        if let some (k, _) := (← eval n leaf).diverging then
          fail s!"const(...) cannot reinterpret a leaf that is the integer {k} and another value"
end

/-- The fuel of a compile-time evaluation: deeper than any expression. -/
def evalFuel : Nat := 10000

/-- `try_const_int`. -/
def tryConstInt (e : Expr) : M (Option Nat) := return (← eval evalFuel e).int

/-- `try_field_const`. -/
def tryFieldConst (e : Expr) : M (Option E) := return (← eval evalFuel e).field

/-- `gaddr_of`. -/
def gaddrOf (e : Expr) : M (Option GAddr) := return (← eval evalFuel e).addr

/-- `try_const_index`: an integer reading below `2^32`. -/
def tryConstIndex (e : Expr) : M (Option Nat) := do
  match ← tryConstInt e with
  | some k => return if k < u32Bound then some k else none
  | none => return none

/-- `const_index`: a compile-time index, required. -/
def constIndex (e : Expr) : M Nat := do
  match ← tryConstInt e with
  | none => fail "a StackBuf index must be a compile-time integer"
  | some k => if k < u32Bound then return k else fail s!"stack index {k} does not fit in u32"

/-- `gpow_exp`. -/
def gpowExp (e : Expr) : M Nat := do
  match ← tryConstIndex e with
  | some k => return k
  | none => fail "`GEN ** e` needs a compile-time integer exponent"

/-- `add_identity`: the other operand of a sum with a constant zero. -/
def addIdentity (a b : Expr) : M (Option Expr) := do
  if (← tryFieldConst a) == some 0 then return some b
  if (← tryFieldConst b) == some 0 then return some a
  return none

/-- `mul_identity`: the other operand of a product with a constant one. -/
def mulIdentity (a b : Expr) : M (Option Expr) := do
  if (← tryFieldConst a) == some 1 then return some b
  if (← tryFieldConst b) == some 1 then return some a
  return none

/-- `try_lit`: a literal, a literal-bound name, or `GEN ** 0`, below `2^64`. -/
def tryLit (e : Expr) : M (Option Nat) := do
  match e with
  | .lit k => return if k < u64Bound then some k else none
  | .var v => do
      let k := (← lookup v).bind (·.int)
      return k.bind fun k => if k < u64Bound then some k else none
  | .gpow 0 => return some 1
  | _ => return none

/-- `const_gpow`: the exponent of a constant g-power small enough for `β`. -/
def constGpow (e : Expr) : M (Option Nat) := do
  let k ← eval evalFuel e
  if let some ⟨none, exp, _⟩ := k.addr then
    if exp ≤ foldMax then return some exp
  match k.int with
  | none => return none
  | some n =>
      if !isPow2Below64 n then return none
      let j := log2Nat n
      match k.field with
      | none => return none
      | some f => return if j ≤ foldMax && f == gpowE j then some j else none

/-! ## Emission helpers -/

/-- A fresh value holding `c` (`const_cell`). -/
def constCell (c : E) : M V := do
  let o ← fresh
  emitAtom (.const o c)
  return o

/-- A pure `XOR` or `MUL` into a fresh value (`pure`). -/
def pureAdd (a b : V) : M V := do
  let o ← fresh
  emitAtom (.add o a b)
  return o

/-- `pure` for `MUL`. -/
def pureMul (a b : V) : M V := do
  let o ← fresh
  emitAtom (.mul o a b)
  return o

/-- `copy`. -/
def copy (src dst : V) : M Unit := emitAtom (.copy dst src)

/-- An anchor for a pending hint (`anchor`). -/
def anchor : M Unit := do
  let o ← fresh
  emitAtom (.const o 0)

/-- A value holding an address (`materialize`). -/
def materialize (ga : GAddr) : M V := do
  match ga.base, ga.exp with
  | some c, 0 => return c
  | base, exp => do
      let k ← constCell (gpowE exp)
      match base with
      | none => return k
      | some c => pureMul c k

/-- The frame cell `arr[idx]` names, if `arr` is a `StackBuf` (`frame_cell`). -/
def frameCell (arr idx : Expr) : M (Option V) := do
  match ← stackOf arr with
  | none => return none
  | some cells => do
      let k ← constIndex idx
      match cells[k]? with
      | some c => return some c
      | none => fail s!"index {k} out of bounds (StackBuf size {cells.length})"

/-- `addr(sb)` (`stack_addr`). -/
def stackAddr (args : List Expr) : M GAddr := do
  let [a] := args | fail "addr(buf) takes one StackBuf"
  match ← stackOf a with
  | none => fail "addr() names a frame run, so it takes a StackBuf"
  | some cells => do
      let p ← fresh
      emitFrameAddr p cells
      return ⟨some p, 0, some cells.length⟩

/-- The compile-time bounds check of a heap or `addr` access (`check_heap_bound`). -/
def checkHeapBound (arr : Expr) (extra span : Nat) : M Unit := do
  let some ga ← gaddrOf arr | return
  let (some base, some exp) := (ga.base, chk (ga.exp + extra)) | return
  if let some len := ga.run then
    if len < exp + span then fail s!"frame access {exp} out of bounds for the StackBuf({len}) named by `addr`"
    return
  match (← get).heapSizes.find? (·.1 == base) with
  | some (_, size) =>
      if size < exp + span then fail s!"heap index {exp} out of bounds (HeapBuf size {size})"
  | none => return

/-- `ret_targets`: the cell each `match` target names, and the names to bind. -/
def retTargets (targets : List Expr) : M (List V × List (String × V)) := do
  let nVars := (targets.filter Expr.isVar).length
  let run ← freshRun nVars
  let mut cells := #[]
  let mut binds := #[]
  let mut k := 0
  for t in targets do
    match t with
    | .index arr idx => do
        match ← frameCell arr idx with
        | some c => cells := cells.push c
        | none => fail "a multi-value target must be a name or a StackBuf element"
    | .var n => do
        let c := run[k]!
        k := k + 1
        cells := cells.push c
        binds := binds.push (n, c)
    | _ => fail "a multi-value target must be a name or a StackBuf element"
  return (cells.toList, binds.toList)

/-- Bind the targets of a `match` (`bind_targets`). -/
def bindTargets (binds : List (String × V)) : M Unit :=
  binds.forM fun (n, c) => rebind n (.scalar c)

/-- `ret_binding`. -/
def retBinding (b : Option RetBind) (dst : V) : Binding :=
  match b with
  | some (.stack cells) => .stack cells
  | some (.gaddr ga) => .gaddr ga
  | _ => .scalar dst

/-- The definition of a callee: an original, else a queued one (`callee_def`). -/
def calleeDef (c : String) : M (Option Func) := do
  let st ← get
  match st.ctx.defs.find? (·.name == c) with
  | some f => return some f
  | none => return st.queue.toList.find? (·.name == c)

/-- An original definition. -/
def origDef (c : String) : M (Option Func) := return (← ctx).defs.find? (·.name == c)

/-- The literal a `Const` argument substitutes (`const_arg`). -/
def constArg (a : Expr) : M (Option Expr) := do
  match a with
  | .lit k => return some (.lit k)
  | .gen => return some (.gpow 1)
  | .gpow k => return some (.gpow k)
  | other => return (← tryConstIndex other).map .lit

/-- The `Const` substitutions of a call (`const_substs`). -/
def constSubsts (def_ : Func) (args : List Expr) : M (Except String (List (String × Expr))) := do
  if args.length != def_.params.length then
    return .error s!"call to `{def_.name}`: wrong arity"
  let mut substs := #[]
  for (p, a) in def_.params.zip args do
    if p.kind == .const then
      match ← constArg a with
      | some c => substs := substs.push (p.name, c)
      | none => return .error s!"argument for Const parameter `{p.name}` of `{def_.name}` must be a compile-time constant"
  return .ok substs.toList

/-- The name of a specialization (`specialize`): `f_` then `_L{n}` or `_G{k}` per constant. -/
def specName (f : String) (substs : List (String × Expr)) : String :=
  substs.foldl (fun s (_, c) => match c with
    | .lit n => s ++ s!"_L{n}"
    | .gpow k => s ++ s!"_G{k}"
    | _ => s) (f ++ "_")

/-- Monomorphize a call to a `Const` template, queueing the specialization once
(`specialize`); the name and the runtime arguments. -/
def specialize (callee : String) (args : List Expr) : M (String × List Expr) := do
  let some def_ ← origDef callee | return (callee, args)
  if !def_.hasConstParams then return (callee, args)
  let substs ← match ← constSubsts def_ args with
    | .ok s => pure s
    | .error e => fail e
  let name := specName callee substs
  let runtime := (def_.params.zip args).filter fun (p, _) => p.kind != .const
  if !(← get).queue.any (·.name == name) then
    if 10000 ≤ (← get).queue.size then fail "Const specialization explosion"
    let spec : Func := { name := name, params := runtime.map (·.1), returnShapes := def_.returnShapes,
                         body := substBody def_.body substs, inline := false }
    modify fun st => { st with queue := st.queue.push spec }
  return (name, runtime.map (·.2))

/-- `plus_k`: `k` when `hi` is syntactically `lo + k`. -/
def plusK (lo hi : Expr) : Option Nat :=
  match hi with
  | .add a b =>
      let second := match b with
        | .lit k => if a == lo then some k else none
        | _ => none
      match a with
      | .lit k => if b == lo then some k else second
      | _ => second
  | _ => none

/-- The blake2s keyword arguments, `__kw_key(value)`. -/
def kwArg : Expr → Option (String × Expr)
  | .call f [v] => if f.startsWith "__kw_" then some (String.ofList (f.toList.drop 5), v) else none
  | _ => none

/-- Whether an argument is a keyword. -/
def isKw : Expr → Bool
  | .call f _ => f.startsWith "__kw_"
  | _ => false

/-- An expression-position use of an inlined return (`take_inline_ret_cell`). -/
def takeInlineRetCell (dst : V) : M V := do
  let b := (← get).inlineStackRet.bind (·.head?)
  modify fun st => { st with inlineStackRet := none }
  match b with
  | some (.gaddr ga) => materialize ga
  | some (.stack cells) =>
      match cells with
      | [c] => return c
      | _ => fail "a multi-cell StackBuf return needs a `let` binding"
  | _ => return dst

/-! ## Lowering -/

mutual
/-- A value holding `e` (`expr`). -/
def expr : Nat → Expr → M V
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    if let some v ← tryFieldConst e then return ← constCell v
    match e with
    | .lit _ | .gen | .gpow _ => fail "internal: a literal folds"
    | .genPow x => do
        let k ← gpowExp x
        constCell (gpowE k)
    | .pow b x => powExpr n b x
    | .var v => do
        match ← lookup v with
        | some ⟨.stack _, _⟩ => fail s!"StackBuf `{v}` used as a scalar"
        | some ⟨.gaddr ga, _⟩ => materialize ga
        | some ⟨.scalar o, _⟩ => return o
        | _ => fail s!"unbound variable `{v}`"
    | .add a b => do
        if let some x ← addIdentity a b then return ← expr n x
        let la ← expr n a
        let lb ← expr n b
        pureAdd la lb
    | .mul a b => do
        if let some x ← mulIdentity a b then return ← expr n x
        let la ← expr n a
        let lb ← expr n b
        pureMul la lb
    | .fdiv a b => do
        let la ← expr n a
        let lb ← expr n b
        let q ← fresh
        emitAtom (.mul la q lb)
        return q
    | .call "f192" _ => fail "f192 needs three literal u64 limbs"
    | .call "const" _ => fail "const(...) asks for a compile-time integer"
    | .call "addr" args => do
        let ga ← stackAddr args
        materialize ga
    | .call "hint_log2_ceil" args => do
        let [a0, a1, a2] := args | fail "hint_log2_ceil takes three arguments"
        let nbits ← constIndex a1
        let floor ← constIndex a2
        let bits ← bitsDest n a0 nbits
        let dst ← fresh
        emitHint (.log2Ceil bits nbits floor dst)
        return dst
    | .call f args => do
        let ds ← call n f args 1
        let some d := ds.head? | fail "internal: no return cell"
        takeInlineRetCell d
    | .heapBuf sz => do
        let arr ← fresh
        modify fun st => { st with heapSizes := (arr, sz) :: st.heapSizes }
        emitHint (.alloc arr sz)
        return arr
    | .heapBufDyn x => do
        let size ← expr n x
        let arr ← fresh
        emitHint (.allocDyn arr size)
        return arr
    | .stackBuf _ => fail "StackBuf(n) must be bound to a name"
    | .index arr idx => do
        if let some c ← frameCell arr idx then return c
        let (ptr, o2) ← heapAddr n arr idx
        let dst ← fresh
        emitAtom (.load dst ptr o2)
        return dst
    | .sub .. | .div .. | .mod .. => fail "`-`, `//`, `%` are compile-time only"
    | .slice .. => fail "a slice is not a scalar"
    | .list _ => fail "a list literal must be bound to a name"

/-- `b ** x`, a non-`GEN` base (`pow_expr`). -/
def powExpr : Nat → Expr → Expr → M V
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, b, x => do
    let some k ← tryConstIndex x | fail "`**` exponent must be a compile-time integer"
    if let some bc ← tryFieldConst b then return ← constCell (fieldPow bc k)
    if k = 0 then
      let o ← fresh
      emitAtom (.const o 1)
      return o
    let base ← expr n b
    let hi := Nat.log2 k
    let mut acc := base
    for i in (List.range hi).reverse do
      acc ← pureMul acc acc
      if (k / 2 ^ i) % 2 = 1 then
        acc ← pureMul acc base
    return acc

/-- Evaluate `e` into `dst` (`expr_into`). -/
def exprInto : Nat → Expr → V → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, e, dst => do
    if let some v ← tryFieldConst e then return ← emitAtom (.const dst v)
    match e with
    | .index arr idx => do
        match ← frameCell arr idx with
        | some c => copy c dst
        | none => do
            let (ptr, o2) ← heapAddr n arr idx
            emitAtom (.load dst ptr o2)
    | .pow b x => do
        let v ← powExpr n b x
        copy v dst
    | .add a b => do
        if let some x ← addIdentity a b then return ← exprInto n x dst
        let la ← expr n a
        let lb ← expr n b
        emitAtom (.add dst la lb)
    | .mul a b => do
        if let some x ← mulIdentity a b then return ← exprInto n x dst
        let la ← expr n a
        let lb ← expr n b
        emitAtom (.mul dst la lb)
    | .call f args => do
        modify fun st => { st with inlineStackRet := none }
        callInto n f args [dst]
        let v ← takeInlineRetCell dst
        if v != dst then copy v dst
    | _ => do
        let v ← expr n e
        copy v dst

/-- Address `arr[idx]` as a pointer and a `β` exponent (`heap_addr`). -/
def heapAddr : Nat → Expr → Expr → M (V × Nat)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, arr, idx => do
    let bareInt := match ← tryLit idx with
      | some k => k != 1
      | none => false
    let known ← eval evalFuel idx
    if (bareInt || known.addr.isNone) && known.field.isSome then
      fail "heap index is a plain integer or a constant that is no g-power: write `buf[GEN ** k]`"
    match known.addr with
    | some ⟨none, exp, _⟩ => return ← heapBase n arr exp
    | some ⟨some ib, exp, _⟩ => do
        if let some ga ← gaddrOf arr then
          if let (some ab, some total) := (ga.base, chk (ga.exp + exp)) then
            if total ≤ foldMax then
              let ptr ← pureMul ab ib
              return (ptr, total)
    | none => pure ()
    arrayPtr n arr idx

/-- Address `arr·g^extra` (`heap_base`). -/
def heapBase : Nat → Expr → Nat → M (V × Nat)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, arr, extra => do
    checkHeapBound arr extra 1
    if let some ga ← gaddrOf arr then
      if let (some base, some exp) := (ga.base, chk (ga.exp + extra)) then
        if exp ≤ foldMax then return (base, exp)
    let a ← expr n arr
    if extra = 0 then return (a, 0)
    let k ← constCell (gpowE extra)
    return (← pureMul a k, 0)

/-- A runtime heap index, a constant g-power factor folded into `β` (`array_ptr`). -/
def arrayPtr : Nat → Expr → Expr → M (V × Nat)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, arr, idx => do
    if let .mul a b := idx then
      if let some k ← constGpow a then
        let la ← expr n arr
        let lr ← expr n b
        return (← pureMul la lr, k)
      if let some k ← constGpow b then
        let la ← expr n arr
        let lr ← expr n a
        return (← pureMul la lr, k)
    let la ← expr n arr
    let li ← expr n idx
    return (← pureMul la li, 0)

/-- The run of cells `e` names (`cell_run`). -/
def cellRun : Nat → Expr → M CellRun
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    match e with
    | .var _ => do
        match ← stackOf e with
        | some cells => return .stack cells
        | none => fail "only a StackBuf names a run of cells unsliced"
    | .slice arr lo hi => do
        match ← tryConstIndex lo, ← tryConstIndex hi with
        | some l, some h => do
            if h ≤ l then fail s!"empty slice {l}:{h}"
            let len := h - l
            match ← stackOf arr with
            | some cells => do
                if cells.length < h then fail s!"slice {l}:{h} out of bounds (StackBuf size {cells.length})"
                return .stack ((cells.drop l).take len)
            | none => do
                checkHeapBound arr l len
                let (ptr, lo') ← heapBase n arr l
                return .heap ptr lo' len
        | _, _ => do
            if (← stackOf arr).isSome then fail "a StackBuf slice needs compile-time bounds"
            let some k := plusK lo hi | fail "a runtime slice must be `buf[i:i + k]`"
            if u32Bound ≤ k then fail s!"slice length {k} does not fit in u32"
            if k = 0 then fail "a runtime slice of length 0 names no cell"
            if let some ⟨none, exp, _⟩ ← gaddrOf lo then
              checkHeapBound arr exp k
            let (ptr, lo') ← heapAddr n arr lo
            return .heap ptr lo' k
    | _ => fail "expected a StackBuf, a StackBuf slice, or a HeapBuf slice"

/-- A computed-advice bit buffer (`bits_dest`). -/
def bitsDest : Nat → Expr → Nat → M Dest
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, e, nbits => do
    match ← stackOf e with
    | some cells => do
        if cells.length < nbits then fail s!"needs {nbits} cells, its StackBuf destination has {cells.length}"
        return .stack (cells.take nbits)
    | none => do
        checkHeapBound e 0 nbits
        return .heap (← expr n e) 0 nbits

/-- A call, its return cells allocated here (`call`). -/
def call : Nat → String → List Expr → Nat → M (List V)
  | 0, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, callee, args, nRet => do
    if callee == "blake2s" then fail "blake2s is a statement"
    modify fun st => { st with inlineStackRet := none }
    let d ← origDef callee
    if d.any (·.inline) then
      let dsts ← (List.range nRet).mapM fun _ => fresh
      callInto n callee args dsts
      return dsts
    if let some d := d then
      if d.returnShapes.length != nRet then
        fail s!"`{callee}` returns {d.returnShapes.length} values, call binds {nRet}"
    let mut logical := #[]
    let mut physical := #[]
    let mut binds := #[]
    for i in List.range nRet do
      match (d.bind (·.returnShapes[i]?)).getD .scalar with
      | .scalar => do
          let dst ← fresh
          logical := logical.push dst
          physical := physical.push dst
          binds := binds.push RetBind.scalar
      | .stackBuf size => do
          if size = 0 then fail "a returned StackBuf must not be empty"
          let run ← freshRun size
          logical := logical.push run[0]!
          physical := physical ++ run.toArray
          binds := binds.push (RetBind.stack run)
    lowerCall n callee args none physical.toList
    modify fun st => { st with inlineStackRet := some binds.toList }
    return logical.toList

/-- Evaluate a call into `dsts` (`call_into`). -/
def callInto : Nat → String → List Expr → List V → M Unit
  | 0, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, callee, args, dsts => do
    if callee == "blake2s" then fail "blake2s is a statement, not a value-returning call"
    if !(← tryInline n callee args dsts) then
      if let some d ← origDef callee then
        if d.returnShapes.length != dsts.length then
          fail s!"`{callee}` returns {d.returnShapes.length} values, call binds {dsts.length}"
        if d.returnShapes.any (· != .scalar) then
          fail "a normal function's multi-cell StackBuf return needs a `let` binding"
      lowerCall n callee args none dsts

/-- A real call (`lower_call`), conditional on `cond ≠ 0` when given. -/
def lowerCall : Nat → String → List Expr → Option V → List V → M Unit
  | 0, _, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, callee0, args0, cond, dsts => do
    match (← calleeDef callee0).map (·.params.length) with
    | some want => if want != args0.length then fail s!"`{callee0}` takes {want} arguments, got {args0.length}"
    | none => fail s!"no function named `{callee0}`"
    let (callee, args) ← specialize callee0 args0
    let shapes : List Shape := match ← calleeDef callee with
      | some f => f.params.map Param.shape
      | none => args.map fun _ => Shape.scalar
    let mut cells := #[]
    for (i, a) in (List.range args.length).zip args do
      match shapes[i]?.getD Shape.scalar with
      | Shape.stackBuf k => do
          let some run ← stackOf a | fail s!"`{callee}` parameter {i} is a StackBuf({k}); pass one"
          if run.length != k then fail s!"`{callee}` parameter {i} is a StackBuf({k}), got a StackBuf({run.length})"
          cells := cells ++ run.toArray
      | Shape.scalar => cells := cells.push (← expr n a)
    match cond with
    | some x => emit (.callIf x callee cells.toList)
    | none => emit (.call callee cells.toList dsts)

/-- Expand an `@inline` call in this frame (`try_inline`); `false` for another callee. -/
def tryInline : Nat → String → List Expr → List V → M Bool
  | 0, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, callee, args, dsts => do
    let some def_ := (← origDef callee).filter (·.inline) | return false
    let substs ← match ← constSubsts def_ args with
      | .ok s => pure s
      | .error _ => fail s!"`@inline {callee}`: bad arity or unresolved Const argument"
    let body := substBody def_.body substs
    if def_.returnShapes.length != dsts.length then
      fail s!"`@inline {callee}` returns {def_.returnShapes.length} values, call binds {dsts.length}"
    if !bodyInlinable body then
      fail s!"`@inline {callee}` requires one tail `return`, with no nested returns, tuple assignments, mul_range loops, or match"
    if (← get).inlineCalls.contains callee then
      fail s!"recursive @inline expansion is not supported: {callee}"
    let mut binds := #[]
    for (p, a) in def_.params.zip args do
      if p.kind == .const then continue
      match ← stackOf a with
      | some cells => binds := binds.push (p.name, Binding.stack cells)
      | none =>
          match ← gaddrOf a with
          | some ga => binds := binds.push (p.name, Binding.gaddr ga)
          | none => binds := binds.push (p.name, Binding.scalar (← expr n a))
    let saved := (← get).names
    modify fun st => { st with names := [] }
    for (p, b) in binds do
      checkNotReserved p
      modify fun st => { st with names := (p, ⟨b, none⟩) :: st.names.filter (·.1 != p) }
    let savedRet := (← get).inlineRet
    modify fun st => { st with inlineRet := some dsts, inlineCalls := callee :: st.inlineCalls }
    let site ← fresh
    withSeg (.i callee site.tag) (stmts n body)
    modify fun st => { st with inlineRet := savedRet, names := saved,
                               inlineCalls := st.inlineCalls.drop 1 }
    return true

/-- `return` (`lower_return`). -/
def lowerReturn : Nat → List Expr → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, es => do
    if let some dsts := (← get).inlineRet then
      modify fun st => { st with inlineRet := none }
      let mut binds := #[]
      for (e, d) in es.zip dsts do
        match ← stackOf e with
        | some cells => binds := binds.push (RetBind.stack cells)
        | none =>
            match ← gaddrOf e with
            | some ga => binds := binds.push (RetBind.gaddr ga)
            | none => do
                exprInto n e d
                binds := binds.push RetBind.scalar
      modify fun st => { st with inlineStackRet := some binds.toList }
      return
    let c ← ctx
    if c.isMain then return
    if es.length != c.returnShapes.length then
      fail s!"function returns {es.length} values here, but its ABI declares {c.returnShapes.length}"
    let rets ← freshRun (c.returnShapes.map Shape.cells).sum
    let mut pos := 0
    for (e, shape) in es.zip c.returnShapes do
      match shape with
      | .scalar => exprInto n e rets[pos]!
      | .stackBuf size => do
          let some cells ← stackOf e | fail s!"expected a StackBuf({size}) return"
          if cells.length != size then fail s!"returned StackBuf has size {cells.length}, expected {size}"
          for k in List.range size do
            copy cells[k]! rets[pos + k]!
      pos := pos + shape.cells
    emit (.ret rets)

/-- A branch body, its bindings local (`branch`, `scoped`). -/
def branch : Nat → Seg → List Source.Stmt → M (List Core.Stmt)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, seg, body => do
    let saved := (← get).names
    let ((), _, blk) ← capture <| withSeg seg do
      stmts n body
      if (← get).pending then anchor
    modify fun st => { st with names := saved }
    return blk

/-- `if` (`lower_if`). -/
def lowerIf : Nat → Bool → Expr → Expr → List Source.Stmt → List Source.Stmt → Bool → M Unit
  | 0, _, _, _, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, eq, lhs, rhs, thn, els, forceConst => do
    let a ← eval evalFuel lhs
    let b ← eval evalFuel rhs
    let small : Option Nat → Option Nat := fun k => k.bind fun k => if k < u32Bound then some k else none
    if let (some ai, some bi) := (small a.int, small b.int) then
      if !forceConst then
        for k in [a, b] do
          if let some (i, _) := k.diverging then
            fail s!"a side reads as the integer {i} where a condition folds and as another field element where a value is wanted: write `if const(...)`"
      let taken := (ai == bi) == eq
      return ← withSeg (if taken then .t else .e) (stmts n (if taken then thn else els))
    if forceConst then
      if let (some fa, some fb) := (a.field, b.field) then
        let taken := (fa == fb) == eq
        return ← withSeg (if taken then .t else .e) (stmts n (if taken then thn else els))
      fail "`if const(...)` asks for a compile-time decision, but this condition is not one"
    let x ← if (← tryLit rhs) == some 0 then expr n lhs
      else if (← tryLit lhs) == some 0 then expr n rhs
      else do
        let la ← expr n lhs
        let lb ← expr n rhs
        pureAdd la lb
    let (zSeg, zBlk, nSeg, nBlk) := if eq then (Seg.t, thn, Seg.e, els) else (Seg.e, els, Seg.t, thn)
    let z ← branch n zSeg zBlk
    let nz ← if nBlk.isEmpty then pure [] else branch n nSeg nBlk
    emit (.ite x z nz)

/-- `assert a != b` (`lower_assert_ne`). -/
def lowerAssertNe : Nat → Expr → Expr → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, a, b => do
    if let (.lit x, .lit y) := (a, b) then
      if x == y then fail s!"assert a != b: sides are the compile-time-equal literal {x}"
      return
    let la ← expr n a
    let lb ← expr n b
    let x ← pureAdd la lb
    let inv ← fresh
    emitHint (.inverse x inv)
    let p ← fresh
    emitAtom (.assertNe x inv p)

/-- `assert log e < bound` (`lower_assert_lt`). -/
def lowerAssertLt : Nat → Expr → LtBound → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, e, bound => do
    let kcell ← match bound with
      | .const k => do
          if k < 1 then fail "range-check bound GEN ** 0 names the empty set"
          if 2 ^ 16 < k then fail s!"range-check bound GEN ** {k} exceeds 2^16 (the minimum memory size)"
          constCell (gpowE (k - 1))
      | .runtime b => do
          if (← tryFieldConst b).isSome then
            fail "a compile-time range-check bound must be written as `log GEN ** k` or an integer"
          let bcell ← expr n b
          let inv ← constCell (ofK gInv)
          let c ← fresh
          emitAtom (.mul c bcell inv)
          pure c
    let x ← expr n e
    let y ← fresh
    let t1 ← fresh
    let t2 ← fresh
    emitAtom (.rangeCheck x y t1 t2 kcell)

/-- `match` (`lower_match`). -/
def lowerMatch : Nat → List Expr → Expr → List Expr → M Unit
  | 0, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, targets, x, arms => do
    for arm in arms do
      if let .call f _ := arm then
        if let some d ← origDef f then
          if !d.inline && d.returnShapes.any (· != .scalar) then
            fail "a normal function's StackBuf return cannot cross a match join; bind it with `let`"
    let isInlineArm : Expr → M Bool := fun
      | .call f _ => return (← origDef f).any (·.inline)
      | _ => return false
    let allCalls ← arms.allM fun a => do
      match a with
      | .call .. => return !(← isInlineArm a)
      | _ => return false
    if allCalls && !arms.isEmpty then
      let specialized ← arms.mapM fun a => do
        match a with
        | .call f cargs => specialize f cargs
        | _ => fail "internal: a call arm"
      let rt0 := specialized.head!.2
      if specialized.all (·.2 == rt0) then
        return ← lowerDispatchedCall n targets x (specialized.map (·.1)) rt0
    let xo ← expr n x
    let (rcells, binds) ← retTargets targets
    let mut blocks := #[]
    for (j, arm) in (List.range arms.length).zip arms do
      let saved := (← get).names
      let ((), _, blk) ← capture do
        withSeg (.a j) do
          match rcells with
          | [rc] => exprInto n arm rc
          | _ => do
              let .call f cargs := arm | fail "a multi-target match arm must be a function call"
              modify fun st => { st with inlineStackRet := none }
              callInto n f cargs rcells
              let bs := (← get).inlineStackRet
              modify fun st => { st with inlineStackRet := none }
              if let some bs := bs then
                for (b, rc) in bs.zip rcells do
                  match b with
                  | .gaddr ga => do
                      let c ← materialize ga
                      copy c rc
                  | .stack cells => do
                      let [c] := cells | fail "a multi-cell StackBuf return cannot cross a match join"
                      copy c rc
                  | .scalar => pure ()
          if (← get).pending then anchor
      modify fun st => { st with names := saved }
      blocks := blocks.push blk
    emit (.match_ xo blocks.toList)
    bindTargets binds

/-- A fused `match` of calls (`lower_dispatched_call`). -/
def lowerDispatchedCall : Nat → List Expr → Expr → List String → List Expr → M Unit
  | 0, _, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, targets, x, callees, rtArgs => do
    let defs ← callees.filterMapM calleeDef
    if let some shared := defs.head? then
      for d in defs do
        if d.params.map (·.shape) != shared.params.map (·.shape) then
          fail s!"`{d.name}` does not take the same parameter shapes as the other arms of this dispatch"
      if shared.params.any (·.shape != .scalar) then
        fail "a `match` arm cannot pass a `StackBuf` parameter"
    for d in defs do
      if d.params.length != rtArgs.length then
        fail s!"`{d.name}` takes {d.params.length} arguments, dispatched call passes {rtArgs.length}"
      if d.returnShapes.length != targets.length then
        fail s!"`{d.name}` returns {d.returnShapes.length} values, dispatched call binds {targets.length}"
      if d.returnShapes.any (· != .scalar) then
        fail s!"`{d.name}`: a multi-cell StackBuf return cannot cross a dispatched join"
    let (rcells, binds) ← retTargets targets
    let argCells ← rtArgs.mapM (expr n)
    let xo ← expr n x
    emit (.dispatch xo callees argCells rcells)
    bindTargets binds

/-- `for var in mul_range(GEN ** lo, hi)`, lifted to `__loopN` (`lower_for`). -/
def lowerFor : Nat → Nat → String → Nat → ForBound → List Source.Stmt → M Unit
  | 0, _, _, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, line, var, lo, hi, body => do
    let id := (← get).loopCtr
    modify fun st => { st with loopCtr := st.loopCtr + 1 }
    let loopName := s!"__loop{id}"
    let boundVar := s!"__bound{id}"
    let (exit, entryBound) := match hi with
      | .const h => (Expr.gpow h, Expr.gpow h)
      | .runtime e => (Expr.var boundVar, e)
    let (refs, bound) := Source.Stmt.freeVarsList body ([], [var])
    let shadowed := Source.Stmt.bindsList body
    let mut captures := #[]
    for r in refs do
      if bound.contains r then continue
      if (← stackOfName r).isSome && !shadowed.contains r then
        fail s!"StackBuf `{r}` cannot be captured into a `for` loop"
      match ← lookup r with
      | some ⟨.scalar _, _⟩ | some ⟨.gaddr _, _⟩ | some ⟨.fconst _, _⟩ =>
          if !captures.contains r then captures := captures.push r
      | _ => pure ()
    let runtime := match hi with | .runtime _ => true | .const _ => false
    let params := [var] ++ (if runtime then [boundVar] else []) ++ captures.toList
    let capArgs : Expr → Expr → List Expr := fun first b =>
      [first] ++ (if runtime then [b] else []) ++ captures.toList.map .var
    let nextVar := s!"__next{id}"
    let loopBody := body ++ [
      .mk line (.let_ nextVar (.mul (.var var) .gen)),
      .mk line (.callIfNe (.var nextVar) exit loopName (capArgs (.var nextVar) (.var boundVar))),
      .mk line (.ret [])]
    let helper : Func := { name := loopName, params := params.map fun q => ⟨q, .runtime .scalar⟩,
                           returnShapes := [], body := loopBody, inline := false }
    modify fun st => { st with queue := st.queue.push helper }
    match hi with
    | .const h =>
        if lo != h then
          discard <| call n loopName (capArgs (.gpow lo) (.gpow h)) 0
    | .runtime _ =>
        stmtKind n line (.callIfNe (.gpow lo) entryBound loopName (capArgs (.gpow lo) entryBound))

/-- The precompile and the hints (`lower_builtin`); `false` for another callee. -/
def lowerBuiltin : Nat → String → List Expr → M Bool
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, f, args => do
    match f with
    | "hint_decompose_bits" | "hint_decompose_bits_exponent" => do
        let plain := f == "hint_decompose_bits"
        if !(args.length == 3 || (plain && args.length == 4)) then
          fail s!"{f} takes (bits, value, nbits[, start])"
        let nbits ← constIndex args[2]!
        let bits ← bitsDest n args[0]! nbits
        let value ← expr n args[1]!
        if plain then
          let start ← match args[3]? with
            | some s => constIndex s
            | none => pure 0
          if 192 < start + nbits then fail s!"{f} reads bits {start}..{start + nbits} of a 192-bit word"
          emitHint (.bits value start nbits bits)
        else
          emitHint (.bitsExp value nbits bits)
        return true
    | "blake2s" => do
        lowerBlake2s n args
        return true
    | "assert_in_k" => do
        let [a0, a1] := args | fail "assert_in_k(a, b) takes two scalar cells"
        let a ← expr n a0
        let b ← expr n a1
        emitAtom (.assertInK a b)
        return true
    | "hint_f192_limbs" => do
        let [d, v] := args | fail "hint_f192_limbs takes two arguments, `(dest, value)`"
        let some cells ← stackOf d | fail "hint_f192_limbs writes frame cells: its destination must be a StackBuf"
        if !(1 ≤ cells.length && cells.length ≤ 3) then
          fail "hint_f192_limbs destination must have 1..=3 cells"
        let value ← expr n v
        emitHint (.limbs value cells)
        return true
    | _ => return false

/-- A `blake2s` operand: two cells (`blake2s_operand`). -/
def blake2sOperand : Nat → Expr → M CellRun
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    let run ← cellRun n e
    let len := match run with
      | .stack cells => cells.length
      | .heap _ _ len => len
    if len != 2 then fail "a blake2s operand must span exactly 2 cells"
    return run

/-- A `blake2s` input operand as its two words (`blake2s_input`). -/
def blake2sInput : Nat → Expr → M (V × V)
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    if let .list ws := e then
      let [w0, w1] := ws | fail s!"a blake2s operand written as a list needs exactly 2 words, got {ws.length}"
      let a ← expr n w0
      let b ← expr n w1
      return (a, b)
    match ← blake2sOperand n e with
    | .stack cells => return (cells[0]!, cells[1]!)
    | .heap ptr lo _ => do
        let t ← freshRun 2
        emitAtom (.load t[0]! ptr lo)
        emitAtom (.load t[1]! ptr (lo + 1))
        return (t[0]!, t[1]!)

/-- A chaining value: two consecutive cells (`blake2s_cv`). -/
def blake2sCv : Nat → Expr → M (V × V)
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    let (a, b) ← blake2sInput n e
    if a.adjacent b then return (a, b)
    let cv ← freshRun 2
    copy a cv[0]!
    copy b cv[1]!
    return (cv[0]!, cv[1]!)

/-- `blake2s(a, b, out, ...)` (`lower_blake2s`). -/
def lowerBlake2s : Nat → List Expr → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, args => do
    let firstKw := (args.findIdx? isKw).getD args.length
    if firstKw != 3 then fail "blake2s takes three positional arguments: (a, b, out)"
    let kws := args.drop 3
    let some kwargs := kws.mapM kwArg | fail "keyword arguments must follow the three positional blake2s arguments"
    for i in List.range kwargs.length do
      if (kwargs.take i).any (·.1 == kwargs[i]!.1) then fail s!"duplicate blake2s keyword `{kwargs[i]!.1}`"
    let allowed := ["cv", "counter", "final", "last_node", "md"]
    if kwargs.any (!allowed.contains ·.1) then fail "unknown blake2s keyword"
    let get := fun (k : String) => (kwargs.find? (·.1 == k)).map (·.2)
    let customized := kwargs.any fun (k, _) => k == "counter" || k == "final" || k == "last_node"
    let runtimeMd := get "md"
    if runtimeMd.isSome && customized then
      fail "blake2s md= is the whole metadata word, so counter=, final= and last_node= cannot come with it"
    if (get "cv").isSome && !customized && runtimeMd.isNone then
      fail "blake2s with cv= requires one of counter=, final=, last_node= or md="
    let (a0, a1) ← blake2sInput n args[0]!
    let (b0, b1) ← blake2sInput n args[1]!
    let (c0, c1, heapOut) ← match ← blake2sOperand n args[2]! with
      | .stack cells => pure (cells[0]!, cells[1]!, none)
      | .heap ptr lo _ => do
          let c ← freshRun 2
          pure (c[0]!, c[1]!, some (ptr, lo))
    let (cv0, cv1) ← match get "cv" with
      | some v => blake2sCv n v
      | none => do
          let cv ← freshRun 2
          emitAtom (.const cv[0]! ivCells.1)
          emitAtom (.const cv[1]! ivCells.2)
          pure (cv[0]!, cv[1]!)
    let md ← match runtimeMd with
      | some e => do
          let m ← expr n e
          if m == c0 || m == c1 then fail "blake2s md= must not name a cell of the digest destination"
          pure m
      | none => do
          let constKw : String → Nat → M Nat := fun name dflt => do
            match get name with
            | none => pure dflt
            | some e => do
                match ← tryConstInt e with
                | some k => pure k
                | none => fail s!"BLAKE2s `{name}` must be a compile-time integer; a runtime metadata word goes through md="
          let counter ← constKw "counter" 64
          if u64Bound ≤ counter then fail s!"blake2s counter= {counter} does not fit in u64"
          let f0 := if (← constKw "final" (if customized then 0 else 1)) != 0 then finalFlag else 0
          let f1 := if (← constKw "last_node" 0) != 0 then 2 ^ 32 - 1 else 0
          constCell (metadata counter f0 f1)
    emitAtom (.blake2s a0 a1 b0 b1 cv0 cv1 c0 c1 md)
    if let some (ptr, lo) := heapOut then
      emitAtom (.load c0 ptr lo)
      emitAtom (.load c1 ptr (lo + 1))

/-- `hint_witness(dest, "stream")` (`lower_hint_witness`). -/
def lowerHintWitness : Nat → Expr → String → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, dest, name => do
    match ← cellRun n dest with
    | .stack cells => emitHint (.witness name (.stack cells))
    | .heap ptr lo len => emitHint (.witness name (.heap ptr lo len))

/-- A statement (`stmt`). -/
def stmtKind : Nat → Nat → StmtKind → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, line, k => do
    match k with
    | .let_ name e => do
        match e with
        | .stackBuf sz => rebind name (.stack (← freshRun sz))
        | .list es => do
            let cells ← freshRun es.length
            for (c, el) in cells.zip es do
              exprInto n el c
            rebind name (.stack cells)
        | .call "addr" cargs => rebind name (.gaddr (← stackAddr cargs))
        | .var v =>
            if let some cells ← stackOfName v then rebind name (.stack cells)
            else letValue n name e
        | _ => letValue n name e
    | .letTuple names f args => do
        let dsts ← call n f args names.length
        let binds := (← get).inlineStackRet
        modify fun st => { st with inlineStackRet := none }
        for (i, nm, d) in (List.range names.length).zip (names.zip dsts) do
          rebind nm (retBinding (binds.bind (·[i]?)) d)
    | .assertEq a b => do
        let la ← expr n a
        let lb ← expr n b
        emitAtom (.assertEq la lb)
    | .assertNe a b => lowerAssertNe n a b
    | .assertLt e bound => lowerAssertLt n e bound
    | .hintWitness dest name => lowerHintWitness n dest name
    | .letHintWitness name stream => do
        let dst ← fresh
        emitHint (.witness stream (.stack [dst]))
        rebind name (.scalar dst)
    | .print _ value => do
        discard <| expr n value
        anchor
    | .ite eq lhs rhs thn els fc => lowerIf n eq lhs rhs thn els fc
    | .match_ targets x arms => lowerMatch n targets x arms
    | .call f args => do
        if !(← lowerBuiltin n f args) then
          discard <| call n f args 0
    | .store arr idx val => do
        match ← frameCell arr idx with
        | some c => exprInto n val c
        | none => do
            let v ← expr n val
            let (ptr, o2) ← heapAddr n arr idx
            emitAtom (.load v ptr o2)
    | .ret es => lowerReturn n es
    | .callIfNe lhs rhs callee args => do
        let la ← expr n lhs
        let lb ← expr n rhs
        let x ← pureAdd la lb
        lowerCall n callee args (some x) []
    | .for_ var lo hi body => lowerFor n line var lo hi body
    | .unroll var lo hi body => do
        let some l ← tryConstIndex lo | fail "unroll bounds must be compile-time integers"
        let some h ← tryConstIndex hi | fail "unroll bounds must be compile-time integers"
        if h < l then fail s!"unroll(a, b) needs a <= b, got ({l}, {h})"
        let blocks ← (List.range' l (h - l)).mapM fun j =>
          capture (withSeg (.u j) (stmts n (Source.Stmt.substList var (.lit j) body)))
        appendBlocks (blocks.map fun ((), pd, b) => (pd, b))

/-- The value binding of `name = e` (the general arm of `Let`). -/
def letValue : Nat → String → Expr → M Unit
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, name, e => do
    let known ← eval evalFuel e
    if let some ga := known.addr then rebind name (.gaddr ga)
    else if let some c := known.field then rebind name (.fconst c)
    else if let some k := known.int then rebind name (.fconst (litField k))
    else
      match e with
      | .call cf cargs =>
          if (← origDef cf).isSome then
            let ds ← call n cf cargs 1
            let b := (← get).inlineStackRet.bind (·.head?)
            modify fun st => { st with inlineStackRet := none }
            rebind name (retBinding b ds.head!)
          else
            rebind name (.scalar (← expr n e))
      | _ => rebind name (.scalar (← expr n e))
    if let some k := known.int then setInt name k

/-- A block, statement `i` at position `Seg.s i`. -/
def stmts : Nat → List Source.Stmt → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, ss =>
      ((List.range ss.length).zip ss).forM fun (i, s) => withSeg (.s i) (stmtKind n s.line s.kind)
end

/-! ## Functions and the program -/

/-- The fuel of an expansion: deeper than any nesting of the guest. -/
def fuel : Nat := 100000

/-- The parameters' bindings and cells (`lower_func`). -/
def paramBindings (f : Func) : List (String × Bound) × List V := Id.run do
  let mut names := []
  let mut pos := 0
  for p in f.params do
    match Param.shape p with
    | Shape.stackBuf k =>
        names := (p.name, ⟨.stack ((List.range k).map fun i => V.param (pos + i)), none⟩) :: names
        pos := pos + k
    | Shape.scalar =>
        names := (p.name, ⟨.scalar (V.param pos), none⟩) :: names
        pos := pos + 1
  return (names, (List.range pos).map V.param)

/-- The state lowering `f` starts in. -/
def initState (p : Program) (f : Func) (queue : Array Func) (loopBase : Nat) : St :=
  { ctx := { defs := p.funcs, arrays := p.constArrays, fnName := f.name, isMain := f.name == "main",
             returnShapes := f.returnShapes },
    names := (paramBindings f).1, heapSizes := [], path := [], tag := 0, out := #[],
    pending := false, inlineRet := none, inlineStackRet := none, inlineCalls := [], queue,
    loopCtr := loopBase }

/-- Lower a function's body (`lower_func`). -/
def lowerFunc (f : Func) : M Unit := do
  stmts fuel f.body
  if (← ctx).isMain then
    emit (.ret [])
  else
    match f.body.getLast? with
    | some (.mk _ (.ret _)) => pure ()
    | _ =>
        let line := (f.body.getLast?.map (·.line)).getD 0
        withSeg (.s f.body.length) (stmtKind fuel line (.ret []))

/-- The core function of `f`, the queue after it, and the loop counter after it: `queue` is
every function queued before (it decides which specializations are new) and `loopBase` the
number of loops lowered before. -/
def expandFn (p : Program) (f : Func) (queue : Array Func := #[]) (loopBase : Nat := 0) :
    Except String (Core.Fn × Array Func × Nat) := do
  if let some q := f.params.find? (fun q => p.constArrays.any (·.1 == q.name)) then
    throw s!"`{f.name}`: parameter `{q.name}` collides with a top-level constant array"
  let ((), st) ← (lowerFunc f).run (initState p f queue loopBase)
  return (⟨f.name, (paramBindings f).2, st.out.toList⟩, st.queue, st.loopCtr)

/-- The specialization of `f` at these `Const` arguments, as the compiler queues it. -/
def specializeFn (f : Func) (constArgs : List Expr) : Except String Func := do
  let consts := f.params.filter (·.kind == .const)
  if consts.length != constArgs.length then throw s!"`{f.name}` takes {consts.length} Const arguments"
  let substs := (consts.zip constArgs).map fun (q, a) => (q.name, a)
  return { name := specName f.name substs, params := f.params.filter (·.kind != .const),
           returnShapes := f.returnShapes, body := substBody f.body substs, inline := false }

/-- The compiler's queue (`compile`), at most `fuel` functions. -/
def expandQueue (p : Program) : Nat → Nat → Array Func → Nat → Array Core.Fn →
    Except String (Array Core.Fn)
  | 0, _, _, _, _ => throw "too many functions"
  | budget + 1, i, queue, loopCtr, out =>
      match queue[i]? with
      | none => return out
      | some f =>
          if f.hasConstParams || f.inline then expandQueue p budget (i + 1) queue loopCtr out
          else do
            let (fn, queue, loopCtr) ← expandFn p f queue loopCtr
            expandQueue p budget (i + 1) queue loopCtr (out.push fn)

/-- Every function the compiler lowers, in its order: `main` first. -/
def expandProgram (p : Program) : Except String Core.Program := do
  let some main := p.funcs.find? (·.name == "main") | throw "program needs a `main`"
  if main.hasConstParams then throw "main cannot take Const parameters"
  if main.inline then throw "main cannot be `@inline`"
  let queue := #[main] ++ (p.funcs.filter (·.name != "main")).toArray
  return (← expandQueue p 1000000 0 queue 0 #[]).toList

end
end LeanVM.Guest.Expand
