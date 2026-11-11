/-
  LeanVM.Guest.Expand

  The zkDSL front end in Lean: a source function and its `Const` arguments to the core IR function
  the compiler lowers, by the compiler's own rules (`crates/lean_compiler/src/lower.rs` and
  `lower/*.rs`, leanVM main `40f877dc`).
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
  arguments, chained `match`es (back to back in an `unroll`, all arms `@inline`, the next
  scrutinee a free frame cell: the entered one sets nothing above its arms; a chain is the
  sequence of its `match`es in the core IR, which only the bytecode's jumps tell apart),
  `mul_range` lifted to a tail-recursive helper `__loopN` taking its captured values, a captured
  `StackBuf` as a `StackBuf(n)` parameter;
* `StackBuf` runs, slices, list literals and `addr`, heap addressing, and the hints;
* the Keccak builtins (`lower/builtins.rs`): `keccak(a, b, out, tail=, len=, cap=)` and
  `keccak_cells(cells, out, state=, len=, final=)`, a list comprehension expanded once its bounds
  are compile-time integers, one `KECCAK` atom per block of 136 bytes (block `k` read from cell
  `17k/2` in the layout of its parity, its output in the next block's layout, the last in the even
  one), the padding XORed into the message cells as constants or one `XOR` with a constant cell
  (`xor_byte`), the lazily `SET` padding run `[0x01, 0, 0, 0, 0]` whose windows are the constant
  `tail` and `cap` runs (`keccak_pad_run`, reverting at a branch join with the bindings), message
  cells XORed into the previous output (`sponge_xor`), the copies into a run, and the last
  block's output cells: the one, two or thirteen cells its destination holds (`keccak_out`; the
  atom's `outs`, whose length is the instruction's `out_cells`), a heap destination's through a
  stack run of its size, copied out afterwards.

What the compiler shares (pure results, pooled constants, repeated loads) is not shared here: a
second occurrence is a second atom with a fresh name, on the same relation. A value's name is its
position (`Core.Seg`): statement index, `unroll` counter, branch, arm, inline call site.

The loop counter `__loopN` is the compiler's: one counter over the whole compilation, advanced
in lowering order, which `expandProgram` reproduces and `expandFn` takes as `loopBase`.

Three places do not reproduce the compiler exactly; none changes a relation. An `addr` pointer
is a value of its own (`Atom.frameAddr`), where the compiler folds the frame offset into it, so
the compiler's `FOLD_MAX` test on such a pointer counts that offset and this one does not; a
hint left pending at the end of a branch gets the compiler's anchor (`SET 0`) when no atom
followed it, which may differ where the compiler's sharing emitted nothing; and four `keccak`
message cells are used in place (`sponge_run`) only when they are one run of the expansion
(`V.adjacent`), where the compiler also uses four cells that its allocator happened to place one
after another (the guest's `fs_perm_pending`, four loads in a row): there the expansion copies
them into a fresh run, and a certificate places each copy in the cell it copies.
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

/-- A materialized shifted pointer (`Scope::mat_cells`): the value `out` holds `base·g^exp`, made
as `src · g^dist` (`src` the base itself or an earlier materialization of it). -/
structure Mat where
  exp : Nat
  out : V
  src : V
  dist : Nat
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
  /-- The run `[0x01, 0, 0, 0, 0]` set for the `keccak`s of this scope (`Scope::keccak_pad`). -/
  keccakPad : Option (List V) := none
  /-- The constants set in this scope, as the compiler pools them (the keys of
  `Scope::const_cells`): which of them are set decides how a shifted pointer is made. -/
  consts : List E := []
  /-- The shifted pointers materialized in this scope, by base (`Scope::mat_cells`). -/
  mats : List (V × List Mat) := []
  /-- The run each `addr` pointer names. -/
  addrRuns : List (V × List V) := []
  /-- The scrutinee of the `match` the one being lowered enters directly, its arms ending in
  the next one's dispatch (`chain_next`). -/
  chainNext : Option V := none
  /-- Set for a `match` an earlier one's arms dispatch into: its scrutinee (`chain_in`). -/
  chainIn : Option V := none
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

/-- Record `c` as a constant set in this scope (`Scope::const_cells`). -/
def poolConst (c : E) : M Unit :=
  modify fun st => if st.consts.contains c then st else { st with consts := c :: st.consts }

/-- Whether `c` is a constant set in this scope. -/
def hasConst (c : E) : M Bool := return (← get).consts.contains c

/-- A fresh value holding `c` (`const_cell`). -/
def constCell (c : E) : M V := do
  let o ← fresh
  emitAtom (.const o c)
  poolConst c
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

/-- The shifted pointers of a base materialized in this scope. -/
def matsOf (c : V) : M (List Mat) :=
  return (((← get).mats.find? (·.1 == c)).map (·.2)).getD []

/-- A value holding an address (`materialize`): a constant is one `SET`; a base with no shift
is that value; a shifted base `c·g^exp` is a product, from the nearest materialization
`c·g^e` below whose distance `g^(exp-e)` is a constant already set, when `g^exp` is not one, else
from `c` and `g^exp` (`mem.rs`, `materialize`). The compiler hands a second materialization of
the same `c·g^exp` the first's cell; here it is the first's atoms again, on fresh values. -/
def materialize (ga : GAddr) : M V := do
  match ga.base, ga.exp with
  | some c, 0 => return c
  | none, exp => constCell (gpowE exp)
  | some c, exp => do
      -- An `addr` pointer shifted: the compiler's base is its own frame pointer and the run's
      -- offset (`stack_addr`), which this expansion does not place, so the shifted pointer is the
      -- `addr` of the run from cell `exp` on.
      if let some (_, cells) := (← get).addrRuns.find? (·.1 == c) then
        let p ← fresh
        emitFrameAddr p (cells.drop exp)
        return p
      let mats ← matsOf c
      if let some m := mats.find? (·.exp == exp) then
        let k ← constCell (gpowE m.dist)
        return ← pureMul m.src k
      let mut best : Option Mat := none
      if !(← hasConst (gpowE exp)) then
        for m in mats do
          if m.exp < exp && (← hasConst (gpowE (exp - m.exp))) then
            if best.all (·.exp < m.exp) then best := some m
      let (src, dist) := match best with
        | some m => (m.out, exp - m.exp)
        | none => (c, exp)
      let k ← constCell (gpowE dist)
      let o ← pureMul src k
      let m : Mat := ⟨exp, o, src, dist⟩
      modify fun st => { st with
        mats := (c, mats ++ [m]) :: st.mats.filter (·.1 != c) }
      return o

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
      modify fun st => { st with addrRuns := (p, cells) :: st.addrRuns }
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

/-- A keyword argument, `__kw_key(value)`. -/
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

/-! ## Keccak (`lower/builtins.rs`)

The lowering's view of a message cell, the padding run, and the absorption of a message into
`KECCAK` atoms, block by block: everything of `keccak` and `keccak_cells` that evaluates no source
expression. -/

/-- One message cell of a `keccak` block, as the lowering knows it (`SpongeCell`): a literal
zero, a constant, or a value. -/
inductive SpongeCell where
  | zero
  | const (c : E)
  | cell (v : V)
  deriving Inhabited

/-- Whether a message cell is a literal zero. -/
def SpongeCell.isZero : SpongeCell → Bool
  | .zero => true
  | _ => false

/-- Where a `keccak` writes (`KeccakOut`): the values its last `KECCAK` writes, its first one, two
or thirteen output cells (the atom's `outs`, whose length is the instruction's `out_cells`), and
the heap run `(ptr, lo)` to copy them out to afterwards. -/
structure KeccakOut where
  state : List V
  heap : Option (V × Nat)

/-- Whether values are one run of consecutive cells of the expansion. -/
def isRun : List V → Bool
  | a :: b :: vs => a.adjacent b && isRun (b :: vs)
  | _ => true

/-- The five values `[0x01, 0, 0, 0, 0]` every `keccak` of this scope shares, set at the first
(`keccak_pad_run`): the zero `tail` and `cap` are its window from `1`, the `tail` of a message
ending at a cell boundary its window from `0`. -/
def keccakPadRun : M (List V) := do
  if let some o := (← get).keccakPad then return o
  let o ← freshRun 5
  for (v, k) in o.zipIdx do
    emitAtom (.const v (if k = 0 then keccakPadValue else 0))
    poolConst (if k = 0 then keccakPadValue else 0)
  modify fun st => { st with keccakPad := some o }
  return o

/-- The last rate lane of a 64-byte message's one block, the padding's closing `0x80` byte
(`two_to_one_close`). -/
def twoToOneClose : E := word (0x80 * 2 ^ 56) 0 0

/-- A value holding a message cell (`sponge_cell`). -/
def spongeCell : SpongeCell → M V
  | .zero => return (← keccakPadRun).getD 1 default
  | .const c => do
      if c == keccakPadValue then return (← keccakPadRun).getD 0 default
      constCell c
  | .cell o => return o

/-- `state + c`, into `dst` if given (`sponge_xor`): a zero `c` is the state value itself, or a
copy of it into `dst`. -/
def spongeXor (state : V) (c : SpongeCell) (dst : Option V) : M V := do
  match c with
  | .zero =>
      match dst with
      | some d => do
          copy state d
          return d
      | none => return state
  | c => do
      let other ← spongeCell c
      let d ← match dst with
        | some d => pure d
        | none => fresh
      emitAtom (.add d state other)
      return d

/-- Four consecutive values holding the message cells (`sponge_run`): where they already lie, a
window of the padding run, or a fresh copy. -/
def spongeRun (cells : List SpongeCell) : M (List V) := do
  let vals := cells.filterMap fun | .cell o => some o | _ => none
  if vals.length == cells.length && isRun vals then return vals
  if cells.all (·.isZero) then return (← keccakPadRun).drop 1
  if let .const c :: rest := cells then
    if c == keccakPadValue && rest.all (·.isZero) then return (← keccakPadRun).take 4
  let t ← freshRun cells.length
  for (c, d) in cells.zip t do
    match c with
    | .zero => emitAtom (.const d 0)
    | .const v => emitAtom (.const d v)
    | .cell o => copy o d
  return t

/-- The `m` and `tail` values of a `KECCAK` reading a block's first eight cells (`keccak_rate`):
themselves from the zero state, or XORed into the values of the previous output `st` they line
up with. -/
def keccakRate (block : List SpongeCell) (st : Option (List V)) : M (List V × List V) := do
  let cell := fun (i : Nat) => block.getD i .zero
  match st with
  | none => do
      let m ← (List.range 4).mapM fun i => spongeCell (cell i)
      let tail ← spongeRun ((List.range 4).map fun j => cell (4 + j))
      return (m, tail)
  | some st => do
      let m ← (List.range 4).mapM fun i => spongeXor (st.getD i default) (cell i) none
      if (List.range 4).all fun j => (cell (4 + j)).isZero then
        return (m, (st.drop 4).take 4)
      let tail ← freshRun 4
      for j in List.range 4 do
        discard <| spongeXor (st.getD (4 + j) default) (cell (4 + j)) (some (tail.getD j default))
      return (m, tail)

/-- XOR the byte `v` into byte `pos` of the message cells (`xor_byte`): into a constant, or by one
`XOR` with a constant cell. -/
def xorByte (cells : List SpongeCell) (pos v : Nat) : M (List SpongeCell) := do
  let i := pos / 16
  let w := byteWord pos v
  let c ← match cells.getD i .zero with
    | .zero => pure (SpongeCell.const w)
    | .const c => pure (.const (c + w))
    | .cell o => do
        let k ← constCell w
        let dst ← fresh
        emitAtom (.add dst o k)
        pure (.cell dst)
  return cells.set i c

/-- The `KECCAK` atoms absorbing `cells` into `state` (the zero state if `none`), the last writing
the cells `out` (its first one, two or thirteen output cells), each earlier one a whole 13-cell
state the next one reads (`emit_keccak_message`). With `finalLen` the message is the cells' first `finalLen` bytes,
padded, in `finalLen / rate + 1` blocks (`primitives::hash::permutations`); without, the cells
zero-extended to whole blocks. `padded`: the cells past `finalLen` already hold the padding's
first byte and zeros (`padTailInPlace`). -/
def emitKeccakMessage (cells : List SpongeCell) (finalLen : Option Nat) (state : Option (List V))
    (out : List V) (padded : Bool) : M Unit := do
  let blocks := match finalLen with
    | some len => len / Protocol.KeccakHash.rate + 1
    | none => (16 * cells.length + Protocol.KeccakHash.rate - 1) / Protocol.KeccakHash.rate
  let read := 17 * (blocks - 1) / 2 + blockCells
  let mut cells := cells ++ List.replicate (read - cells.length) SpongeCell.zero
  if let some len := finalLen then
    if !padded then
      let past := (len + 15) / 16
      if let some k := (List.range' past (cells.length - past)).find? fun k =>
          !(cells.getD k .zero).isZero then
        fail s!"keccak len= {len} ends before message cell {k}, which is not a literal 0"
      cells ← xorByte cells len Protocol.KeccakHash.padFirst.toNat
    cells ← xorByte cells (blocks * Protocol.KeccakHash.rate - 1) Protocol.KeccakHash.padLast.toNat
  let mut state := state
  for k in List.range blocks do
    let last := k + 1 == blocks
    let c ← if last then pure out else freshRun stateCells
    let block := (cells.drop (17 * k / 2)).take blockCells
    let (m, tail) ← keccakRate block state
    let b8 ← match state with
      | none => spongeCell (block.getD 8 .zero)
      | some st => spongeXor (st.getD 8 default) (block.getD 8 .zero) none
    let cap ← match state with
      | none => pure ((← keccakPadRun).drop 1)
      | some st => pure ((st.drop 9).take 4)
    emitAtom (.keccak (m ++ tail ++ [b8] ++ cap) c (k % 2 == 1) (!last && k % 2 == 0))
    state := some c

/-- Copy what `keccakOut` promised out of the cells written, to a heap destination
(`keccak_finish`). -/
def keccakFinish (out : KeccakOut) : M Unit := do
  if let some (ptr, lo) := out.heap then
    for (s, k) in out.state.zipIdx do emitAtom (.load s ptr (lo + k))

/-- The keyword arguments after builtin `f`'s positional ones, checked against `allowed`
(`keccak_kwargs`). -/
def keccakKwargs (args : List Expr) (f : String) (positional allowed : List String) :
    M (List (String × Expr)) := do
  let firstKw := (args.findIdx? isKw).getD args.length
  if firstKw != positional.length then
    fail s!"{f} takes {positional.length} positional arguments: ({", ".intercalate positional})"
  let some kwargs := (args.drop firstKw).mapM kwArg
    | fail "keyword arguments must follow the positional keccak arguments"
  for i in List.range kwargs.length do
    if (kwargs.take i).any (·.1 == (kwargs.getD i ("", .lit 0)).1) then
      fail s!"duplicate keccak keyword `{(kwargs.getD i ("", .lit 0)).1}`"
  if kwargs.any (!allowed.contains ·.1) then
    fail s!"unknown keccak keyword; the keywords are {allowed}"
  return kwargs

/-- A keyword's value. -/
def kwGet (kwargs : List (String × Expr)) (k : String) : Option Expr :=
  (kwargs.find? (·.1 == k)).map (·.2)

/-- The message length `len=` names, at most the `n` cells' bytes and all of them by default
(`keccak_len`). -/
def keccakLen (kwargs : List (String × Expr)) (n : Nat) : M Nat := do
  let some e := kwGet kwargs "len" | return 16 * n
  let some len ← tryConstInt e | fail "keccak `len` must be a compile-time integer"
  if 16 * n < len then fail s!"keccak len= {len} is past the {16 * n} bytes of its {n} cells"
  return len

/-- Whether every arm is an `@inline` call (`all_inline`). -/
def allInline (arms : List Expr) : M Bool :=
  arms.allM fun
    | .call f _ => return (← origDef f).any (·.inline)
    | _ => return false

/-- The frame cell `e` names, if reading it emits nothing and names nothing `targets` rebinds: a
scalar variable, or a `StackBuf` cell at a compile-time index (`free_cell`). -/
def freeCell (e : Expr) (targets : List Expr) : M (Option V) := do
  let names := e.freeVars []
  if names.any (fun n => targets.any (Expr.isVarNamed n)) then return none
  match e with
  | .var n =>
      match ← lookup n with
      | some ⟨.scalar o, _⟩ => return some o
      | _ => return none
  | .index (.var n) i =>
      let some k ← tryConstIndex i | return none
      let some cells ← stackOfName n | return none
      return cells[k]?
  | _ => return none

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
        if let some ga ← gaddrOf e then
          if ga.base.isSome then return ← materialize ga
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
    | .listComp .. => fail "a list comprehension is only a keccak_cells argument"

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
    if callee == "keccak" || callee == "keccak_cells" then
      fail s!"{callee} is a statement: it writes the state or the digest into its `out` run"
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
    if callee == "keccak" || callee == "keccak_cells" then
      fail s!"{callee} is a statement, not a value-returning call"
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
      fail s!"`@inline {callee}` requires one tail `return`, with no nested returns or mul_range loops"
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

/-- A branch body, its bindings and its padding run local (`branch`, `scoped`). -/
def branch : Nat → Seg → List Source.Stmt → M (List Core.Stmt)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, seg, body => do
    let saved := (← get).names
    let pad := (← get).keccakPad
    let (consts, mats) := ((← get).consts, (← get).mats)
    let ((), _, blk) ← capture <| withSeg seg do
      stmts n body
      if (← get).pending then anchor
    modify fun st => { st with names := saved, keccakPad := pad, consts, mats }
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
          match ← gaddrOf b with
          | some ⟨some c, j + 1, none⟩ => materialize ⟨some c, j, none⟩
          | _ => do
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
    -- A chained `match` is entered from the previous one's arms: its scrutinee is the free
    -- cell the chain named, and nothing is set above its arms (`lower_match`).
    let (chainNext, chainIn) := ((← get).chainNext, (← get).chainIn)
    modify fun st => { st with chainNext := none, chainIn := none }
    let xo ← match chainIn with
      | some c => pure c
      | none => expr n x
    let (rcells, binds) ← retTargets targets
    -- Arms that are all `@inline` calls: the padding run and a two-to-one hash's closing lane
    -- are set once above the dispatch (`lower_match`), unless the match is entered.
    if chainIn.isNone && (← arms.allM isInlineArm) then
      discard keccakPadRun
      discard <| constCell twoToOneClose
    let mut blocks := #[]
    for (j, arm) in (List.range arms.length).zip arms do
      let saved := (← get).names
      let pad := (← get).keccakPad
      let (consts, mats) := ((← get).consts, (← get).mats)
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
      modify fun st => { st with names := saved, keccakPad := pad, consts, mats }
      blocks := blocks.push blk
    emit (.match_ xo blocks.toList)
    -- Chained: every arm ends in the next match's dispatch (`lower_match_dispatch`).
    modify fun st => { st with chainIn := chainNext }
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
    -- A captured `StackBuf` becomes a `StackBuf(n)` parameter, which each iteration's
    -- self-call copies on, cell by cell.
    let mut captures : Array (String × Shape) := #[]
    for r in refs do
      if bound.contains r then continue
      if let some cells ← stackOfName r then
        if !shadowed.contains r then
          if !captures.any (·.1 == r) then captures := captures.push (r, .stackBuf cells.length)
          continue
      match ← lookup r with
      | some ⟨.scalar _, _⟩ | some ⟨.gaddr _, _⟩ | some ⟨.fconst _, _⟩ =>
          if !captures.any (·.1 == r) then captures := captures.push (r, .scalar)
      | _ => pure ()
    let runtime := match hi with | .runtime _ => true | .const _ => false
    let params := [(var, Shape.scalar)] ++ (if runtime then [(boundVar, Shape.scalar)] else []) ++
      captures.toList
    let capArgs : Expr → Expr → List Expr := fun first b =>
      [first] ++ (if runtime then [b] else []) ++ captures.toList.map (.var ·.1)
    let nextVar := s!"__next{id}"
    let loopBody := body ++ [
      .mk line (.let_ nextVar (.mul (.var var) .gen)),
      .mk line (.callIfNe (.var nextVar) exit loopName (capArgs (.var nextVar) (.var boundVar))),
      .mk line (.ret [])]
    let helper : Func := { name := loopName, params := params.map fun q => ⟨q.1, .runtime q.2⟩,
                           returnShapes := [], body := loopBody, inline := false }
    modify fun st => { st with queue := st.queue.push helper }
    match hi with
    | .const h =>
        if lo != h then
          discard <| call n loopName (capArgs (.gpow lo) (.gpow h)) 0
    | .runtime _ =>
        stmtKind n line (.callIfNe (.gpow lo) entryBound loopName (capArgs (.gpow lo) entryBound))

/-- The Keccak builtins, `assert_in_k` and the hints (`lower_builtin`); `false` for another
callee. -/
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
    | "hint_windows_exponent" => do
        if !(args.length == 5 || args.length == 6) then
          fail s!"{f} takes `(dest, value, start, width, count[, at])`, got {args.length} arguments"
        let start ← constIndex args[2]!
        let width ← constIndex args[3]!
        let count ← constIndex args[4]!
        if !(1 ≤ width && width ≤ 16) || 192 < start + width * count then
          fail s!"{f}: windows of 1..=16 bits inside a 192-bit word"
        let skip ← match args[5]? with
          | some a => constIndex a
          | none => pure 0
        let dest ← bitsDest n args[0]! (skip + count)
        let value ← expr n args[1]!
        let dest : Dest := match dest with
          | .stack cells => .stack (cells.drop skip)
          | .heap p off len => .heap p (off + skip) (len - skip)
        emitHint (.windowsExp value start width count dest)
        return true
    | "hint_decompose_digits_exponent" => do
        let [a0, a1, a2, a3, a4, a5] := args
          | fail s!"{f} takes `(dest, value, nbits, ndigits, digit_bits, start)`, got {args.length} arguments"
        let nbits ← constIndex a2
        let ndigits ← constIndex a3
        let digitBits ← constIndex a4
        if 64 < nbits || !(1 ≤ digitBits && digitBits ≤ 16) then
          fail s!"{f}: nbits <= 64 and 1 <= digit_bits <= 16"
        let dst ← bitsDest n a0 ndigits
        let value ← expr n a1
        let (start, startCell) ← match ← tryConstIndex a5 with
          | some k => pure (k, none)
          | none => do pure (0, some (← expr n a5))
        emitHint (.digitsExp value nbits ndigits digitBits start startCell dst)
        return true
    | "assert_gpow" => do
        -- One `DEREF` through `x` into a fresh touch cell: `x = g^e` with `e < 2^h`.
        let [a0] := args | fail "assert_gpow(x) takes one scalar cell"
        let x ← expr n a0
        let t ← fresh
        emitAtom (.touch t x)
        return true
    | "keccak" => do
        lowerKeccak n args
        return true
    | "keccak_cells" => do
        lowerKeccakCells n args
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

/-- `N` message cells of a `keccak` operand (`keccak_words`): a list literal of `N` words (a
literal `0` a known zero), or a run of `N` cells, a heap run bridged through fresh values, one
`DEREF` each. -/
def keccakWords : Nat → Nat → Expr → M (List SpongeCell)
  | 0, _, _ => fail "expansion fuel exhausted"
  | n + 1, N, e => do
    if let .list ws := e then
      if ws.length != N then
        fail s!"a keccak operand written as a list needs exactly {N} words, got {ws.length}"
      return ← ws.mapM fun w => do
        if (← tryConstInt w) == some 0 then return SpongeCell.zero
        return .cell (← expr n w)
    match ← cellRun n e with
    | .stack cells =>
        if cells.length == N then return cells.map .cell
        fail s!"this keccak operand spans exactly {N} cells"
    | .heap ptr lo len => do
        if len != N then fail s!"this keccak operand spans exactly {N} cells"
        let t ← freshRun N
        for (d, k) in t.zipIdx do emitAtom (.load d ptr (lo + k))
        return t.map .cell

/-- `cellRun`, or `none` for an expression that names no run (`try_cell_run`). -/
def tryCellRun : Nat → Expr → M (Option CellRun)
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    match e with
    | .var _ | .slice .. => return some (← cellRun n e)
    | _ => return none

/-- Where a `keccak` writes (`keccak_out`): a stack run of one or two cells, in place, or of at
least thirteen, its first thirteen; else fresh values for a heap run of one, two or thirteen cells,
copied there afterwards. The `KECCAK` writes exactly the cells the destination holds. -/
def keccakOut : Nat → Expr → M KeccakOut
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, e => do
    let run ← cellRun n e
    match run with
    | .stack cells =>
        if stateCells ≤ cells.length then return ⟨cells.take stateCells, none⟩
        if cells.length == 1 || cells.length == 2 then return ⟨cells, none⟩
    | .heap ptr lo len =>
        if len == stateCells || len == 1 || len == 2 then return ⟨← freshRun len, some (ptr, lo)⟩
    fail s!"a keccak destination is a {stateCells}-cell run (the state), a 2-cell run (the \
      digest) or a 1-cell run (its first cell)"

/-- `pad_tail=1` (`pad_tail_in_place`): set the cells of the `tail` slice from `len` on to the
padding (its first byte, then zeros), so the message is read in place instead of copied into a
padded run. The slice must be a `StackBuf`'s, `len` must end one of its cells, and `a` and `b`
must not read the cells it sets. -/
def padTailInPlace : Nat → List (String × Expr) → List SpongeCell → Nat → M Unit
  | 0, _, _, _ => fail "expansion fuel exhausted"
  | n + 1, kwargs, cells, len => do
    let tailStart := 4
    let some e := kwGet kwargs "pad_tail" | fail "keccak pad_tail= takes 1"
    if (← tryConstInt e) != some 1 then fail "keccak pad_tail= takes 1"
    let some tailCells ← (match kwGet kwargs "tail" with
        | some tail => do
            match ← tryCellRun n tail with
            | some (.stack cs) => pure (some cs)
            | _ => pure none
        | none => pure none)
      | fail "keccak pad_tail=1 needs tail= a StackBuf slice"
    let past := len / 16
    if len % 16 != 0 || !(tailStart ≤ past && past < cells.length) then
      fail s!"keccak pad_tail=1 needs len= ending a tail cell (64, 80, 96 or 112), got {len}"
    let set := (tailCells.drop (past - tailStart)).take (cells.length - past)
    if (cells.take tailStart).any fun | .cell o => set.contains o | _ => false then
      fail "keccak pad_tail=1: a or b reads a cell past len, which the padding sets"
    for (o, k) in set.zipIdx do
      emitAtom (.const o (if k = 0 then keccakPadValue else 0))

/-- `keccak(a, b, out, tail=, len=, cap=, pad_tail=)` (`lower_keccak`): the Keccak-256 of the first `len`
bytes of `a ‖ b ‖ tail`, one `KECCAK`; with `cap=`, the duplex step in overwrite mode, the eight
message cells over the zero padding and the five cells a previous output ends with; with
`pad_tail=1`, the padding set in the tail's cells (`padTailInPlace`). -/
def lowerKeccak : Nat → List Expr → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, args => do
    let kwargs ← keccakKwargs args "keccak" ["a", "b", "out"] ["tail", "len", "cap", "pad_tail"]
    let a ← keccakWords n 2 (args.getD 0 default)
    let b ← keccakWords n 2 (args.getD 1 default)
    let mut cells := a ++ b
    if let some tail := kwGet kwargs "tail" then
      cells := cells ++ (← keccakWords n 4 tail)
    if let some cap := kwGet kwargs "cap" then
      if (kwGet kwargs "len").isSome then
        fail "keccak cap= is an overwrite duplex step: it takes no len="
      let bad : M (List V) :=
        fail s!"keccak cap= must be a previous {stateCells}-cell output or its last five cells"
      let capRun ← match ← tryCellRun n cap with
        | some (.stack cs) =>
            if cs.length == stateCells then pure (cs.drop 8)
            else if cs.length == 5 then pure cs
            else bad
        | some (.heap ptr lo len) =>
            if len == stateCells || len == 5 then do
              let run ← freshRun 5
              for (d, k) in run.zipIdx do emitAtom (.load d ptr (lo + len - 5 + k))
              pure run
            else bad
        | none => bad
      cells := cells ++ List.replicate (8 - cells.length) SpongeCell.zero
      let out ← keccakOut n (args.getD 2 default)
      let (m, tail) ← keccakRate cells none
      emitAtom (.keccak (m ++ tail ++ capRun) out.state false false)
      keccakFinish out
      return
    let len ← keccakLen kwargs cells.length
    let padded := (kwGet kwargs "pad_tail").isSome
    if padded then padTailInPlace n kwargs cells len
    let out ← keccakOut n (args.getD 2 default)
    emitKeccakMessage cells (some len) none out.state padded
    keccakFinish out

/-- `keccak_cells(cells, out, state=, len=, final=)` (`lower_keccak_cells`): the Keccak-256 of the
first `len` bytes the cells hold, 136 bytes a `KECCAK`, continuing the 13-cell `state` if given;
`final=0` absorbs the cells zero-extended to whole blocks, unpadded. -/
def lowerKeccakCells : Nat → List Expr → M Unit
  | 0, _ => fail "expansion fuel exhausted"
  | n + 1, args => do
    let kwargs ← keccakKwargs args "keccak_cells" ["cells", "out"] ["state", "len", "final"]
    let list ← match args.getD 0 default with
      | .listComp body var lo hi => do
          let some l ← tryConstInt lo
            | fail "a list comprehension's bounds must be compile-time integers"
          let some h ← tryConstInt hi
            | fail "a list comprehension's bounds must be compile-time integers"
          pure (Expr.list ((List.range' l (h - l)).map fun i => body.subst var (.lit i)))
      | e => pure e
    let cells : List SpongeCell ← match list with
      | .list ws => ws.mapM fun w => do
          if (← tryConstInt w) == some 0 then return SpongeCell.zero
          return .cell (← expr n w)
      | e => do
          match ← cellRun n e with
          | .stack cs => pure (cs.map .cell)
          | .heap ptr lo len => do
              let t ← freshRun len
              for (d, k) in t.zipIdx do emitAtom (.load d ptr (lo + k))
              pure (t.map .cell)
    if cells.isEmpty then fail "keccak_cells hashes at least one cell"
    let isFinal ← match kwGet kwargs "final" with
      | some e => do
          let some k ← tryConstInt e | fail "keccak `final` must be a compile-time integer"
          pure (k != 0)
      | none => pure true
    let finalLen ← if isFinal then some <$> keccakLen kwargs cells.length else do
      if (kwGet kwargs "len").isSome then
        fail "keccak_cells final=0 absorbs whole cells: it takes no len="
      pure none
    let bad : M (Option (List V)) :=
      fail s!"keccak_cells state= must be the {stateCells}-cell run a previous keccak wrote"
    let state ← match kwGet kwargs "state" with
      | none => pure none
      | some st => do
          match ← tryCellRun n st with
          | some (.stack cs) =>
              if stateCells ≤ cs.length then pure (some (cs.take stateCells)) else bad
          | some (.heap ptr lo len) =>
              if len == stateCells then do
                let s ← freshRun stateCells
                for (d, k) in s.zipIdx do emitAtom (.load d ptr (lo + k))
                pure (some s)
              else bad
          | none => bad
    let out ← keccakOut n (args.getD 1 default)
    emitKeccakMessage cells finalLen state out.state false
    keccakFinish out

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
        -- Back-to-back dispatches chain: each arm of one enters the next (`unroll`).
        let iters := (List.range' l (h - l)).map fun j => (j, Source.Stmt.substList var (.lit j) body)
        let flat := iters.flatMap fun (j, ss) => ((List.range ss.length).zip ss).map fun (i, s) => (j, i, s)
        let nexts := (flat.drop 1).map (some ·.2.2) ++ [none]
        let mut blocks := #[]
        let mut k := 0
        for (j, ss) in iters do
          let here := (flat.zip nexts).drop k |>.take ss.length
          k := k + ss.length
          let blk ← capture <| withSeg (.u j) do
            for ((_, i, s), nx) in here do
              if let .match_ targets _ arms := s.kind then
                if let some nxs := nx then
                  if let .match_ _ nxx narms := nxs.kind then
                    if (← allInline arms) && (← allInline narms) then
                      if let some c ← freeCell nxx targets then
                        modify fun st => { st with chainNext := some c }
              withSeg (.s i) (stmtKind n s.line s.kind)
          blocks := blocks.push blk
        appendBlocks (blocks.toList.map fun ((), pd, b) => (pd, b))

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
    pending := false, inlineRet := none, inlineStackRet := none, inlineCalls := [],
    keccakPad := none, queue,
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
