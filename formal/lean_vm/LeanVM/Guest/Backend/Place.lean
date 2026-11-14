/-
  LeanVM.Guest.Backend.Place

  Cell placement: a core function to its placed function, every value in the frame cell the Rust
  lowering gives it (`crates/lean_compiler/src/lower.rs`, `lower/*.rs`).
-/

module

public import LeanVM.Guest.Backend.Ir
public import LeanVM.Guest.Backend.Trace
public import LeanVM.Guest.Word
public import Std.Data.TreeMap
public import Std.Data.HashMap

/-!
# Placement

`placeFn` walks a core function once, with its allocation trace (`Trace`), as `lower_func` walks
the source, and keeps what the lowering keeps: the next free cell (`next`, a bump allocator that
a `match` rewinds for each arm), the place of every value made so far (`locs`), the pools of the
current scope (`Scope`: constants, pure results, loads, shifted pointers, the frame's own
pointer), which revert at the end of a branch or an arm, the hints waiting for the next
instruction, and the jump tables' length.

**The walk.** The trace lists what the expansion did in order, so the two are read together: a
core statement is its `emit` event, a branch or an arm the events from its `enter` to its `leave`.
Before each statement and at the end of each block, `flush` takes the cells of the values made
since (`Event.alloc`), in the trace's order: a `Kind.cell` value takes the next free cells now.
Then the statement takes the cells of its own plumbing (a pooled `1`, a callee's frame pointer and
entry, a jump target), which are in no trace because they are no value.

**Pools.** A `Kind.pooled` value is the result of the statement that follows it, and the lowering
asks a pool first: `const` (`const_cell`), `add` and `mul` (`pure`), `load` (`load_cells`). On a
hit the value is placed in the pooled cell and nothing is emitted; on a miss it takes the next
free cell, the instruction is emitted and the pool learns it. A statement whose result has its
cells already writes them and asks no pool (`expr_into`, a store, `xor_byte`).

**Addresses.** An `addr` pointer is held in no cell (`Loc.shifted`): a `DEREF` through it folds
its offset into the immediate, and it becomes a product only where it is used as a value
(`Event.use`, `Event.shift`; `materialize`).

Invariants a placement is meant to maintain, the statements a correctness proof starts from (none
is proved here):

* `locs` only grows, and a value's place never changes;
* a cell below `next` is never given to two `Kind.cell` values of one path of the control flow
  (the arms of a `match` share cells, one arm running);
* two values share a cell only through a pool, whose entry was written by an instruction that
  runs before the reuse on every path, the scope reverting at each join: so they hold one word;
* `(placeFn …).frameSize` is past every cell the placed statements name.

Placement fails, rather than guess, when the trace and the core function part (`expect`) or a
statement names a value the trace gave no cell (`cellAt`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- Where a value is. -/
inductive Loc where
  | cell (n : Cell)
  /-- In no cell: the word of cell `n` times `g^exp`. An `addr` pointer is the frame pointer's
  cell shifted by its run's offset (`stack_addr`). -/
  | shifted (n : Cell) (exp : Nat)
  deriving Inhabited

/-- The order of pairs, for the pools. -/
def cmp2 (a b : Nat × Nat) : Ordering := (compare a.1 b.1).then (compare a.2 b.2)

/-- A pool keyed by a pair. -/
abbrev Pool := Std.TreeMap (Nat × Nat) Cell cmp2

/-- What a branch may not have run (`Scope`, without the name bindings). -/
structure Scope where
  /-- Constants by their limbs (`const_cells`). -/
  consts : Pool := {}
  /-- `XOR`s by their sorted operands (`pure_cells`). -/
  xors : Pool := {}
  /-- `MUL`s by their sorted operands (`pure_cells`). -/
  muls : Pool := {}
  /-- Loads by pointer cell and offset (`load_cells`). -/
  loads : Pool := {}
  /-- Shifted pointers by base cell: `(exp, cell)` (`mat_cells`). -/
  mats : Std.TreeMap Nat (List (Nat × Cell)) := {}
  /-- The cell holding this frame's pointer (`self_fp_off`). -/
  selfFp : Option Cell := none
  deriving Inhabited

/-- A `mul_range` helper, as the lowering's `loop_bounds` holds it. -/
structure LoopInfo where
  /-- Its frames are reserved in one run. -/
  registered : Bool
  /-- The exponent of a constant exit bound. -/
  hi : Option Nat
  deriving Inhabited

/-- The program's loop helpers. -/
abbrev Loops := Std.HashMap String LoopInfo

/-- Whether a function is a loop helper, by the compiler's name for it. -/
def isLoopName (f : String) : Bool := f.startsWith "__loop"

/-- The program's loop helpers (`loop_bounds`). -/
def loopTable (fns : List TracedFn) : Loops :=
  fns.foldl (init := {}) fun table tf =>
    if isLoopName tf.core.name then
      let (registered, hi) := loopSource tf.src
      table.insert tf.core.name ⟨registered, hi⟩
    else table

/-- The function being placed. -/
structure Ctx where
  name : String
  isMain : Bool
  /-- Its argument cells (`Abi::arg_cells`). -/
  argCells : Nat
  loops : Loops
  trace : Array Event

/-- The jump tables' state, threaded through the program (`JumpTables`). -/
structure Tables where
  /-- The slots given out so far. -/
  len : Nat := 0
  /-- The table of each dispatched call's callees (`shared`). -/
  shared : List (List String × Nat) := []
  /-- The slots of the shared tables: `(slot, callee)`. -/
  entries : Array (Nat × String) := #[]
  deriving Inhabited

/-- The placement state. -/
structure St where
  next : Cell
  locs : Std.HashMap V Loc := {}
  scope : Scope := {}
  pending : Array LHint := #[]
  out : Array PStmt := #[]
  tables : Tables
  /-- The next event of the trace. -/
  pos : Nat := 0
  /-- The value the next statement makes, a pool asked first or an `addr` pointer. -/
  lazy : Option (V × Kind) := none
  /-- The values wanted in a cell by the next statement (`Event.use`). -/
  used : List V := []
  /-- The pointer and shift of the next `addr` value (`Event.shift`). -/
  shift : Option (V × Nat) := none
  /-- The next `match` chains into the one after it (`Event.chain`). -/
  chain : Bool := false
  /-- The offset of the next `hint_windows_exponent` (`Event.note`). -/
  note : Nat := 0
  /-- Set for a `match` the previous one's arms dispatch into: its table and the join cell. -/
  chainIn : Option (Nat × Cell) := none
  /-- The padding run being set. -/
  padRun : Option (List Seg × Nat) := none
  /-- The message run read in place, whose copies are dropped. -/
  aliasRun : Option (List Seg × Nat) := none
  /-- The constant of each value a `SET` made. -/
  constOf : Std.HashMap V (Nat × Nat) := {}

/-- The placement monad. -/
abbrev P := ReaderT Ctx (StateT St (Except String))

/-- A placement error, naming the function. -/
def failP {α : Type} (msg : String) : P α := do
  throw s!"in {(← read).name}: {msg}"

/-! ## Cells -/

/-- The next cell (`fresh`). -/
def fresh : P Cell :=
  modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- Queue a hint for the next instruction. -/
def pushHint (h : LHint) : P Unit :=
  modify fun s => { s with pending := s.pending.push h }

/-- The hints waiting, for the instruction about to be emitted. -/
def takeHints : P (List LHint) :=
  modifyGet fun s => (s.pending.toList, { s with pending := #[] })

/-- Emit a placed statement. -/
def push (s : PStmt) : P Unit :=
  modify fun st => { st with out := st.out.push s }

/-- Emit one instruction, with the hints waiting (`emit`). -/
def emitOp (o : LOp) : P Unit := do
  let hints ← takeHints
  push (.op hints o)

/-- Place the `len` values of a run in the cells from `base`. -/
def bindRun (v : V) (len : Nat) (base : Cell) : P Unit :=
  modify fun s => { s with
    locs := (List.range len).foldl (init := s.locs) fun m k =>
      m.insert ⟨v.path, v.tag, k⟩ (.cell (base + k)) }

/-- Place a run in the next free cells (`alloc_stack`). -/
def takeRun (v : V) (len : Nat) : P Unit := do
  let base := (← get).next
  bindRun v len base
  modify fun s => { s with next := base + len }

/-- The cell of a value held in one. -/
def cellAt (v : V) : P Cell := do
  match (← get).locs[v]? with
  | some (.cell n) => pure n
  | _ => failP "a value with no cell"

/-- Give a value its place. -/
def bindTo (v : V) (l : Loc) : P Unit :=
  modify fun s => { s with locs := s.locs.insert v l }

/-- Whether the statement being placed makes this value (`Kind.pooled`, `Kind.addr`). -/
def isLazy (v : V) (kind : Kind) : P Bool :=
  return (← get).lazy == some (v, kind)

/-! ## Pools -/

/-- The sorted pair of a commutative operation's operands. -/
def sorted (a b : Cell) : Nat × Nat := (min a b, max a b)

/-- A cell holding the constant of these limbs (`const_cell`). -/
def constCell (k : Nat × Nat) : P Cell := do
  match (← get).scope.consts.get? k with
  | some o => pure o
  | none =>
      let o ← fresh
      emitOp (.set o (.const k.1 k.2))
      modify fun s => { s with scope.consts := s.scope.consts.insert k o }
      pure o

/-- A cell holding `1` (`one`). -/
def oneCell : P Cell := constCell (1, 0)

/-- A cell holding `0` (`zero`). -/
def zeroCell : P Cell := constCell (0, 0)

/-- The cell holding `a · b` (`pure`). -/
def mulCell (a b : Cell) : P Cell := do
  match (← get).scope.muls.get? (sorted a b) with
  | some o => pure o
  | none =>
      let o ← fresh
      emitOp (.mul a b o)
      modify fun s => { s with scope.muls := s.scope.muls.insert (sorted a b) o }
      pure o

/-- A `DEREF` of a cell: it is a load the scope remembers (`deref`). -/
def emitDeref (ptr : Cell) (off : Nat) (dst : Cell) : P Unit := do
  emitOp (.deref ptr off dst .cell)
  modify fun s => { s with scope.loads := s.scope.loads.insertIfNew (ptr, off) dst }

/-- A cell holding this frame's pointer (`self_fp`): in `main` the cell holding `1`; else read
back from a one-cell buffer the pointer is stored to. -/
def selfFp : P Cell := do
  if (← read).isMain then return ← oneCell
  match (← get).scope.selfFp with
  | some o => pure o
  | none =>
      let q ← fresh
      pushHint (.resolved (.alloc q 1))
      emitOp (.deref q 0 0 .fp)
      let o ← fresh
      emitOp (.deref q 0 o .cell)
      modify fun s => { s with scope.selfFp := some o }
      pure o

/-- The limbs of `g^e`. -/
def gpowLimbs (e : Nat) : Nat × Nat := ((gpowK e).toBitVec.toNat, 0)

/-- The β-immediate cap (`FOLD_MAX`). -/
def foldMaxExp : Nat := 2 ^ 16

/-- A cell holding `c · g^exp` for the pointer in cell `c` (`materialize`): `c` itself, a
product made before, or a product from `c` or the nearest shifted pointer below whose distance is
a constant already set. -/
def materialize (c : Cell) (exp : Nat) : P Cell := do
  if exp = 0 then return c
  let sc := (← get).scope
  let mats := (sc.mats.get? c).getD []
  if let some (_, o) := mats.find? (·.1 == exp) then return o
  let has := fun (e : Nat) => sc.consts.contains (gpowLimbs e)
  let start : Option (Nat × Cell) :=
    if has exp then none
    else ((0, c) :: mats).foldl (init := none) fun best (e, src) =>
      if e < exp && has (exp - e) && best.all (·.1 ≤ e) then some (e, src) else best
  let (src, dist) := match start with
    | some (e, src) => (src, exp - e)
    | none => (c, exp)
  let k ← constCell (gpowLimbs dist)
  let o ← mulCell src k
  modify fun s => { s with scope.mats := s.scope.mats.insert c (mats ++ [(exp, o)]) }
  pure o

/-- The cell of a value an instruction reads: an address is the product made of it. -/
def cellOf (v : V) : P Cell := do
  match (← get).locs[v]? with
  | some (.cell n) => pure n
  | some (.shifted n exp) => materialize n exp
  | none => failP "a value with no place"

/-- A value as a factor: a cell and the shift still to apply, an address not wanted in a cell
keeping its shift for the `DEREF` that reads through the product (`heap_addr`). -/
def factor (v : V) : P (Cell × Nat) := do
  let st ← get
  match st.locs[v]? with
  | some (.shifted n exp) => if st.used.contains v then return (← materialize n exp, 0) else return (n, exp)
  | _ => return (← cellOf v, 0)

/-- The pointer cell and offset of a `DEREF` through `p · g^off`: an address folds its shift into
the immediate (`heap_base`). -/
def pointer (p : V) (off : Nat) : P (Cell × Nat) := do
  let (n, exp) ← factor p
  if exp != 0 && foldMaxExp < exp + off then failP "a frame address past the largest DEREF immediate"
  return (n, exp + off)

/-- The cell of a result the lowering takes from a pool: the pooled cell under `find`, or the
next free cell, which `mk` writes and `learn` records. -/
def pooledCell (find : Scope → Option Cell) (learn : Cell → Scope → Scope) (mk : Cell → LOp) :
    P Cell := do
  match find (← get).scope with
  | some o => pure o
  | none =>
      let o ← fresh
      emitOp (mk o)
      modify fun s => { s with scope := learn o s.scope }
      pure o

/-- Place a value this statement makes from a pool. -/
def pooled (d : V) (find : Scope → Option Cell) (learn : Cell → Scope → Scope) (mk : Cell → LOp) :
    P Unit := do
  bindTo d (.cell (← pooledCell find learn mk))

/-! ## The trace -/

/-- The event the walk is at. -/
def peek : P (Option Event) := do
  return (← read).trace[(← get).pos]?

/-- Pass the event the walk is at. -/
def advance : P Unit :=
  modify fun s => { s with pos := s.pos + 1 }

/-- Four message cells already in consecutive frame cells are read in place (`sponge_run`): the
next statements copy them into the run `v`, cell by cell. -/
def spongeInPlace (v : V) (len : Nat) (upcoming : List Stmt) : P (Option Cell) := do
  let st ← get
  let srcs := (upcoming.take len).zipIdx.filterMap fun
    | (.atom (.copy d s), k) =>
        if d == ⟨v.path, v.tag, k⟩ then
          match st.locs[s]? with
          | some (.cell n) => some n
          | _ => none
        else none
    | _ => none
  match srcs with
  | [] => return none
  | base :: _ =>
      return if len != 0 && srcs.length == len && srcs.zipIdx.all (fun (n, k) => n == base + k)
        then some base else none

/-- A value is made (`Event.alloc`). -/
def onAlloc (v : V) (len : Nat) (kind : Kind) (upcoming : List Stmt) : P Unit := do
  match kind with
  | .cell => takeRun v len
  | .pooled | .addr => modify fun s => { s with lazy := some (v, kind) }
  | .site => pure ()
  | .ret => bindRun v len (2 + (← read).argCells)
  | .padRun =>
      takeRun v len
      modify fun s => { s with padRun := some (v.path, v.tag) }
  | .spongeRun =>
      match ← spongeInPlace v len upcoming with
      | some base =>
          bindRun v len base
          modify fun s => { s with aliasRun := some (v.path, v.tag) }
      | none => takeRun v len

/-- Take the cells of the values made before the next statement or the end of the block; at most
`fuel` events. `upcoming` are the statements from the next one on. -/
def flushN (upcoming : List Stmt) : Nat → P Unit
  | 0 => pure ()
  | fuel + 1 => do
      match ← peek with
      | some (.alloc v len kind) =>
          advance
          onAlloc v len kind upcoming
          flushN upcoming fuel
      | some (.use v) =>
          advance
          if let some (.shifted n exp) := (← get).locs[v]? then discard <| materialize n exp
          modify fun s => { s with used := v :: s.used }
          flushN upcoming fuel
      | some (.shift v exp) =>
          advance
          modify fun s => { s with shift := some (v, exp) }
          flushN upcoming fuel
      | some .chain =>
          advance
          modify fun s => { s with chain := true }
          flushN upcoming fuel
      | some (.note n) =>
          advance
          modify fun s => { s with note := n }
          flushN upcoming fuel
      | _ => pure ()

/-- `flushN`, to the next statement or block. -/
def flush (upcoming : List Stmt) : P Unit := do
  flushN upcoming ((← read).trace.size)

/-- Pass the event `e`, which the walk must be at. -/
def expect (e : Event → Bool) (what : String) : P Unit := do
  match ← peek with
  | some ev => if e ev then advance else failP s!"the trace is not at {what}"
  | none => failP s!"the trace ends before {what}"

def isEmit : Event → Bool
  | .emit => true
  | _ => false

def isEnter : Event → Bool
  | .enter => true
  | _ => false

def isLeave : Event → Bool
  | .leave => true
  | _ => false

/-- A statement begins: the values made before it, then its own `emit`. -/
def beginStmt (upcoming : List Stmt) : P Unit := do
  flush upcoming
  expect isEmit "a statement"

/-- A statement ends. -/
def endStmt : P Unit :=
  modify fun s => { s with lazy := none, used := [], shift := none }

/-! ## Atoms -/

/-- A hint's destination as the cells it names. -/
def destBits : Dest → P BitsDest
  | .stack cells => do
      match cells.head? with
      | some c => return .stack (← cellAt c)
      | none => failP "a hint with no destination"
  | .heap p _ _ => return .heap (← cellOf p)

/-- A hint (`RHint`), queued for the next instruction. -/
def placeHint : Hint → P Unit
  | .witness s (.stack cells) => do
      match cells.head? with
      | some c => pushHint (.resolved (.witnessStack s (← cellAt c) cells.length))
      | none => failP "a witness with no destination"
  | .witness s (.heap p off len) => do
      let (ptr, lo) ← pointer p off
      pushHint (.resolved (.witnessHeap s ptr lo len))
  | .bits value start nbits dest => do
      if start != 0 then failP "hint_decompose_bits from a later bit has no runtime hint"
      let b ← destBits dest
      pushHint (.resolved (.bitDecompose (← cellOf value) b nbits))
  | .bitsExp value nbits dest => do
      let b ← destBits dest
      pushHint (.resolved (.bitDecomposeExp (← cellOf value) b nbits))
  | .digitsExp value nbits ndigits digitBits start startCell dest => do
      let b ← destBits dest
      let v ← cellOf value
      let sc ← startCell.mapM cellOf
      pushHint (.resolved (.digitDecomposeExp v b nbits ndigits digitBits start sc))
  | .windowsExp value start width count dest => do
      -- The expansion folded the hint's `at` into `dest`: the trace's note gives it back.
      let skip := (← get).note
      let b ← match dest with
        | .stack cells =>
            match cells.head? with
            | some c => pure (BitsDest.stack ((← cellAt c) - skip))
            | none => failP "a hint with no destination"
        | .heap p _ _ => pure (BitsDest.heap (← cellOf p))
      pushHint (.resolved (.windowsExp (← cellOf value) b skip start width count))
  | .limbs value dest => do
      let v ← cellOf value
      match dest.head? with
      | some c => pushHint (.resolved (.fieldLimbs v (← cellAt c) dest.length))
      | none => failP "a hint with no destination"
  | .log2Ceil bits nbits floor dst => do
      let b ← destBits bits
      pushHint (.resolved (.log2Ceil b (← cellAt dst) nbits floor))
  | .inverse x dst => do
      let lx ← cellOf x
      pushHint (.resolved (.inverse lx (← cellAt dst)))
  | .alloc d size => do
      pushHint (.resolved (.alloc (← cellAt d) size))
  | .allocDyn d size => do
      let ls ← cellOf size
      pushHint (.resolved (.allocDyn (← cellAt d) ls))

/-- An atom. -/
def placeAtom (a : Atom) : P Unit := do
  match a with
  | .const d c =>
      let k := limbsOf c
      modify fun s => { s with constOf := s.constOf.insert d k }
      if ← isLazy d .pooled then
        pooled d (·.consts.get? k) (fun o sc => { sc with consts := sc.consts.insert k o })
          (fun o => .set o (.const k.1 k.2))
      else
        let o ← cellAt d
        emitOp (.set o (.const k.1 k.2))
        -- The padding run's cells are pooled constants too (`keccak_pad_run`).
        if (← get).padRun == some (d.path, d.tag) then
          modify fun s => { s with scope.consts := s.scope.consts.insertIfNew k o }
  | .add d a b =>
      let la ← cellOf a
      let lb ← cellOf b
      if ← isLazy d .pooled then
        pooled d (·.xors.get? (sorted la lb))
          (fun o sc => { sc with xors := sc.xors.insert (sorted la lb) o })
          (fun o => .xor la lb o)
      else
        emitOp (.xor la lb (← cellAt d))
  | .mul d a b =>
      if ← isLazy d .pooled then
        let (la, ea) ← factor a
        let (lb, eb) ← factor b
        let o ← pooledCell (·.muls.get? (sorted la lb))
          (fun o sc => { sc with muls := sc.muls.insert (sorted la lb) o })
          (fun o => .mul la lb o)
        bindTo d (if ea + eb == 0 then .cell o else .shifted o (ea + eb))
      else
        -- A store, or a division `d = a · b` whose quotient `a` is the fresh cell.
        let la ← cellOf a
        let lb ← cellOf b
        emitOp (.mul la lb (← cellAt d))
  | .copy d s =>
      let ls ← cellOf s
      if (← get).aliasRun == some (d.path, d.tag) then return
      let one ← oneCell
      emitOp (.mul ls one (← cellAt d))
  | .load d p off =>
      if ← isLazy d .pooled then
        let (ptr, o2) ← pointer p off
        pooled d (·.loads.get? (ptr, o2))
          (fun o sc => { sc with loads := sc.loads.insertIfNew (ptr, o2) o })
          (fun o => .deref ptr o2 o .cell)
      else
        -- A read into a cell given, or a store of the value `d`.
        let o ← cellOf d
        let (ptr, o2) ← pointer p off
        emitDeref ptr o2 o
  | .assertEq a b =>
      let la ← cellOf a
      let lb ← cellOf b
      let one ← oneCell
      emitOp (.mul la one lb)
  | .assertNe x inv p =>
      let lx ← cellOf x
      let li ← cellOf inv
      let lp ← cellAt p
      emitOp (.mul lx li lp)
      emitOp (.set lp (.const 1 0))
  | .rangeCheck x y t1 t2 k =>
      let lk ← cellOf k
      let lx ← cellOf x
      let ly ← cellAt y
      emitDeref lx 0 (← cellAt t1)
      emitOp (.mul lx ly lk)
      emitDeref ly 0 (← cellAt t2)
  | .assertInK a b =>
      let la ← cellOf a
      let lb ← cellOf b
      let zeroAt ← zeroCell
      emitOp (.jump zeroAt la lb)
  | .keccak ins outs inOdd outOdd =>
      let cs ← ins.mapM cellOf
      let some out := outs.head? | failP "a KECCAK with no output"
      let outCells : KeccakOutputCells :=
        if outs.length == 1 then .one else if outs.length == 2 then .two else .all
      let c := fun (i : Nat) => cs.getD i 0
      emitOp (.keccak (c 0) (c 1) (c 2) (c 3) (c 4) (c 8) (c 9) (← cellAt out) inOdd outOdd outCells)
  | .frameAddr p run =>
      if ← isLazy p .addr then
        -- `addr(run)`: the address stays symbolic (`stack_addr`).
        let some r0 := run.head? | failP "addr of no cell"
        let base ← cellAt r0
        bindTo p (.shifted (← selfFp) base)
      else
        -- An `addr` pointer shifted, as a value (`materialize`).
        match (← get).shift with
        | some (c, exp) =>
            match (← get).locs[c]? with
            | some (.shifted n e) => bindTo p (.cell (← materialize n (e + exp)))
            | _ => failP "a shifted pointer that is no address"
        | none => failP "an address with no pointer"
  | .hint h => placeHint h
  | .touch t p =>
      let lp ← cellOf p
      emitDeref lp 0 (← cellAt t)

/-! ## Statements -/

/-- Run `m` on the block the walk is at, into a block of its own with a scope of its own
(`scoped`): the pools revert after it, and a hint still waiting at its end gets an anchor. -/
def inBlock (m : P Unit) : P (List PStmt) := do
  expect isEnter "a block"
  let st ← get
  let (out, scope) := (st.out, st.scope)
  set { st with out := #[] }
  m
  flush []
  expect isLeave "the end of a block"
  if !(← get).pending.isEmpty then
    let o ← fresh
    emitOp (.set o (.const 0 0))
  let st ← get
  set { st with out, scope }
  return st.out.toList

/-- A table of `n` fresh slots (`slots.extend`). -/
def allocTable (n : Nat) : P Nat :=
  modifyGet fun s => (s.tables.len, { s with tables.len := s.tables.len + n })

/-- The table of a dispatched call's callees, shared by every call to the same ones. -/
def sharedTable (callees : List String) : P Nat := do
  let st ← get
  match st.tables.shared.find? (·.1 == callees) with
  | some (_, first) => pure first
  | none =>
      let first := st.tables.len
      set { st with tables := {
        len := first + callees.length,
        shared := (callees, first) :: st.tables.shared,
        entries := st.tables.entries ++
          (callees.zipIdx.map fun ((c, j) : String × Nat) => (first + j, c)).toArray } }
      pure first

/-- The exponent `k < limit` with `g^k` the word of these limbs. -/
def smallLog (limit : Nat) (limbs : Nat × Nat) : Option Nat :=
  if limbs.2 != 0 then none else go limit 0 1
where
  go : Nat → Nat → K → Option Nat
    | 0, _, _ => none
    | fuel + 1, k, x => if x.toBitVec.toNat == limbs.1 then some k else go fuel (k + 1) (x * g)

/-- The largest loop start looked for. -/
def loopLogLimit : Nat := 2 ^ 20

/-- The frames to reserve for a call into the loop helper `f` (`AllocLoopFrames`), from the
arguments of the call: the first is the constant `g^lo`, the second the runtime bound if the
loop has one. -/
def loopCount (f : String) (args : List V) (cells : List Cell) : P (Option LoopCount) := do
  let ctx ← read
  match ctx.loops[f]? with
  | some li =>
      if !li.registered then return none
      let st ← get
      let lo := (args.head?.bind fun a => st.constOf[a]?).bind (smallLog loopLogLimit)
      match lo, li.hi with
      | some lo, some hi => return some (.constant (hi - lo + 1))
      | some lo, none => return some (.bound (cells.getD 1 0) lo)
      | none, _ => failP s!"the start of loop {f} is not a constant power of g"
  | none => return none

/-- A call (`lower_call`), its arguments and returns placed. -/
def placeCall (f : String) (argVs : List V) (args rets : List Cell) (cond : Option Cell)
    (tail : Bool) : P Unit := do
  let nfp ← fresh
  let entry ← fresh
  let oc ← match cond with
    | some c => pure c
    | none => oneCell
  let hints ← takeHints
  let loop ← loopCount f argVs args
  push (.call hints { callee := f, nfp, entry, oc, args, rets, loop, tail })

/-- How an arm of a `match` leaves: to the join, or through the next `match`'s table. -/
inductive ArmExit where
  | join (join one sfp : Cell)
  | next (x : Cell) (first : Nat) (one sfp : Cell)

mutual
/-- A block. -/
def placeBlock : List Stmt → P Unit
  | [] => pure ()
  | s :: rest => do
      placeStmt s rest
      endStmt
      placeBlock rest

/-- A statement, `rest` the statements after it in its block. -/
def placeStmt : Stmt → List Stmt → P Unit
  | .atom a, rest => do
      beginStmt (.atom a :: rest)
      placeAtom a
  | .ite c z nz, _ => do
      flush []
      let lc ← cellOf c
      let sfp ← selfFp
      let one ← oneCell
      let bdest ← fresh
      let hints ← takeHints
      let zeroBlk ← inBlock (placeBlock z)
      -- An `else` block is in the trace even when it emits nothing.
      match ← peek with
      | some .enter =>
          let edest ← fresh
          let nonzero ← inBlock (placeBlock nz)
          expect isEmit "a branch"
          push (.ite hints lc bdest sfp zeroBlk true edest one nonzero)
      | _ =>
          expect isEmit "a branch"
          push (.ite hints lc bdest sfp zeroBlk false 0 0 [])
  | .match_ x arms, rest => do
      flush []
      let st ← get
      let (entered, chained) := (st.chainIn, st.chain)
      set { st with chainIn := none, chain := false }
      let lx ← cellOf x
      -- The next `match` is entered from these arms (`chain_next`).
      let nextSel ← if chained then
          match rest with
          | .match_ x' arms' :: _ => pure (some (← cellOf x', arms'.length))
          | _ => failP "a chained match followed by no match"
        else pure none
      let sfp ← selfFp
      let one ← oneCell
      let (join, first, head) ← match entered with
        | some (first, join) => pure (join, first, none)
        | none => do
            let join ← fresh
            let hints ← takeHints
            let first ← allocTable arms.length
            let entry ← fresh
            pure (join, first, some (hints, entry))
      let exit ← match nextSel with
        | some (x', n') => do pure (ArmExit.next x' (← allocTable n') one sfp)
        | none => pure (ArmExit.join join one sfp)
      let base := (← get).next
      let blocks ← placeArms arms 0 arms.length base exit
      expect isEmit "a match"
      match head with
      | some (hints, entry) => push (.chain hints join lx entry one sfp [first] [blocks])
      | none =>
          -- An entered `match` is one more stage of the chain before it.
          let st ← get
          match st.out.back? with
          | some (.chain h j x e o s firsts stages) =>
              let node := PStmt.chain h j x e o s (firsts ++ [first]) (stages ++ [blocks])
              set { st with out := st.out.pop.push node }
          | _ => failP "a chained match follows no match"
      match exit with
      | .next _ nf _ _ => modify fun s => { s with chainIn := some (nf, join) }
      | .join .. => pure ()
  | .call f args rets, rest => do
      beginStmt (.call f args rets :: rest)
      let las ← args.mapM cellOf
      let lrs ← rets.mapM cellAt
      placeCall f args las lrs none false
  | .callIf c f args, rest => do
      beginStmt (.callIf c f args :: rest)
      let lc ← cellOf c
      let las ← args.mapM cellOf
      let ctx ← read
      let self := f == ctx.name
      if self && (ctx.loops[f]?).any (·.registered) then
        -- The next frame of the run (`lower_call`, the loop arm).
        let ownFp ← selfFp
        let scale ← fresh
        emitOp (.set scale .frameSize)
        pushHint .nextFrameAddress
        let nfp ← mulCell ownFp scale
        let entry ← fresh
        let one ← oneCell
        let hints ← takeHints
        push (.loopNext hints f nfp entry lc one las)
      else placeCall f args las [] (some lc) self
  | .dispatch x fs args rets, rest => do
      beginStmt (.dispatch x fs args rets :: rest)
      let las ← args.mapM cellOf
      let lrs ← rets.mapM cellAt
      let lx ← cellOf x
      let one ← oneCell
      let nfp ← fresh
      let hints ← takeHints
      let joinCell ← fresh
      let first ← sharedTable fs
      let entry ← fresh
      push (.dispatch hints fs nfp joinCell lx entry one first las lrs)
  | .ret vs, rest => do
      beginStmt (.ret vs :: rest)
      let one ← oneCell
      if (← read).isMain then
        let dest ← fresh
        let hints ← takeHints
        push (.halt hints one dest)
      else
        let hints ← takeHints
        push (.ret hints one)

/-- The arms of a `match` from arm `j` of `n`, each from the cell `base` on (one arm runs, so
they share their cells) and in a scope of its own; `next` ends past the longest. -/
def placeArms : List (List Stmt) → Nat → Nat → Cell → ArmExit → P (List (List PStmt))
  | [], _, _, base, _ => do
      modify fun s => { s with next := base }
      pure []
  | arm :: more, j, n, base, exit => do
      modify fun s => { s with next := base }
      let blk ← inBlock (placeBlock arm)
      let leave ← match exit with
        | .next x first one sfp => do
            let e ← fresh
            pure [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)]
        | .join join one sfp =>
            pure (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else [])
      let top := (← get).next
      let blocks ← placeArms more (j + 1) n base exit
      modify fun s => { s with next := max s.next top }
      pure ((blk ++ leave) :: blocks)
end

/-! ## Functions -/

/-- A placed function with the place of each of its values: the valuation a correctness proof
reads the frame with, and what a certificate of the existing checker calls its cells
(`Check.Cert.locs`). -/
structure Placed where
  fn : PFn
  locs : Std.HashMap V Loc

/-- Place a function (`lower_func`): cells `0` and `1` hold the return target, then the
arguments, then the return cells, then a registered loop's own frame pointer, then the locals. -/
def placeFn (loops : Loops) (tables : Tables) (tf : TracedFn) :
    Except String (Placed × Tables) := do
  let f := tf.core
  let loopFrame := (loops[f.name]?).any (·.registered)
  let argCells := f.params.length
  let abiEnd := 2 + argCells + (tf.src.returnShapes.map Source.Shape.cells).sum
  let locs : Std.HashMap V Loc := f.params.zipIdx.foldl (init := {}) fun m (v, k) =>
    m.insert v (.cell (2 + k))
  let st : St := {
    next := abiEnd + (if loopFrame then 1 else 0), locs, tables,
    scope := { selfFp := if loopFrame then some abiEnd else none } }
  let ctx : Ctx := { name := f.name, isMain := f.name == "main", argCells, loops, trace := tf.trace }
  let walk : P Unit := do
    placeBlock f.body
    flush []
    if (← get).pos != tf.trace.size then failP "the trace goes on past the function"
  let ((), st) ← walk.run ctx |>.run st
  return (⟨{ name := f.name, body := st.out.toList, frameSize := st.next }, st.locs⟩, st.tables)

/-- Place a program, its functions in order: the jump tables grow as the lowering reaches each
`match`. -/
def placeProgram (p : List TracedFn) : Except String (List Placed × Tables) := do
  let loops := loopTable p
  let (fns, tables) ← p.foldlM (init := (#[], ({} : Tables))) fun (fns, tables) tf => do
    let (pf, tables) ← placeFn loops tables tf
    pure (fns.push pf, tables)
  return (fns.toList, tables)

end
end LeanVM.Guest.Backend
