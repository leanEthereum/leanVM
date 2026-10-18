/-
  LeanVM.Guest.Interp

  An executable interpreter of the core IR: it evaluates a function on given arguments, memory
  and hint streams, solving each atom for its one unknown as the Rust runner does, and checks
  every constraint on the way; and a printer of core functions.
-/

module

public import LeanVM.Guest.Core
public import Std.Data.HashMap

/-!
# The core IR interpreter

`run` evaluates a core function and returns its words, or the first constraint that fails. It
is the witness generation of `leanvm_core::cpu::execute` on the core IR: an atom whose inputs are
known computes its output, and one whose output is known back-solves its single unknown input
(`a / b` as `mul a q b`, the range check's complement, `a + b` with the sum known); a word read
through a pointer and the memory cell it names are unified, so a load before the store sees the
stored word. A second write of a value or a cell is the write-once check.

What the prover chooses comes from `Cfg`: the memory's initial contents (the public input), the
witness streams, and a discrete logarithm for `hint_decompose_bits_exponent`; heap and frame
addresses come from a bump allocator above the public input. Address validity is checked where
it is a constraint of its own, the two `DEREF`s of a range check, against `2^logMem` words.
This is test machinery: nothing is proved about it, and `Fn.Sem` is the semantics.
-/

namespace LeanVM.Guest.Interp

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- A unification node: a value of a call frame, or a memory cell by its address's bits. -/
inductive Node where
  | val (frame : Nat) (v : V)
  | mem (addr : Nat)
  deriving BEq, Hashable, Repr

/-- The interpreter's configuration. -/
structure Cfg where
  program : Core.Program
  /-- The memory before the run, by address. -/
  initMem : K → Option E := fun _ => none
  /-- The memory holds `2^logMem` words. -/
  logMem : Nat := 16
  /-- `n` with `g^n = a`, for `hint_decompose_bits_exponent` and runtime `HeapBuf` sizes. -/
  dlog : K → Option Nat
  /-- The witness streams, each a list of entries. -/
  streams : List (String × List (List E)) := []
  /-- The first word the bump allocator hands out. -/
  heapStart : Nat := 2

/-- The interpreter's state: classes of unified nodes and their words. -/
structure IState where
  cls : Std.HashMap Node Nat := {}
  members : Std.HashMap Nat (List Node) := {}
  known : Std.HashMap Nat E := {}
  nextCls : Nat := 0
  streams : List (String × List (List E)) := []
  nextFrame : Nat := 0
  heapTop : Nat := 0

/-- The interpreter monad. -/
abbrev IM := ReaderT Cfg (StateT IState (Except String))

/-- The bits of a `K` element, a memory key. -/
def keyOf (a : K) : Nat := a.toBitVec.toNat

/-- The word a node holds, if known. -/
def find (n : Node) : IM (Option E) := do
  let st ← get
  match st.cls[n]? with
  | some c => return st.known[c]?
  | none =>
      match n with
      | .mem a => return (← read).initMem (K.ofBits a)
      | .val .. => return none

/-- The class of a node, made on first use; a memory cell of the initial image starts known. -/
def classOf (n : Node) : IM Nat := do
  let st ← get
  if let some c := st.cls[n]? then return c
  let c := st.nextCls
  let init ← match n with
    | .mem a => pure ((← read).initMem (K.ofBits a))
    | .val .. => pure none
  set { st with cls := st.cls.insert n c, members := st.members.insert c [n], nextCls := c + 1,
                known := match init with
                  | some x => st.known.insert c x
                  | none => st.known }
  return c

/-- Write a word into a node: the write-once check if it is known. -/
def assign (n : Node) (x : E) : IM Unit := do
  let c ← classOf n
  let st ← get
  match st.known[c]? with
  | some y => if y != x then throw s!"write-once conflict at {repr n}"
  | none => set { st with known := st.known.insert c x }

/-- Unify two nodes: one word for both from now on. -/
def link (a b : Node) : IM Unit := do
  let ca ← classOf a
  let cb ← classOf b
  if ca == cb then return
  let st ← get
  let ka := st.known[ca]?
  let kb := st.known[cb]?
  if let (some x, some y) := (ka, kb) then
    if x != y then throw s!"write-once conflict linking {repr a} and {repr b}"
  let mb := st.members.getD cb []
  let cls := mb.foldl (fun m n => m.insert n ca) st.cls
  let known := match ka, kb with
    | none, some y => st.known.insert ca y
    | _, _ => st.known
  set { st with cls, known, members := (st.members.insert ca (st.members.getD ca [] ++ mb)).erase cb }

/-- A frame's value. -/
def getV (fr : Nat) (v : V) : IM (Option E) := find (.val fr v)

/-- A frame's value, required. -/
def needV (fr : Nat) (v : V) : IM E := do
  match ← getV fr v with
  | some x => return x
  | none => throw s!"{repr v} is read before it is written"

/-- Write a frame's value. -/
def setV (fr : Nat) (v : V) (x : E) : IM Unit := assign (.val fr v) x

/-- A word in `K`, required. -/
def needK (x : E) (what : String) : IM K := do
  if x.limb 1 = 0 ∧ x.limb 2 = 0 then return x.limb 0 else throw s!"{what} is not in K"

/-- The memory node of `p·g^off`. -/
def memAt (p : E) (off : Nat) : IM Node := do
  let a ← needK p "a pointer"
  return .mem (keyOf (a * gpowK off))

/-- Whether `a` is one of the memory's addresses. -/
def isAddress (a : K) : IM Bool := do
  match (← read).dlog a with
  | some i => return i < 2 ^ (← read).logMem
  | none => return false

/-- A fresh region of `size` words: its address. -/
def alloc (size : Nat) : IM E := do
  let st ← get
  set { st with heapTop := st.heapTop + size }
  return ofK (gpowK st.heapTop)

/-- The nodes a hint destination names. -/
def destNodes (fr : Nat) : Dest → IM (List Node)
  | .stack cells => return cells.map (.val fr)
  | .heap ptr off len => do
      let p ← needV fr ptr
      (List.range len).mapM fun k => memAt p (off + k)

/-- A `0`/`1` word. -/
def bitWord (b : Bool) : E := if b then 1 else 0

/-- Run a hint. -/
def execHint (fr : Nat) : Hint → IM Unit
  | .witness stream dest => do
      let nodes ← destNodes fr dest
      let st ← get
      let entries := (st.streams.find? (·.1 == stream)).map (·.2) |>.getD []
      match entries with
      | [] => throw s!"witness stream `{stream}` is exhausted"
      | e :: rest => do
          if e.length != nodes.length then
            throw s!"witness stream `{stream}`: an entry of {e.length} values for {nodes.length} cells"
          set { st with streams := (stream, rest) :: st.streams.filter (·.1 != stream) }
          (nodes.zip e).forM fun (n, x) => assign n x
  | .bits value start nbits dest => do
      let x ← needV fr value
      let nodes ← destNodes fr dest
      ((List.range nbits).zip nodes).forM fun (j, n) => assign n (bitWord (wordBit x (start + j)))
  | .bitsExp value nbits dest => do
      let a ← needK (← needV fr value) "a hint_decompose_bits_exponent value"
      let some e := (← read).dlog a | throw "hint_decompose_bits_exponent of no small g-power"
      let nodes ← destNodes fr dest
      ((List.range nbits).zip nodes).forM fun (j, n) => assign n (bitWord ((e / 2 ^ j) % 2 = 1))
  | .limbs value dest => do
      let x ← needV fr value
      ((List.range dest.length).zip dest).forM fun (j, v) =>
        setV fr v (ofK (x.limb ⟨j % 3, Nat.mod_lt _ (by decide)⟩))
  | .log2Ceil bits nbits floor dst => do
      let nodes ← destNodes fr bits
      let mut word := 0
      for (j, n) in (List.range nbits).zip nodes do
        let some b ← find n | throw "hint_log2_ceil of unwritten bits"
        if b != 0 then word := word + 2 ^ j
      let cl := if word ≤ 1 then 0 else Nat.log2 (word - 1) + 1
      setV fr dst (gpowE (max cl floor))
  | .inverse x dst => do
      let v ← needV fr x
      setV fr dst (if v = 0 then 0 else v⁻¹)
  | .alloc dst size => do setV fr dst (← alloc size)
  | .allocDyn dst size => do
      let a ← needK (← needV fr size) "a HeapBuf size"
      let some n := (← read).dlog a | throw "a HeapBuf size that is no small g-power"
      setV fr dst (← alloc n)

/-- Run an atom. -/
def execAtom (fr : Nat) : Atom → IM Unit
  | .const d c => setV fr d c
  | .add d a b => do
      match ← getV fr a, ← getV fr b, ← getV fr d with
      | some x, some y, _ => setV fr d (x + y)
      | some x, none, some z => setV fr b (z + x)
      | none, some y, some z => setV fr a (z + y)
      | _, _, _ => throw s!"XOR with two unknowns at {repr d}"
  | .mul d a b => do
      match ← getV fr a, ← getV fr b, ← getV fr d with
      | some x, some y, _ => setV fr d (x * y)
      | some x, none, some z => if x = 0 then throw "back-solve by zero" else setV fr b (z * x⁻¹)
      | none, some y, some z => if y = 0 then throw "back-solve by zero" else setV fr a (z * y⁻¹)
      | _, _, _ => throw s!"MUL with two unknowns at {repr d}"
  | .copy d s => link (.val fr d) (.val fr s)
  | .load d p off => do link (← memAt (← needV fr p) off) (.val fr d)
  | .assertEq a b => link (.val fr a) (.val fr b)
  | .assertNe x inv p => do
      let v ← needV fr x
      let i ← needV fr inv
      setV fr p (v * i)
      setV fr p 1
  | .rangeCheck x y t1 t2 k => do
      let vx ← needV fr x
      let vk ← needV fr k
      let ax ← needK vx "a range-checked value"
      if !(← isAddress ax) then throw "a range-checked value is no address"
      if vx = 0 then throw "a range-checked value is zero"
      setV fr y (vk * vx⁻¹)
      let ay ← needK (← needV fr y) "a range check's complement"
      if !(← isAddress ay) then throw "a failed range check"
      link (← memAt vx 0) (.val fr t1)
      link (← memAt (← needV fr y) 0) (.val fr t2)
  | .assertInK a b => do
      discard <| needK (← needV fr a) "an assert_in_k operand"
      discard <| needK (← needV fr b) "an assert_in_k operand"
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md => do
      let m ← [m0, m1, m2, m3].mapM (needV fr)
      let h0 ← needV fr cv0
      let h1 ← needV fr cv1
      let w ← needV fr md
      let canon := fun (x : E) => decide (x.limb 2 = 0)
      if !(m.all canon && canon h0 && canon h1 && canon w) then throw "a BLAKE2s operand is not canonical"
      let out := compress (cellWords h0 ++ cellWords h1)
        (messageWords ![m[0]!, m[1]!, m[2]!, m[3]!]) (unpackMetadata w).1 (unpackMetadata w).2.1
        (unpackMetadata w).2.2
      setV fr o0 (wordsCell #v[out[0], out[1], out[2], out[3]])
      setV fr o1 (wordsCell #v[out[4], out[5], out[6], out[7]])
  | .frameAddr p run => do
      let p' ← alloc run.length
      setV fr p p'
      ((List.range run.length).zip run).forM fun (k, c) => do link (← memAt p' k) (.val fr c)
  | .hint h => execHint fr h

/-- The arm `x` selects: `j` with `x = g^j`. -/
def armOf (x : E) (n : Nat) : Option Nat :=
  (List.range n).find? fun j => x == gpowE j

mutual
/-- Run a function on its argument words: its return words. -/
def execFn : Nat → String → List E → IM (List E)
  | 0, _, _ => throw "interpreter fuel exhausted"
  | fuel + 1, f, args => do
      let some fn := (← read).program.find? f | throw s!"no function `{f}`"
      if fn.params.length != args.length then throw s!"`{f}` takes {fn.params.length} words"
      let st ← get
      let fr := st.nextFrame
      set { st with nextFrame := fr + 1 }
      (fn.params.zip args).forM fun (v, x) => setV fr v x
      match ← execStmts fuel fr fn.body with
      | some rs => return rs
      | none => throw s!"`{f}` falls off its end"

/-- Run a block: the return words if it returns. -/
def execStmts : Nat → Nat → List Stmt → IM (Option (List E))
  | 0, _, _ => throw "interpreter fuel exhausted"
  | _ + 1, _, [] => return none
  | fuel + 1, fr, s :: ss => do
      match ← execStmt fuel fr s with
      | some rs => return some rs
      | none => execStmts fuel fr ss

/-- Run a statement. -/
def execStmt : Nat → Nat → Stmt → IM (Option (List E))
  | 0, _, _ => throw "interpreter fuel exhausted"
  | fuel + 1, fr, s => do
      match s with
      | .atom a => do execAtom fr a; return none
      | .ite c z n => do
          let vc ← needV fr c
          discard <| needK vc "a branch condition"
          execStmts fuel fr (if vc = 0 then z else n)
      | .match_ x arms => do
          let some j := armOf (← needV fr x) arms.length | throw "a match selector out of range"
          execStmts fuel fr arms[j]!
      | .call f args rets => do
          let rs ← execFn fuel f (← args.mapM (needV fr))
          if rs.length != rets.length then throw s!"`{f}` returns {rs.length} words for {rets.length}"
          (rets.zip rs).forM fun (v, x) => setV fr v x
          return none
      | .callIf c f args => do
          let vc ← needV fr c
          discard <| needK vc "a call condition"
          if vc != 0 then discard <| execFn fuel f (← args.mapM (needV fr))
          return none
      | .dispatch x fs args rets => do
          let some j := armOf (← needV fr x) fs.length | throw "a dispatch selector out of range"
          let rs ← execFn fuel fs[j]! (← args.mapM (needV fr))
          if rs.length != rets.length then throw s!"`{fs[j]!}` returns {rs.length} words"
          (rets.zip rs).forM fun (v, x) => setV fr v x
          return none
      | .ret vs => return some (← vs.mapM (needV fr))
end

/-- A small discrete logarithm, by search below `2^bits`. -/
def dlogSearch (bits : Nat) (a : K) : Option Nat := Id.run do
  let mut x : K := 1
  for i in List.range (2 ^ bits) do
    if x == a then return some i
    x := x * g
  return none

/-! ## Discrete logarithms

`g` has order `2^64 - 1`, a product of seven primes, the largest `6700417`: Pohlig-Hellman reduces
a logarithm to one per prime, each found by baby steps and giant steps. -/

/-- The prime factors of `2^64 - 1`, the order of `g`. -/
def orderPrimes : List Nat := [3, 5, 17, 257, 641, 65537, 6700417]

/-- Per prime `p` of the order: `p`, the step `m = ⌊√p⌋ + 1`, `h^(-m)` for `h = g^((2^64-1)/p)`
of order `p`, and `h^j ↦ j` for `j < m`. -/
structure DlogTables where
  primes : List (Nat × Nat × K × Std.HashMap Nat Nat)

/-- The tables. -/
def DlogTables.build : DlogTables where
  primes := orderPrimes.map fun p =>
    let h : K := powBin 64 g 1 ((2 ^ 64 - 1) / p)
    let m := p.sqrt + 1
    let baby := (List.range m).foldl (fun (acc : Std.HashMap Nat Nat × K) j =>
      (acc.1.insert (keyOf acc.2) j, acc.2 * h)) ({}, 1)
    (p, m, powBin 64 h 1 (p - m), baby.1)

/-- `b^e mod p` for `e < 2^64`. -/
def powMod (b e p : Nat) : Nat :=
  ((List.range 64).foldl (fun (acc : Nat × Nat) i =>
    (if e.testBit i then acc.1 * acc.2 % p else acc.1, acc.2 * acc.2 % p)) (1 % p, b % p)).1

/-- The `n < 2^64 - 1` with `g^n = a`, by Pohlig-Hellman; `none` for `0`. -/
def dlogWith (t : DlogTables) (a : K) : Option Nat := Id.run do
  if a == 0 then return none
  let order := 2 ^ 64 - 1
  let mut n := 0
  for (p, m, giant, baby) in t.primes do
    let mut y : K := powBin 64 a 1 (order / p)
    let mut x : Option Nat := none
    for i in List.range m do
      if let some j := baby[keyOf y]? then
        x := some ((i * m + j) % p)
        break
      y := y * giant
    let some xp := x | return none
    let q := order / p
    n := (n + xp * q * powMod q (p - 2) p) % order
  return if gpowK n == a then some n else none

/-- Evaluate `f` on `args`: its return words and the final state. -/
def run (cfg : Cfg) (f : String) (args : List E) (fuel : Nat := 1000000000) :
    Except String (List E × IState) :=
  (execFn fuel f args cfg).run { streams := cfg.streams, heapTop := cfg.heapStart }

/-! ## Printing -/

/-- A word: its low limb in decimal when the others are zero, else its three limbs. -/
def showE (x : E) : String :=
  let (c0, c1, c2) := limbsOf x
  if c1 = 0 && c2 = 0 then s!"{c0}" else s!"({c0}, {c1}, {c2})"

/-- A position step. -/
def showSeg : Seg → String
  | .s i => s!"s{i}"
  | .u j => s!"u{j}"
  | .t => "t"
  | .e => "e"
  | .a j => s!"a{j}"
  | .i f k => s!"i{k}:{f}"

/-- A value: `%` then its position outermost first, its tag, and its run index. -/
def showV (v : V) : String :=
  let p := String.intercalate "." (v.path.reverse.map showSeg)
  s!"%{p}#{v.tag}" ++ (if v.idx = 0 then "" else s!"[{v.idx}]")

/-- Values. -/
def showVs (vs : List V) : String := String.intercalate ", " (vs.map showV)

/-- A hint destination. -/
def showDest : Dest → String
  | .stack cells => s!"[{showVs cells}]"
  | .heap p off len => s!"{showV p}[{off}..+{len}]"

/-- An atom. -/
def showAtom : Atom → String
  | .const d c => s!"{showV d} = {showE c}"
  | .add d a b => s!"{showV d} = {showV a} + {showV b}"
  | .mul d a b => s!"{showV d} = {showV a} * {showV b}"
  | .copy d s => s!"{showV d} = {showV s}"
  | .load d p off => s!"{showV d} = mem[{showV p} g^{off}]"
  | .assertEq a b => s!"assert {showV a} == {showV b}"
  | .assertNe x inv p => s!"assert {showV x} != 0 by {showV inv}, {showV p}"
  | .rangeCheck x y t1 t2 k => s!"assert log {showV x} < log g*{showV k} by {showVs [y, t1, t2]}"
  | .assertInK a b => s!"assert_in_k {showV a}, {showV b}"
  | .blake2s m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
      s!"{showVs [o0, o1]} = blake2s([{showVs [m0, m1, m2, m3]}], cv [{showVs [cv0, cv1]}], md {showV md})"
  | .frameAddr p run => s!"{showV p} = addr [{showVs run}]"
  | .hint h => match h with
    | .witness s d => s!"hint {showDest d} = witness \"{s}\""
    | .bits v st n d => s!"hint {showDest d} = bits {showV v} [{st}..+{n}]"
    | .bitsExp v n d => s!"hint {showDest d} = bits log {showV v} [..{n}]"
    | .limbs v d => s!"hint [{showVs d}] = limbs {showV v}"
    | .log2Ceil b n f d => s!"hint {showV d} = log2ceil {showDest b} {n} floor {f}"
    | .inverse x d => s!"hint {showV d} = inverse {showV x}"
    | .alloc d n => s!"hint {showV d} = HeapBuf({n})"
    | .allocDyn d n => s!"hint {showV d} = HeapBuf(log {showV n})"

mutual
/-- A statement, as lines at an indentation. -/
def showStmt (ind : String) : Stmt → List String
  | .atom a => [ind ++ showAtom a]
  | .ite c z n => [s!"{ind}if {showV c} == 0:"] ++ showStmts (ind ++ "  ") z ++ [s!"{ind}else:"] ++
      showStmts (ind ++ "  ") n
  | .match_ x arms => [s!"{ind}match log {showV x}:"] ++ showArms ind 0 arms
  | .call f args rets => [s!"{ind}[{showVs rets}] = {f}({showVs args})"]
  | .callIf c f args => [s!"{ind}if {showV c} != 0: {f}({showVs args})"]
  | .dispatch x fs args rets =>
      [s!"{ind}[{showVs rets}] = match log {showV x}: {String.intercalate " | " fs}({showVs args})"]
  | .ret vs => [if vs.isEmpty then s!"{ind}return" else s!"{ind}return {showVs vs}"]

/-- A block. -/
def showStmts (ind : String) : List Stmt → List String
  | [] => []
  | s :: ss => showStmt ind s ++ showStmts ind ss

/-- The arms of a `match`. -/
def showArms (ind : String) : Nat → List (List Stmt) → List String
  | _, [] => []
  | j, a :: as => [s!"{ind}  {j}:"] ++ showStmts (ind ++ "    ") a ++ showArms ind (j + 1) as
end

/-- A core function, one line per statement. -/
def showFn (f : Fn) : String :=
  String.intercalate "\n" ([s!"def {f.name}({showVs f.params}):"] ++ showStmts "  " f.body)

end
end LeanVM.Guest.Interp
