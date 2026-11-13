module

public import Statement.LeanIsa

/-!
# The executor

`execute prog input advice` runs `prog` on `input` as leanVM's Rust executor does
(`Program::execute_with`, `crates/leanvm_core/src/cpu/execute.rs`), producing the execution the
prover takes. The memory starts empty and is written once: each instruction fills the cell its
relation determines (a `XOR`'s or a `MUL`'s result, a `MUL`'s one unknown operand, a `SET`'s cell,
the unwritten side of a `DEREF`, a `KECCAK`'s outputs), and a `DEREF` between two unwritten cells
links them, a later write to either reaching both. The hints a `pc` carries (`RHint`,
`cpu/hints.rs`) run before its instruction: they allocate (`next_free`, a bump pointer from the end
of `main`'s frame), pop witness streams, and compute advice the instructions go on to check.

Nothing here is trusted: a run that halts gives a valid execution whatever the program, its hints
and its streams (`lean_vm`, `LeanVM/Prover/ExecuteSound.lean`). One difference from the Rust: an
instruction reading an unwritten cell fails here, where the Rust reads zero and records the read,
an execution its prover then refuses (`unconstrained_reads`); so the two accept the same runs. A
run whose hints write past `maxCells` fails at its end, its memory being no stack's. A `DEREF` link
is a class of cells sharing one value; the run ends by checking that every link's two cells agree.
-/

@[expose] public section

namespace LeanVM.Prover.Exec

open LeanVM.Parameters LeanVM.Semantics

/-! ## Limits -/

/-- `MAX_CELLS` (`cpu/hints.rs`): the cells a run addresses, the most a committed stack holds. -/
def maxCells : ℕ := 2 ^ 28

/-- `MAX_STEPS` (`execute.rs`): `2^30` committed words over the narrowest table's `7` columns
(`MIN_COMMITTED_COLUMNS`, `tables.rs`). -/
def maxSteps : ℕ := 2 ^ 30 / 7

/-! ## Discrete logarithms (`GPow`, `bounded_dlog`, `cpu/hints.rs`) -/

/-- `g⁻¹` (`div_by_g`). -/
def gInv : K := K.ofBits 0x800000000000000D

/-- Exponents by the lane of their power. -/
abbrev Idx : Type := Std.HashMap UInt64 ℕ

/-- `I` with `k + step·i ↦` its power for `i < n`, from `y = g^k` (`gs = g^step`). -/
def fill (gs : K) (step : ℕ) : ℕ → ℕ → K → Idx → Idx
  | 0, _, _, I => I
  | n + 1, k, y, I => fill gs step n (k + step) (y * gs) (I.insert y.lane k)

/-- The baby steps: `g^j ↦ j` for `j < 2^17`. -/
def baby : Idx := fill g 1 (2 ^ 17) 0 1 ∅

/-- The giant step, `g^(-2^17)`. -/
def giant : K := gInv ^ 2 ^ 17

/-- Baby-step giant-step from `y = x · g^(-2^17·a)`, for `n` giant steps. -/
def bsgs : ℕ → ℕ → K → Option ℕ
  | 0, _, _ => none
  | n + 1, a, y =>
    match baby[y.lane]? with
    | some j => some (2 ^ 17 * a + j)
    | none => bsgs n (a + 1) (y * giant)

/-- A `k` with `g^k = x`, searching `k < 2^nbits` (for `nbits ≤ 17`, `k < 2^17`)
(`bounded_dlog`). -/
def boundedDlog (x : K) (nbits : ℕ) : Option ℕ :=
  bsgs (if 17 < nbits then 2 ^ (nbits - 17) else 1) 0 x

/-- `y · g^j = x` with `y · g^(-i)` in the coarse index for some `i < n`: its exponent plus `j + i`
(`GPow::resolve`). -/
def resolve (coarse : Idx) : ℕ → ℕ → K → Option ℕ
  | 0, _, _ => none
  | n + 1, j, y =>
    match coarse[y.lane]? with
    | some k => some (k + j)
    | none => resolve coarse n (j + 1) (y * gInv)

/-- The logarithm table of a run: the exponents announced (frame and buffer bases, resolved
lookups) and every multiple of `64` below `cover` (`top = g^cover`). -/
structure Dlog where
  noted : Idx
  coarse : Idx
  cover : ℕ
  top : K

/-- The empty table. -/
def Dlog.empty : Dlog := ⟨∅, ∅, 0, 1⟩

/-- Cover the multiples of `64` up to `n` (`GPow::grow_to`). -/
def Dlog.grow (D : Dlog) (n : ℕ) : Dlog :=
  if D.cover ≤ n then
    let ⟨noted, coarse, cover, top⟩ := D
    let m := (n - cover) / 64 + 1
    ⟨noted, fill (g ^ 64) 64 m cover top coarse, cover + 64 * m, g ^ (cover + 64 * m)⟩
  else D

/-- Announce `k` (`GPow::note`). -/
def Dlog.note (D : Dlog) (k : ℕ) : Dlog :=
  let ⟨noted, coarse, cover, top⟩ := D
  ⟨noted.insert (g ^ k).lane k, coarse, cover, top⟩

/-- The `k < bound` with `g^k = x`: announced, or within `64` above a covered multiple of `64`,
or by a bounded discrete logarithm; announced once found (`GPow::log_below`). -/
def Dlog.log (D : Dlog) (x : K) (bound : ℕ) : Option ℕ × Dlog :=
  match D.noted[x.lane]? with
  | some k => (if k < bound then some k else none, D)
  | none =>
    match (resolve D.coarse 64 0 x).orElse fun _ ↦ boundedDlog x (Nat.clog 2 bound) with
    | some k => if k < bound then (some k, D.note k) else (none, D)
    | none => (none, D)

/-! ## The advice -/

/-- Where a hint's run of cells starts (`BitsDest`). -/
inductive BitsDest where
  /-- Frame cells `fp + base + k`. -/
  | stack (base : ℕ)
  /-- Heap cells from the pointer at `fp + ptr`. -/
  | heap (ptr : ℕ)

/-- A hint (`RHint`, `cpu/hints.rs`), its offsets relative to `fp`. -/
inductive Hint where
  /-- Announce `fp + offset`'s address (no effect on the run). -/
  | frameAddress (offset : ℕ)
  /-- Reserve `n` frames of `size` cells and `tail` more, `n` the exponent of
  `[fp + stop] · startInverse`, its base written to `fp + ptr`. -/
  | allocFrames (ptr size stop : ℕ) (startInverse : K) (tail : ℕ)
  /-- Reserve `size` cells, its base written to `fp + ptr`. -/
  | alloc (ptr size : ℕ)
  /-- Reserve the exponent of `[fp + size]` cells, its base written to `fp + ptr`. -/
  | allocDyn (ptr size : ℕ)
  /-- Reserve the exponent of `stream`'s next entry, one word, cells, its base written to
  `fp + ptr`; nothing for an empty entry. -/
  | allocAdvice (ptr : ℕ) (stream : String)
  /-- Reserve `sizes[k]` cells, `k` the exponent of `[fp + sel]`, its base written to
  `fp + ptr`: a dispatched call's frame, sized by the arm it selects. -/
  | allocArm (ptr sel : ℕ) (sizes : List ℕ)
  /-- Write the address of `fp + cell` to `fp + ptr`. -/
  | cellAddress (ptr cell : ℕ)
  /-- Pop `stream`'s next entry, of `len` words, into `fp + base + k`. -/
  | witnessStack (stream : String) (base len : ℕ)
  /-- Pop `stream`'s next entry, of `len` words, into the heap from the pointer at `fp + ptr`,
  plus `lo`. -/
  | witnessHeap (stream : String) (ptr lo len : ℕ)
  /-- Write `g^max(⌈log₂ v⌉, floor)` to `fp + dst`, `v` the integer of the `nbits` bits at `bits`. -/
  | log2Ceil (bits : BitsDest) (dst nbits floor : ℕ)
  /-- Write the low `nbits` bits of `[fp + value]` to `bits`. -/
  | bitDecompose (value : ℕ) (bits : BitsDest) (nbits : ℕ)
  /-- Write the `nbits` bits of the exponent of `[fp + value]` to `bits`. -/
  | bitDecomposeExp (value : ℕ) (bits : BitsDest) (nbits : ℕ)
  /-- Write `g^d` for the `ndigits` digits `d` of `digitBits` bits of the exponent of
  `[fp + value]` (below `2^nbits`) from bit `start`, or from the exponent of `[fp + startCell]`. -/
  | digitDecomposeExp (value : ℕ) (dst : BitsDest) (nbits ndigits digitBits start : ℕ)
      (startCell : Option ℕ)
  /-- Write `g^n` for `count` windows `n` of `width` bits of `[fp + value]` from bit `start`, to
  `dest` from cell `pos`. -/
  | windowsExp (value : ℕ) (dest : BitsDest) (pos start width count : ℕ)
  /-- Write the first `len` limbs of `[fp + value]` to `fp + base + j`. -/
  | fieldLimbs (value base len : ℕ)
  /-- Write `[fp + value]⁻¹`, or `0`, to `fp + dst`. -/
  | inverse (value dst : ℕ)

/-- What a run needs besides the program and its public input: `main`'s frame size (where
allocation starts), the hints by `pc`, and the witness streams by name, each its entries in the
order the program pops them. -/
structure Advice where
  mainFrame : ℕ
  hints : List (ℕ × List Hint)
  streams : List (String × List (List E))

/-! ## Faults (`Fault`, `execute.rs`) -/

/-- Why a run has no execution. -/
inductive Fault where
  | conflict (cell : ℕ) (had new : E)
  | unwrittenRead (cell : ℕ)
  | wildPointer (value : E)
  | notInK (what : String) (value : E)
  | notAGPower (what : String) (value : K)
  | backSolveThroughZero
  | witness (problem : String)
  | outOfMemory
  | haltOutsideMain (fp : ℕ)
  | stepLimit
  | badInstruction
  | linkMismatch (a b : ℕ)

/-! ## The memory -/

/-- A cell: unwritten, written, or in a link class. -/
inductive Cell where
  | free
  | lit (v : E)
  | cls (k : ℕ)
  deriving Inhabited

/-- The write-once memory: its cells, the link classes' values and members, every link made,
and one past the highest cell accessed or reserved (`used`). -/
structure Mem where
  cells : Array Cell
  vals : Array (Option E)
  members : Array (Array ℕ)
  links : Array (ℕ × ℕ)
  used : ℕ

/-- The value of cell `c`, if written. -/
def Mem.get (m : Mem) (c : ℕ) : Option E :=
  match m.cells[c]? with
  | some (.lit v) => some v
  | some (.cls k) => (m.vals[k]?).join
  | _ => none

/-- Whether cell `c` is written. -/
def Mem.written (m : Mem) (c : ℕ) : Bool := (m.get c).isSome

/-- A hint's read: an unwritten cell reads as zero (`Mem::get`). -/
def Mem.peek (m : Mem) (c : ℕ) : E := (m.get c).getD 0

/-- Cover cell `c` (`Mem::ensure`). -/
def Mem.ensure (m : Mem) (c : ℕ) : Mem := { m with used := max m.used (c + 1) }

/-- Set cell `c`, growing the array. -/
def Mem.setCell (m : Mem) (c : ℕ) (x : Cell) : Mem :=
  let ⟨cells, vals, members, links, used⟩ := m
  let cells := if c < cells.size then cells
    else cells ++ Array.replicate (max (c + 1) (2 * cells.size) - cells.size) .free
  ⟨cells.set! c x, vals, members, links, used⟩

/-- Write `v` to cell `c`, once (`Mem::put`): a written cell must hold `v`; a cell in a class
writes the class. -/
def Mem.put (m : Mem) (c : ℕ) (v : E) : Except Fault Mem :=
  let m := m.ensure c
  match m.cells[c]? with
  | some (.lit w) => if w = v then pure m else throw (.conflict c w v)
  | some (.cls k) =>
    match (m.vals[k]?).join with
    | some w => if w = v then pure m else throw (.conflict c w v)
    | none =>
      let ⟨cells, vals, members, links, used⟩ := m
      pure ⟨cells, vals.set! k (some v), members, links, used⟩
  | _ => pure (m.setCell c (.lit v))

/-- An instruction's read: a written cell's value (`Mem::read`). -/
def Mem.read (m : Mem) (c : ℕ) : Except Fault E :=
  match m.get c with
  | some v => pure v
  | none => throw (.unwrittenRead c)

/-- Move class `j`'s cells into class `i`. -/
def Mem.merge (m : Mem) (i j : ℕ) : Mem :=
  let ⟨cells, vals, members, links, used⟩ := m
  let js := members[j]?.getD #[]
  let cells := js.foldl (fun cs c ↦ match cs[c]? with
    | some (.cls k) => if k = j then cs.set! c (.cls i) else cs
    | _ => cs) cells
  ⟨cells, vals, (members.set! j #[]).modify i (· ++ js), links, used⟩

/-- Add the unwritten cell `c` to class `i`. -/
def Mem.join (m : Mem) (c i : ℕ) : Mem :=
  let ⟨cells, vals, members, links, used⟩ := m.setCell c (.cls i)
  ⟨cells, vals, members.modify i (·.push c), links, used⟩

/-- Link the unwritten cells `a` and `b` (`Mem::link`), the smaller class into the larger. -/
def Mem.link (m : Mem) (a b : ℕ) : Mem :=
  let ⟨cells, vals, members, links, used⟩ := m
  let m : Mem := ⟨cells, vals, members, links.push (a, b), max used (max a b + 1)⟩
  match m.cells[a]?, m.cells[b]? with
  | some (.cls i), some (.cls j) =>
    if i = j then m
    else if (m.members[j]?.getD #[]).size ≤ (m.members[i]?.getD #[]).size then m.merge i j
    else m.merge j i
  | some (.cls i), _ => m.join b i
  | _, some (.cls j) => m.join a j
  | _, _ =>
    let ⟨cells, vals, members, links, used⟩ := m
    let k := vals.size
    (Mem.join ⟨cells, vals.push none, members.push #[], links, used⟩ a k).join b k

/-! ## The run -/

/-- An instruction, its operands as offsets: `o = g^offset`. A `KECCAK`'s thirteen input cells and
its first output cell, from `fp`. -/
inductive Op where
  | xor (a b c : ℕ)
  | mul (a b c : ℕ)
  | set (o : ℕ) (k : E)
  | deref (o1 o2 o3 : ℕ) (mode : DerefMode)
  | jump (c d f : ℕ)
  | keccak (ins : Array ℕ) (out : ℕ) (inOdd outOdd : Bool) (count : ℕ)
  deriving Inhabited

/-- An operand's offset. -/
def offOf (o : K) : Option ℕ := boundedDlog o 28

/-- An instruction's offsets. -/
def decode : LeanIsaInstruction → Option Op
  | .xor a b c => return .xor (← offOf a) (← offOf b) (← offOf c)
  | .mulNative a b c => return .mul (← offOf a) (← offOf b) (← offOf c)
  | .setConstant o k => return .set (← offOf o) k
  | .deref o1 o2 o3 mode => return .deref (← offOf o1) (← offOf o2) (← offOf o3) mode
  | .jump c d f => return .jump (← offOf c) (← offOf d) (← offOf f)
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells => do
    let ins ← (List.finRange 13).mapM fun c ↦ offOf (keccakInputCellOffset om otail ob8 ocap c)
    return .keccak ins.toArray (← offOf oout) inOdd outOdd outCells.cellCount

/-- The program and advice, tabulated. -/
structure Ctx where
  ops : Array Op
  hints : Array (List Hint)
  streams : Std.HashMap String (Array (List E))

/-- The state of a run. -/
structure St where
  mem : Mem
  dl : Dlog
  pc : ℕ
  fp : ℕ
  nextFree : ℕ
  cursor : Std.HashMap String ℕ
  steps : ℕ

/-- Cell `base + off`, if below `maxCells`. -/
def cellAt (base off : ℕ) : Except Fault ℕ :=
  if base + off < maxCells then pure (base + off) else throw .outOfMemory

/-- A word in `K`, or `NotInK`. -/
def inK (what : String) (v : E) : Except Fault K :=
  if v.limb 1 = 0 then pure (v.limb 0) else throw (.notInK what v)

/-- A word as the integer `limb 0 + 2^64 · limb 1` (`u128::from`). -/
def wordNat (v : E) : ℕ := (v.limb 0).lane.toNat + 2 ^ 64 * (v.limb 1).lane.toNat

/-- `0` or `1` as a word. -/
def bitWord (b : Bool) : E := if b then 1 else 0

/-- The empty memory. -/
def Mem.empty : Mem := ⟨#[], #[], #[], #[], 0⟩

/-- Change the memory, taking it out of the state first so that it is changed in place. -/
@[inline] def St.withMem (s : St) (f : Mem → Except Fault Mem) : Except Fault St := do
  let mem := s.mem
  let s := { s with mem := .empty }
  pure { s with mem := ← f mem }

/-- `Dlog.log` on the state's table, changed in place. -/
@[inline] def St.log (s : St) (x : K) (bound : ℕ) : Option ℕ × St :=
  let dl := s.dl
  let s := { s with dl := .empty }
  let (k, dl) := dl.log x bound
  (k, { s with dl })

/-- `Dlog.log`, failing with `fault` where there is no logarithm. -/
@[inline] def St.logOr (s : St) (x : K) (bound : ℕ) (fault : Fault) : Except Fault (ℕ × St) :=
  match s.log x bound with
  | (some k, s) => pure (k, s)
  | (none, _) => throw fault

/-- Write `vs` from cell `b`. -/
def putRun (b : ℕ) (vs : List E) (m : Mem) : Except Fault Mem :=
  vs.zipIdx.foldlM (fun m (v, k) ↦ m.put (b + k) v) m

/-- The base of a heap run: the exponent of the pointer at cell `c` (`heap_base`). -/
def heapBase (s : St) (c : ℕ) (what : String) : Except Fault (ℕ × St) := do
  let p ← inK what (s.mem.peek c)
  s.logOr p maxCells (.notAGPower what p)

/-- Where a hint's run starts (`bits_base`). -/
def bitsBase (s : St) (d : BitsDest) (what : String) : Except Fault (ℕ × St) :=
  match d with
  | .stack base => pure (s.fp + base, s)
  | .heap ptr => heapBase s (s.fp + ptr) what

/-- The exponent of a word below `2^nbits`, by a bounded discrete logarithm. -/
def expOf (what : String) (v : E) (nbits : ℕ) : Except Fault ℕ := do
  let x ← inK what v
  match boundedDlog x nbits with
  | some n => pure n
  | none => throw (.notAGPower what x)

/-- Reserve `size` cells, their base written to `fp + ptr`, unless written. -/
def allocate (s : St) (ptr size : ℕ) : Except Fault St := do
  let cell := s.fp + ptr
  if s.mem.written cell then return s
  let base := s.nextFree
  let next ← cellAt base size
  let s ← s.withMem fun m ↦ (if base < next then m.ensure (next - 1) else m).put cell (ofK (g ^ base))
  let dl := s.dl
  let s := { s with dl := .empty }
  pure { s with nextFree := next, dl := (dl.grow next).note base }

/-- Pop stream `name`'s next entry, whatever its length (`Stream::next`). -/
def popEntry (C : Ctx) (s : St) (name : String) : Except Fault (List E × St) := do
  let some entries := C.streams[name]? | throw (.witness s!"no witness stream `{name}`")
  let i := s.cursor.getD name 0
  let some e := entries[i]? | throw (.witness s!"witness stream `{name}` exhausted")
  let cursor := s.cursor
  let s := { s with cursor := ∅ }
  pure (e, { s with cursor := cursor.insert name (i + 1) })

/-- Pop stream `name`'s next entry, of `len` words (`Stream::pop`). -/
def pop (C : Ctx) (s : St) (name : String) (len : ℕ) : Except Fault (List E × St) := do
  let some entries := C.streams[name]? | throw (.witness s!"no witness stream `{name}`")
  let i := s.cursor.getD name 0
  let some e := entries[i]? | throw (.witness s!"witness stream `{name}` exhausted")
  if e.length ≠ len then
    throw (.witness s!"witness `{name}` entry {i}: length {e.length}, not {len}")
  let cursor := s.cursor
  let s := { s with cursor := ∅ }
  pure (e, { s with cursor := cursor.insert name (i + 1) })

/-- Run a hint. -/
def runHint (C : Ctx) (s : St) : Hint → Except Fault St
  | .frameAddress offset => do
    let c ← cellAt s.fp offset
    let dl := s.dl
    let s := { s with dl := .empty }
    pure { s with dl := dl.note c }
  | .alloc ptr size => allocate s ptr size
  | .allocDyn ptr size => do
    let sz ← inK "HeapBuf size" (s.mem.peek (s.fp + size))
    let (n, s) ← s.logOr sz maxCells (.notAGPower "HeapBuf size" sz)
    allocate s ptr n
  | .allocAdvice ptr stream => do
    match ← popEntry C s stream with
    | ([], s) => pure s
    | ([w], s) =>
      let sz ← inK "HeapBuf size advice" w
      let (n, s) ← s.logOr sz maxCells (.notAGPower "HeapBuf size advice" sz)
      allocate s ptr n
    | (v, _) => throw (.witness s!"a HeapBuf size advice holds {v.length} values, not 0 or 1")
  | .allocArm ptr sel sizes => do
    let x ← inK "dispatch selector" (s.mem.peek (s.fp + sel))
    let (k, s) ← s.logOr x maxCells (.notAGPower "dispatch selector" x)
    let some n := sizes[k]? | throw (.notAGPower "dispatch selector" x)
    allocate s ptr n
  | .cellAddress ptr cell => do
    let c ← cellAt s.fp cell
    s.withMem (·.put (s.fp + ptr) (ofK (g ^ c)))
  | .allocFrames ptr size stop startInverse tail => do
    let span := (← inK "loop bound" (s.mem.peek (s.fp + stop))) * startInverse
    if span = 0 then throw (.notAGPower "loop bound" span)
    let (n, s) ← s.logOr span maxCells (.notAGPower "loop bound" span)
    allocate s ptr (size * n + tail)
  | .witnessStack name base len => do
    let (v, s) ← pop C s name len
    s.withMem (putRun (s.fp + base) v)
  | .witnessHeap name ptr lo len => do
    let (b, s) ← heapBase s (s.fp + ptr) "hint_witness heap pointer"
    let (v, s) ← pop C s name len
    s.withMem (putRun (b + lo) v)
  | .log2Ceil bits dst nbits floor => do
    let (b, s) ← bitsBase s bits "log2_ceil pointer"
    let word := (List.range nbits).foldl
      (fun w j ↦ if s.mem.peek (b + j) = 0 then w else w + 2 ^ j) 0
    let cl := if word ≤ 1 then 0 else Nat.log2 (word - 1) + 1
    s.withMem (·.put (s.fp + dst) (ofK (g ^ max cl floor)))
  | .bitDecompose value bits nbits => do
    let v := wordNat (s.mem.peek (s.fp + value))
    let (b, s) ← bitsBase s bits "decompose pointer"
    s.withMem (putRun b ((List.range nbits).map fun j ↦ bitWord (v.testBit j)))
  | .bitDecomposeExp value bits nbits => do
    let n ← expOf "hint_decompose_bits_exponent value" (s.mem.peek (s.fp + value)) nbits
    let (b, s) ← bitsBase s bits "hint_decompose_bits_exponent pointer"
    s.withMem (putRun b ((List.range nbits).map fun j ↦ bitWord (n.testBit j)))
  | .windowsExp value dest pos start width count => do
    let v := wordNat (s.mem.peek (s.fp + value))
    let (b, s) ← bitsBase s dest "windows pointer"
    let window (i : ℕ) : ℕ := (v >>> (start + i * width)) % 2 ^ width
    s.withMem (putRun (b + pos) ((List.range count).map fun i ↦ ofK (g ^ window i)))
  | .digitDecomposeExp value dst nbits ndigits digitBits start startCell => do
    let n ← expOf "hint_decompose_digits_exponent value" (s.mem.peek (s.fp + value)) nbits
    let st ← match startCell with
      | none => pure start
      | some c => expOf "hint_decompose_digits_exponent start" (s.mem.peek (s.fp + c)) 7
    let (b, s) ← bitsBase s dst "hint_decompose_digits_exponent pointer"
    let digit (j : ℕ) : ℕ :=
      let at' := st + digitBits * j
      if 128 ≤ at' then 0 else (n >>> at') % 2 ^ digitBits
    s.withMem (putRun b ((List.range ndigits).map fun j ↦ ofK (g ^ digit j)))
  | .fieldLimbs value base len => do
    let v := s.mem.peek (s.fp + value)
    s.withMem (putRun (s.fp + base)
      ((List.range len).map fun j ↦ ofK (if j = 0 then v.limb 0 else v.limb 1)))
  | .inverse value dst => do
    let v := s.mem.peek (s.fp + value)
    s.withMem (·.put (s.fp + dst) (if v = 0 then 0 else v⁻¹))

/-- Execute an instruction (`execute.rs`'s opcode arms). -/
def runOp (C : Ctx) (s : St) : Op → Except Fault St
  | .xor a b c => do
    let (ca, cb, cc) := (← cellAt s.fp a, ← cellAt s.fp b, ← cellAt s.fp c)
    let v := (← s.mem.read ca) + (← s.mem.read cb)
    let s ← s.withMem fun m ↦ return ((← m.put cc v).ensure ca).ensure cb
    pure { s with pc := s.pc + 1 }
  | .mul a b c => do
    let (ca, cb, cc) := (← cellAt s.fp a, ← cellAt s.fp b, ← cellAt s.fp c)
    -- A `MUL` whose result is written and one operand not solves for that operand.
    let s ← s.withMem fun m ↦ do
      let m ← if m.written cc && m.written ca != m.written cb then do
          let (known, unknown) := if m.written ca then (ca, cb) else (cb, ca)
          let vk := m.peek known
          if vk = 0 then throw .backSolveThroughZero
          m.put unknown (m.peek cc * vk⁻¹)
        else pure m
      let v := (← m.read ca) * (← m.read cb)
      return ((← m.put cc v).ensure ca).ensure cb
    pure { s with pc := s.pc + 1 }
  | .set o k => do
    let c ← cellAt s.fp o
    let s ← s.withMem (·.put c k)
    pure { s with pc := s.pc + 1 }
  | .deref o1 o2 o3 mode => do
    let a1 ← cellAt s.fp o1
    let p ← s.mem.read a1
    if p.limb 1 ≠ 0 then throw (.wildPointer p)
    let (base, s) ← s.logOr (p.limb 0) maxCells (.wildPointer p)
    let (a2, a3) := (← cellAt base o2, ← cellAt s.fp o3)
    let (pc, fp) := (s.pc, s.fp)
    let s ← s.withMem fun m ↦ do
      let m ← match mode with
        | .cell =>
          if m.written a2 then m.put a3 (m.peek a2)
          else if m.written a3 then m.put a2 (m.peek a3)
          else pure (m.link a2 a3)
        | .pc => m.put a2 (ofK (g ^ (pc + 2)))
        | .fp => m.put a2 (ofK (g ^ fp))
      return ((m.ensure a1).ensure a2).ensure a3
    pure { s with pc := pc + 1 }
  | .jump c d f => do
    let (ac, ad, af) := (← cellAt s.fp c, ← cellAt s.fp d, ← cellAt s.fp f)
    let vc ← inK "JUMP condition" (← s.mem.read ac)
    let vd ← inK "JUMP target" (← s.mem.read ad)
    let vf ← inK "JUMP fp" (← s.mem.read af)
    let s ← s.withMem fun m ↦ return ((m.ensure ac).ensure ad).ensure af
    if vc = 0 then return { s with pc := s.pc + 1 }
    let (pc, s) ← s.logOr vd C.ops.size (.notAGPower "JUMP target" vd)
    let (fp, s) ← s.logOr vf maxCells (.notAGPower "JUMP fp" vf)
    pure { s with pc, fp }
  | .keccak ins out inOdd outOdd count => do
    let cells ← ins.toList.mapM (cellAt s.fp)
    let input ← cells.mapM s.mem.read
    let cellOf (c : Fin 13) : E := input.getD c.val 0
    let output := cellsOfState (keccakF1600 (stateOfCells cellOf inOdd)) outOdd
    let outs ← (List.range count).mapM fun k ↦ cellAt s.fp (out + k)
    let s ← s.withMem fun m ↦ do
      let m ← outs.zipIdx.foldlM (fun m (c, k) ↦ m.put c (output ⟨k % 13, Nat.mod_lt _ (by decide)⟩)) m
      return (cells ++ outs).foldl Mem.ensure m
    pure { s with pc := s.pc + 1 }

/-- One step: the hints at `pc`, then its instruction. -/
def step (C : Ctx) (s : St) : Except (ℕ × Fault) St := do
  let pc := s.pc
  let s ← ((C.hints[pc]?.getD []).foldlM (runHint C) s).mapError (pc, ·)
  let some op := C.ops[pc]? | throw (pc, .badInstruction)
  let s ← (runOp C s op).mapError (pc, ·)
  pure { s with steps := s.steps + 1 }

/-- Run until the halting state (`pc` the last slot, `fp = 0`), at most `n` more steps. -/
def loop (C : Ctx) : ℕ → St → Except (ℕ × Fault) St
  | n, s =>
    let ending := C.ops.size - 1
    if s.pc = ending ∧ s.fp = 0 then pure s
    else if ending < s.pc then throw (ending, .haltOutsideMain s.fp)
    else match n with
      | 0 => throw (s.pc, .stepLimit)
      | n + 1 => do loop C n (← step C s)

/-- The program tabulated: its instructions decoded, its hints by `pc`, its streams by name. -/
def Ctx.of (prog : LeanIsaProgram) (adv : Advice) : Except (ℕ × Fault) Ctx := do
  let ops ← (List.finRange (2 ^ prog.logSize)).mapM fun i ↦
    (decode (prog.instructions i)).elim (throw (i.val, .badInstruction)) pure
  let hints := adv.hints.foldl (fun hs (pc, h) ↦ hs.setIfInBounds pc h)
    (Array.replicate (2 ^ prog.logSize) [])
  pure ⟨ops.toArray, hints, Std.HashMap.ofList (adv.streams.map fun (n, es) ↦ (n, es.toArray))⟩

/-- The final memory image: a written cell's value, zero elsewhere, over the least power of two
covering `used`. -/
def Mem.image (m : Mem) : (κ : ℕ) × MemoryImage κ :=
  ⟨Nat.log2 m.used.nextPowerOfTwo, fun i ↦ m.peek i.val⟩

/-- **The executor**: run `prog` on `input` with `adv`; the execution, or the `pc` and fault it
failed at. -/
def execute (prog : LeanIsaProgram) (input : PublicInput) (adv : Advice) :
    Except (ℕ × Fault) (Execution prog) := do
  let C ← Ctx.of prog adv
  if maxCells ≤ adv.mainFrame then throw (0, .outOfMemory)
  let mem : Mem := ⟨#[], #[], #[], #[], max adv.mainFrame 2⟩
  let mem ← ((mem.put 0 input.word0).bind (·.put 1 input.word1)).mapError (0, ·)
  let s ← loop C maxSteps ⟨mem, Dlog.empty.grow (max (C.ops.size + 2) adv.mainFrame), 0, 0,
    adv.mainFrame, ∅, 0⟩
  if maxCells < s.mem.used then throw (0, .outOfMemory)
  for (a, b) in s.mem.links do
    if s.mem.peek a ≠ s.mem.peek b then throw (0, .linkMismatch a b)
  let ⟨κ, img⟩ := s.mem.image
  pure ⟨κ, img, s.steps⟩

end LeanVM.Prover.Exec
