module

public import Statement.Verifier.Multilinear
public import Statement.LeanIsa
public import Statement.LeanVmVerifier

/-!
# The verifier's layout (`layout.rs`, `multilinear.rs`, `bytecode.rs`)

Every row of an instruction table names its cycle, the memory cells it touches and its instruction
by pointers, each committed one-hot in one `K` word; a table's `Links` say what its rows link
(`layout.rs`), and two chained sum-checks check every link (`crates/verifier/src/link.rs`, below).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics

/-! ### Constants (`layout.rs`; `crates/verifier/src/keccak.rs`) -/

/-- `BYTECODE_SLOT_BITS`: the stacked program has `2^BYTECODE_SLOT_BITS` slots per instruction (`layout.rs`). -/
def bytecodeSlotBits : ℕ := 4

/-- `NUM_GLOBAL_COLUMNS`: the columns no instruction table owns, first in the global numbering
(`layout.rs`). -/
def numGlobalColumns : ℕ := 3

/-- Global column `MEMORY_0` (`layout.rs`), the memory's low limb; then `MEMORY_1`, its high
limb. -/
def memory0 : ℕ := 0
def memory1 : ℕ := 1
/-- Global column `QKECCAK`, the Keccak reduction's committed column: per step, its input state's
lanes and the state after every `KECCAK_DEPTH` rounds but the last, a lane per slot, and in the
slots left over some of the `KECCAK` table's own committed columns (`qkeccak_slot`,
`layout.rs`). -/
def qkeccak : ℕ := 2

/-- `K_BITS`: a `K` word's bits (`layout.rs`). -/
def kBits : ℕ := 64

/-- `KECCAK_DEPTH`: the reduction commits a step's state every `12` rounds (`layout.rs`). -/
def keccakDepth : ℕ := 12

/-- `KeccakShape::segments`, `ROUNDS / depth` at `depth = KECCAK_DEPTH`, `ROUNDS = 24`
(`keccak.rs`). -/
def keccakSegments : ℕ := 24 / keccakDepth

/-- The bits of a segment index, `log2_ceil(shape.segments())` (`keccak.rs`). -/
def keccakSegmentBits : ℕ := log2Ceil keccakSegments

/-- `KeccakShape::slot_bits`, `log2_ceil(STATE_LANES * segments)`, `STATE_LANES = 25`
(`keccak.rs`): lane `l` of the state after `KECCAK_DEPTH · m` rounds is slot `25m + l`; the
`2^6 - 50` slots above the states carry `KECCAK` columns (`keccakSlot`). -/
def qkeccakSlotBits : ℕ := log2Ceil (25 * keccakSegments)

/-- `KECCAK_MIN_STEPS_LOG`: the reduction is sized for at least one block of `512` steps
(`layout.rs`). -/
def keccakMinStepsLog : ℕ := 9

/-- `BITS = 64 * STATE_LANES`: a state's bits (`keccak.rs`). -/
def keccakBits : ℕ := 1600

/-- `LOCAL_BITS`: a bit position is `z + 64 · lane`, in a cube of `2^11` (`keccak.rs`). -/
def keccakLocalBits : ℕ := 11

/-- `LANE_BITS`: the bits of a lane's index, `25 ≤ 2^5` (`keccak.rs`). -/
def keccakLaneBits : ℕ := 5

/-- The opcodes' numbers `OP_XOR`, `OP_MUL`, `OP_SET`, `OP_DEREF`, `OP_JUMP`, `OP_KECCAK`
(`layout.rs`). -/
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def opKeccak : ℕ := 5

/-- `N_TABLES`: the instruction tables, one per opcode (`layout.rs`). -/
def nTables : ℕ := 6

/-- `MAX_TABLE_LOG`: every size a proof announces or commits is at most `2^30` (`layout.rs`). -/
def maxTableLog : ℕ := 30

/-- `MIN_LOG_MEMORY`: the least memory a proof announces, as a log, the public input's two cells
(`layout.rs`). -/
def minLogMemory : ℕ := 1

/-- `MAX_LOG_MEMORY` (`layout.rs`). -/
def maxLogMemory : ℕ := 30

/-- `MAX_LOG_BYTECODE`: the largest bytecode, as a log of its instructions (`layout.rs`). -/
def maxLogBytecode : ℕ := 30

/-- `STATE_LANES`: a Keccak state's lanes (`crates/verifier/src/hash.rs`). -/
def keccakStateLanes : ℕ := 25

/-- `Y`, the generator of `E` over `K`: a word is `lo + y·hi` (`layout.rs`). -/
def eY : E := E.ofLimbs 0 1

/-! ### Forms (`Form`, `layout.rs`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order (the Rust's `BTreeMap` orders them by monomial; a form's value does
not depend on the order). -/
structure Form where
  /-- The monomials, each with its coefficient. -/
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the
`entry(monomial).or_default() +=` of `Form::add_scaled`). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form::add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form + Form`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form::sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form::evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `constant(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-- `layout_limb(even, odd, flag, missing)` (`layout.rs`): a cell limb holding the
column `even` in the even layout and `odd` in the odd one, as the column `flag` selects,
`a + flag·(a + b)`; a missing column is `missing`. -/
def layoutLimb (even odd : Option ℕ) (flag : ℕ) (missing : Option ℕ) : Form :=
  let a := even.orElse fun _ ↦ missing
  let b := odd.orElse fun _ ↦ missing
  if a = b then
    match a with
    | none => Form.const 0
    | some a => Form.col a
  else
    Form.sum ((match a with
      | some a => [Form.col a, Form.prod flag a]
      | none => []) ++
      (match b with
      | some b => [Form.prod flag b]
      | none => []))


/-! ### Placements (`Placement`, `multilinear.rs`) -/

/-- Where a column sits in the stacked cube (`Placement`, `multilinear.rs`): a claim's point fills
the low `variableCount` coordinates (the Rust's `variables`), the bits of `index` (a multiple of
`2^variableCount`) fixing the rest. -/
structure Placement where
  /-- `variables`: the coordinates a claim's point fills. -/
  variableCount : ℕ
  /-- `index`: the column's offset, whose bits fix the other coordinates. -/
  index : ℕ
  deriving Inhabited, DecidableEq

/-- `Placement::stack_point(point, stack_log)` (`multilinear.rs`): the stack point of a claim at row
`point`, in a stack of `2^stackLog` words. The Rust asserts `|point| = variableCount`. -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above(point)`: the equality weight of the coordinates above the window
(`multilinear.rs`). -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.length - p.variableCount))
    (point.drop p.variableCount)

/-- `stack_offsets(sizes)` (`multilinear.rs`): blocks of `2^size` words laid end to end, largest
first, ties by index; their offsets, and the log-size of the total, rounded up. -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ### Links (`layout.rs`) -/

/-- A row's step of the state chain (`StateLink`, `layout.rs`): its cycle pointer column, its
`pc` and `fp` columns, and the successor state `(pc', fp')` it derives (`next`). -/
structure StateLink where
  /-- `cycle`: the cycle pointer column. -/
  cycle : ℕ
  /-- `pc`: the `pc` column. -/
  pc : ℕ
  /-- `fp`: the `fp` column. -/
  fp : ℕ
  /-- `next`: the successor's `pc` and `fp`. -/
  next : Form × Form
  deriving Inhabited

/-- A row's read of the program (`BytecodeLink`, `layout.rs`): its pointer column, its `pc`
column, its opcode, and each operand equation `Σ_{s ∈ slots} BC_s = form` it checks against its
instruction, weighed by the first slot's challenge. A slot no equation names is read only through
the accesses' `Read`s. -/
structure BytecodeLink where
  /-- `pointer`: the program pointer column. -/
  pointer : ℕ
  /-- `pc`: the `pc` column. -/
  pc : ℕ
  /-- `opcode`: the table's opcode. -/
  opcode : ℕ
  /-- `operands`: each equation's slots and form. -/
  operands : List (List ℕ × Form)
  deriving Inhabited

/-- A term of an access's value that the row reads where one of its pointers points, rather than
from its columns (`Read`, `layout.rs`). -/
inductive Read where
  /-- `Read::Word`: `scale·word(σ)`, the word in the cell the row's pointer column `pointer` names;
  `scale` has degree at most one. -/
  | word (pointer : ℕ) (scale : Form)
  /-- `Read::Slot`: `scale·BC_slot(σ_bc)`, a slot of the row's instruction. -/
  | slot (slot : ℕ) (scale : E)
  /-- `Read::Frame`: `scale·fp·BC_slot(σ_bc)`. -/
  | frame (slot : ℕ) (scale : E)
  /-- `Read::Pc`: `scale·pc·BC_slot(σ_bc)`, where `pc = g^σ_bc`. -/
  | pc (slot : ℕ) (scale : E)
  deriving Inhabited

/-- A row's memory access (`Access`, `layout.rs`): its pointer column and how far past the
pointer's cell it reads, the column gating it if any, the address, and the word `lo + y·hi`. The
address is `address + g^e·fp·BC_slot(σ_bc)` for `frame = some (slot, e)`, and the word is
`value + Σ reads`. A gated access reads nothing: its coefficients already hold the gate. -/
structure Access where
  /-- `pointer`: the pointer column. -/
  pointer : ℕ
  /-- `shift`: the cells past the pointer's cell it reads, inside the pointer's window. -/
  shift : ℕ
  /-- `gate`: the column gating it, if any. -/
  gate : Option ℕ
  /-- `address`: the address's committed part. -/
  address : Form
  /-- `frame`: the slot and exponent of the address's `g^e·fp·BC_slot(σ_bc)`, if any. -/
  frame : Option (ℕ × ℕ)
  /-- `value`: the word's committed part. -/
  value : Form
  /-- `reads`: the word's terms read through pointers. -/
  reads : List Read
  deriving Inhabited

/-- Everything a table links, over its own local column indices (`Links`, `layout.rs`): the state
link, the program link, and the memory accesses. The Rust's `Links::default()` has neither link
until its table sets them, and `state()` and `bytecode_link()` expect both (`Links.stateLink`,
`Links.bytecodeLink`). -/
structure Links where
  /-- `state`: the state link. -/
  state : Option StateLink := none
  /-- `bytecode`: the program link. -/
  bytecode : Option BytecodeLink := none
  /-- `memory`: the memory accesses, in order. -/
  memory : List Access := []
  deriving Inhabited

/-- `Links::state()` (`layout.rs`): the state link, which every table sets. -/
def Links.stateLink (links : Links) : StateLink := links.state.getD default

/-- `Links::bytecode_link()` (`layout.rs`): the program link, which every table sets. -/
def Links.bytecodeLink (links : Links) : BytecodeLink := links.bytecode.getD default

/-- `Links::state_derived(cycle, pc, fp, npc, nfp)` (`layout.rs`): set the state link, the successor
`(npc, nfp)`. -/
def Links.stateDerived (links : Links) (cycle pc fp : ℕ) (npc nfp : Form) : Links :=
  { links with state := some { cycle := cycle, pc := pc, fp := fp, next := (npc, nfp) } }

/-- `Links::state_step(cycle, pc, fp)` (`layout.rs`): the successor `(g·pc, fp)`. -/
def Links.stateStep (links : Links) (cycle pc fp : ℕ) : Links :=
  links.stateDerived cycle pc fp (Form.col pc 1) (Form.col fp 0)

/-- `Links::bytecode(pc, pointer, opcode, operands)` (`layout.rs`): set the program link. -/
def Links.setBytecode (links : Links) (pc pointer opcode : ℕ) (operands : List (List ℕ × Form)) :
    Links :=
  { links with bytecode := some { pointer := pointer, pc := pc, opcode := opcode, operands := operands } }

/-- `Links::access(pointer, shift, gate, address, frame, value, reads)` (`layout.rs`): append a
memory access (the Rust asserts a gated access has no frame and no reads, which every table
meets). -/
def Links.access (links : Links) (pointer shift : ℕ) (gate : Option ℕ) (address : Form)
    (frame : Option (ℕ × ℕ)) (value : Form) (reads : List Read) : Links :=
  let access : Access :=
    { pointer := pointer, shift := shift, gate := gate, address := address, frame := frame
      value := value, reads := reads }
  { links with memory := links.memory ++ [access] }

/-- `Links::framed(pointer, slot, value, reads)` (`layout.rs`): an ungated access to the cell at
`fp·BC_slot(σ_bc)`. -/
def Links.framed (links : Links) (pointer slot : ℕ) (value : Form) (reads : List Read) : Links :=
  links.access pointer 0 none {} (some (slot, 0)) value reads

/-- `Links::pointers()` (`layout.rs`): the pointer columns in the order Hotwire numbers them, the
cycle, the bytecode, then each access's pointer in order of first use (the Rust looks for it among
the access pointers already listed, `out[2..]`). -/
def Links.pointers (links : Links) : List ℕ :=
  links.memory.foldl (fun out access ↦
      if (out.drop 2).contains access.pointer then out else out ++ [access.pointer])
    [links.stateLink.cycle, links.bytecodeLink.pointer]

/-- `Links::max_shift()` (`layout.rs`): the largest shift any access takes, `0` for none. -/
def Links.maxShift (links : Links) : ℕ := (links.memory.map (·.shift)).foldl max 0

/-! ### The instruction tables (`Table`, `layout.rs`) -/

/-- One instruction's table: its opcode, its columns, the row a padding row holds, its links and its
constraints (`Table`, `layout.rs`). -/
structure Table where
  /-- `opcode`: also its index in `tables()`, so `g^opcode` is its bytecode tag. -/
  opcode : ℕ
  /-- `columns`: its columns' names, in order. -/
  columns : List String
  /-- `padding`: the row a padding row holds. -/
  padding : List E
  /-- `links`: what its rows link. -/
  links : Links
  /-- `constraints`: its constraints, as a function of a row's values. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-! ### The layout (`Layout`, `layout.rs`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes (`Layout`,
`layout.rs`). The Rust's `keccak`, the Keccak reduction's shape, is `tableLogHeights[OP_KECCAK]`
steps at depth `KECCAK_DEPTH`, read off the heights. -/
structure Layout where
  /-- `log_memory`: the memory's log-size, `κ`. -/
  logMemory : ℕ
  /-- `log_bytecode`: the program's log-size, in instructions of `2^BYTECODE_SLOT_BITS` slots. -/
  logBytecode : ℕ
  /-- `bytecode`: the stacked program's words. -/
  bytecode : List K
  /-- `tables`: the instruction tables, in opcode order. -/
  tables : List Table
  /-- `table_rows`: each table's announced row count. -/
  tableRows : List ℕ
  /-- `placements`: every global column's placement; `none` for a column nothing commits, the
  `KECCAK` output lanes. -/
  placements : List (Option Placement)
  /-- `stack_log`: the stack's log-size. -/
  stackLog : ℕ
  /-- `table_log_heights`: each table's log-height, the least `h` with `rows ≤ 2^h`, at least its
  floor. -/
  tableLogHeights : List ℕ
  deriving Inhabited

/-! ### The tables and their links (`tables()`, `layout.rs`) -/

/-- `cols(columns, names)`, one name: the index of a column by name (every name the tables use is
in its list, as the Rust's `expect` checks, `layout.rs`). -/
def colIndex (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `word(pointer)`: `1·word(σ)`, the word in the cell the pointer column `pointer` names
(`layout.rs`). -/
def readWord (pointer : ℕ) : Read := .word pointer (Form.const 1)

/-- `XOR_COLUMNS` (`layout.rs`). -/
def xorColumns : List String := ["pc", "fp", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]

/-- `MUL_COLUMNS` (`layout.rs`). -/
def mulColumns : List String :=
  ["pc", "fp", "a_0", "a_1", "ix_a", "ix_b", "ix_c", "ix_bc", "ix_cycle"]

/-- `SET_COLUMNS` (`layout.rs`). -/
def setColumns : List String := ["pc", "fp", "ix", "ix_bc", "ix_cycle"]

/-- `DEREF_COLUMNS` (`layout.rs`). -/
def derefColumns : List String :=
  ["pc", "fp", "ptr", "o2", "s", "ix_ptr", "ix_target", "ix_local", "ix_bc", "ix_cycle"]

/-- `JUMP_COLUMNS` (`layout.rs`). -/
def jumpColumns : List String :=
  ["pc", "fp", "v_cond", "v_pc", "v_fp", "pc_next", "fp_next", "w", "b", "ix_c", "ix_d", "ix_f",
    "ix_bc", "ix_cycle"]

/-- `links_arith(opcode, multiply)` (`layout.rs`): `XOR` and `MUL`, whose operands sit in slots
`4, 5, 6`. `XOR` reads `a` and `b` where their pointers point and checks `c = a + b`; `MUL` commits
`a = a_0 + y·a_1`, reads `b`, and checks `c = a·b`, linear in that read. -/
def linksArith (opcode : ℕ) (multiply : Bool) : Links :=
  let columns := if multiply then mulColumns else xorColumns
  let c := colIndex columns
  let (pc, fp, ixA, ixB, ixC, ixBc, ixCycle) :=
    (c "pc", c "fp", c "ix_a", c "ix_b", c "ix_c", c "ix_bc", c "ix_cycle")
  let links := (({} : Links).stateStep ixCycle pc fp).setBytecode pc ixBc opcode []
  if multiply then
    let a := (Form.col (c "a_0") 0).add ⟨[([c "a_1"], eY)]⟩
    ((links.framed ixA 4 a []).framed ixB 5 {} [readWord ixB]).framed ixC 6 {} [.word ixB a]
  else
    ((links.framed ixA 4 {} [readWord ixA]).framed ixB 5 {} [readWord ixB]).framed ixC 6 {}
      [readWord ixA, readWord ixB]

/-- `links_set()` (`layout.rs`): the stored immediate's two limbs are slots `5` and `6` of the
instruction. -/
def linksSet : Links :=
  let c := colIndex setColumns
  let links := (({} : Links).stateStep (c "ix_cycle") (c "pc") (c "fp")).setBytecode (c "pc")
    (c "ix_bc") opSet []
  links.framed (c "ix") 4 {} [.slot 5 1, .slot 6 eY]

/-- `links_deref()` (`layout.rs`): `s = f_pc + f_fp` (slots `7, 8`), and the store
`v2 = (1 + s)·v3 + f_pc·(g²·pc) + f_fp·fp`. -/
def linksDeref : Links :=
  let c := colIndex derefColumns
  let (pc, fp, ptr, o2, s) := (c "pc", c "fp", c "ptr", c "o2", c "s")
  let (ixPtr, ixTarget, ixLocal, ixBc, ixCycle) :=
    (c "ix_ptr", c "ix_target", c "ix_local", c "ix_bc", c "ix_cycle")
  let links := (({} : Links).stateStep ixCycle pc fp).setBytecode pc ixBc opDeref
    [([5], Form.col o2 0), ([7, 8], Form.col s 0)]
  let links := links.framed ixPtr 4 (Form.col ptr 0) []
  let store : List Read :=
    [.word ixLocal ((Form.const 1).add (Form.col s 0)), .pc 7 (gpow 2), .frame 8 1]
  let links := links.access ixTarget 0 none (Form.prod ptr o2 0) none {} store
  links.framed ixLocal 6 {} [readWord ixLocal]

/-- `links_jump()` (`layout.rs`): the successor is committed (`pc_next`, `fp_next`), so the state
link stays affine; the three words, `K`-valued on every row, are committed in one lane. -/
def linksJump : Links :=
  let c := colIndex jumpColumns
  let (pc, fp, cond, dest, frame, pcNext, fpNext) :=
    (c "pc", c "fp", c "v_cond", c "v_pc", c "v_fp", c "pc_next", c "fp_next")
  let (ixC, ixD, ixF, ixBc, ixCycle) := (c "ix_c", c "ix_d", c "ix_f", c "ix_bc", c "ix_cycle")
  let links := (({} : Links).stateDerived ixCycle pc fp (Form.col pcNext 0)
    (Form.col fpNext 0)).setBytecode pc ixBc opJump []
  ((links.framed ixC 4 (Form.col cond 0) []).framed ixD 5 (Form.col dest 0) []).framed ixF 6
    (Form.col frame 0) []

/-- `jump_constraints(columns)` (`layout.rs`): `b = [cond ≠ 0]` by its inverse `w`, and the
successor `b·(v_pc, v_fp) + (1 + b)·(g·pc, fp)`. -/
def jumpConstraints (columns : List E) : List E :=
  let v := fun name ↦ columns.getD (colIndex jumpColumns name) 0
  let flag := v "b"
  let untaken := flag + 1
  [flag + v "v_cond" * v "w",
    v "v_cond" * untaken,
    v "pc_next" + flag * v "v_pc" + untaken * gpow 1 * v "pc",
    v "fp_next" + flag * v "v_fp" + untaken * v "fp"]

/-- `KECCAK_CELLS`: a sponge state's cells, read then written (`layout.rs`). -/
def keccakCells : ℕ := 13

/-- `keccak_cell_lanes(odd)` (`layout.rs`): the lanes each of a sponge state's thirteen cells holds,
`(lo, hi)`, `none` for a limb that holds no lane: nine rate cells, lanes `0..16` two to a cell then
lane `16` in a low limb (even), or lane `0` in a high limb then lanes `1..17` two to a cell (odd),
then the capacity lanes `17..25`. -/
def keccakCellLanes (odd : Bool) : List (Option ℕ × Option ℕ) :=
  (List.range keccakCells).map fun cell ↦
    if 9 ≤ cell ∨ (odd ∧ 1 ≤ cell) then (some (2 * cell - 1), some (2 * cell))
    else if odd then (none, some 0)
    else if cell = 8 then (some 16, none)
    else (some (2 * cell), some (2 * cell + 1))

/-- `keccak_offset_slot(i)` (`layout.rs`): the bytecode slot of `KECCAK`'s offset operand `i`, in
the order `m0..m3, tail, b8, cap, out`. -/
def keccakOffsetSlot (i : ℕ) : ℕ := 4 + i

/-- `KECCAK_HEAD`: `KECCAK`'s columns before its lanes (`layout.rs`). -/
def keccakHead : List String :=
  ["pc", "fp", "o_out", "odd_in", "odd_out", "out_two", "out_all", "free"]

/-- `KECCAK_IN`: the local column of input lane `0` (`layout.rs`). -/
def keccakIn : ℕ := keccakHead.length

/-- `KECCAK_OUT`: the local column of output lane `0` (`layout.rs`). -/
def keccakOut : ℕ := keccakIn + keccakStateLanes

/-- `KECCAK_IX`: the local column of the first cell pointer, `ix_m0` (`layout.rs`). -/
def keccakIx : ℕ := keccakOut + keccakStateLanes

/-- `KECCAK_IX_BC`: the program pointer (`layout.rs`). -/
def keccakIxBc : ℕ := keccakIx + 8

/-- `KECCAK_CYCLE`: the cycle pointer, the last column (`layout.rs`). -/
def keccakCycle : ℕ := keccakIxBc + 1

/-- `links_keccak()` (`layout.rs`). The seven read offsets ride the instruction alone; `out` and the
four flags are operand equations on slots `11..16`. The thirteen cells read (the four addressed
ones, the tail run, `b8`, the cap run), then the thirteen written, each holding its lanes in the
layout its flag names: a read cell's free limb is the column `free`, a written one's zero. A read
cell is framed at its operand's slot, `step` cells past the operand's cell, through the pointer
`KECCAK_IX + operand`; written cell `c` is at `fp·o_out + c`, `c` past `ix_out`'s cell, cell `0`
always written, cell `1` gated by `out_two`, cells `2..13` by `out_all`. -/
def linksKeccak : Links :=
  let h := colIndex keccakHead
  let (pc, fp, free, oOut) := (h "pc", h "fp", h "free", h "o_out")
  let (inOdd, outOdd, outTwo, outAll) := (h "odd_in", h "odd_out", h "out_two", h "out_all")
  let operands := [oOut, inOdd, outOdd, outTwo, outAll].zipIdx.map fun (c, i) ↦
    ([keccakOffsetSlot 7 + i], Form.col c 0)
  let links := (({} : Links).stateStep keccakCycle pc fp).setBytecode pc keccakIxBc opKeccak operands
  let part := fun cell : ℕ ↦
    if cell < 4 then (cell, 0) else if cell < 8 then (4, cell - 4) else if cell = 8 then (5, 0)
    else (6, cell - 9)
  let even := keccakCellLanes false
  let odd := keccakCellLanes true
  let sides : List (ℕ × ℕ × ℕ × Option ℕ) := [(0, keccakIn, inOdd, some free), (1, keccakOut, outOdd, none)]
  sides.foldl (fun links (side, lanes, flag, missing) ↦
    let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
    (List.range keccakCells).foldl (fun links cell ↦
      let limb := fun (e o : Option ℕ) ↦ layoutLimb (lane e) (lane o) flag missing
      let (e, o) := (even.getD cell (none, none), odd.getD cell (none, none))
      let value := (limb e.1 o.1).addScaled (limb e.2 o.2) eY
      if side = 0 then
        let (operand, step) := part cell
        links.access (keccakIx + operand) step none {} (some (keccakOffsetSlot operand, step)) value
          []
      else
        let gate := if cell = 0 then none else if cell = 1 then some outTwo else some outAll
        links.access (keccakIx + 7) cell gate (Form.prod fp oOut cell) none value []) links) links

/-- `keccak_columns()` (`layout.rs`): `KECCAK_HEAD`, the input lanes `in_l`, the output lanes
`out_l`, a pointer `ix_c` for each cell operand, `ix_bc` and `ix_cycle`. The fifty value lanes are
not committed in the table: an input lane is one of `q_keccak`'s slots, and the output lanes' claims
are the Keccak reduction's claim on the output. -/
def keccakColumns : List String :=
  let lanes := fun (name : String) ↦ (List.range keccakStateLanes).map fun l ↦ name ++ "_" ++ toString l
  keccakHead ++ lanes "in" ++ lanes "out" ++
    (["m0", "m1", "m2", "m3", "tail", "b8", "cap", "out"].map ("ix_" ++ ·)) ++ ["ix_bc", "ix_cycle"]

/-- `spare_local(k)` (`layout.rs`): the local `KECCAK` column riding spare slot `k` of
`q_keccak`, its committed columns in local order, the ones before the value lanes then the pointers
after them. -/
def spareLocal (k : ℕ) : ℕ := if k < keccakIn then k else keccakIx + (k - keccakIn)

/-- `QKECCAK_SLOTS = STATE_LANES * (ROUNDS / KECCAK_DEPTH)`: the slots of `q_keccak` the committed
states occupy (`layout.rs`). -/
def qkeccakSlots : ℕ := keccakStateLanes * keccakSegments

/-- `QKECCAK_SPARE`: the slots of `q_keccak` the states leave over (`layout.rs`). -/
def qkeccakSpare : ℕ := 2 ^ log2Ceil qkeccakSlots - qkeccakSlots

/-- `tables()` (`layout.rs`), in opcode order. A padding row is zero, but for `KECCAK`'s output
lanes `KECCAK_OUT …`: a padding row permutes zeros (`keccak_f` of the zero state). -/
def tables : List Table :=
  let table := fun (opcode : ℕ) (columns : List String) (links : Links)
      (constraints : List E → List E) ↦
    ({ opcode := opcode, columns := columns, padding := List.replicate columns.length 0
       links := links, constraints := constraints } : Table)
  let output := keccakF1600 (Vector.replicate 25 0)
  let keccak := table opKeccak keccakColumns linksKeccak fun _ ↦ []
  let keccak := { keccak with
    padding := keccak.padding.zipIdx.map fun (p, i) ↦
      if keccakOut ≤ i ∧ i < keccakOut + keccakStateLanes then
        eOfNat (Keccak.lane output (i - keccakOut)).toNat
      else p }
  [table opXor xorColumns (linksArith opXor false) fun _ ↦ [],
    table opMul mulColumns (linksArith opMul true) fun _ ↦ [],
    table opSet setColumns linksSet fun _ ↦ [],
    table opDeref derefColumns linksDeref fun _ ↦ [],
    table opJump jumpColumns linksJump jumpConstraints,
    keccak]

/-- `Table::width` (`layout.rs`). -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table::n_constraints` (`layout.rs`): the constraints' count, at the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `TABLE_WIDTHS` (`layout.rs`). -/
def tableWidths : List ℕ :=
  [xorColumns.length, mulColumns.length, setColumns.length, derefColumns.length,
    jumpColumns.length, keccakCycle + 1]

/-- `GLOBAL_COLUMN_BASES`: each table's first global column, after the global columns
(`layout.rs`). -/
def globalColumnBases : List ℕ :=
  (List.range nTables).map fun t ↦ numGlobalColumns + (tableWidths.take t).sum

/-- `TABLE_LOG_FLOORS` (`layout.rs`): each table's least log-height, `0` but for `KECCAK`, the
Keccak reduction's block of steps. -/
def tableLogFloors : List ℕ := [0, 0, 0, 0, 0, keccakMinStepsLog]

/-- `qkeccak_slot(column)` (`layout.rs`): the slot of `q_keccak` the global column is, if it is
one: one of `KECCAK`'s own columns riding a spare slot past the committed states (`spareLocal`), or
an input lane (slot = lane); `none` for every other column, those below the `KECCAK` base among
them (where the Rust's `checked_sub` fails). -/
def qkeccakSlot (column : ℕ) : Option ℕ :=
  let base := globalColumnBases.getD opKeccak 0
  if base ≤ column then
    let loc := column - base
    match (List.range qkeccakSpare).find? (spareLocal · = loc) with
    | some k => some (qkeccakSlots + k)
    | none => if keccakIn ≤ loc ∧ loc < keccakOut then some (loc - keccakIn) else none
  else none

/-- `column_kappas(tables, log_memory, table_log_heights)` (`layout.rs`): every column's
log-size, in global order: the memory's two limbs, `q_keccak`'s (the `KECCAK` table's steps times
`2^slot_bits` slots), then each table's block. -/
def columnKappas (tables : List Table) (logMemory : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  [logMemory, logMemory, tableLogHeights.getD opKeccak 0 + qkeccakSlotBits] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- What a stack block's log-size is, in terms of the announced sizes (`SizeSource`,
`layout.rs`). -/
inductive SizeSource where
  /-- `SizeSource::Memory`. -/
  | memory
  /-- `SizeSource::Table(opcode)`. -/
  | table (opcode : ℕ)
  deriving Inhabited, DecidableEq

/-- A column with a block of its own in the stack (`StackBlock`, `layout.rs`): its log-size is its
source's plus `adj`. -/
structure StackBlock where
  /-- `column`: the global column. -/
  column : ℕ
  /-- `source`: what its log-size derives from. -/
  source : SizeSource
  /-- `adj`: its log-size past its source's. -/
  adj : ℕ
  deriving Inhabited, DecidableEq

/-- `stack_blocks()` (`layout.rs`): the stack's blocks, in global column order: the memory's two
limbs, `q_keccak`, then every table column that `q_keccak` does not carry (`qkeccakSlot`) and that
is not a `KECCAK` output lane, which nothing commits. -/
def stackBlocks : List StackBlock :=
  let keccakBase := globalColumnBases.getD opKeccak 0
  let isOutput := fun column : ℕ ↦
    keccakBase + keccakOut ≤ column ∧ column < keccakBase + keccakOut + keccakStateLanes
  [⟨memory0, .memory, 0⟩, ⟨memory1, .memory, 0⟩,
    ⟨qkeccak, .table opKeccak, log2Ceil qkeccakSlots⟩] ++
  tables.flatMap fun t ↦
    let base := globalColumnBases.getD t.opcode 0
    ((List.range t.width).filter fun l ↦
        (qkeccakSlot (base + l)).isNone && !decide (isOutput (base + l))).map fun l ↦
      ⟨base + l, .table t.opcode, 0⟩

/-- `stack(kappas)` (`layout.rs`): each stacked column's offset, by global column, and the stack's
log-size, at least `MIN_STACKED_LOG`. -/
def stack (kappas : List ℕ) : List (ℕ × ℕ) × ℕ :=
  let blocks := stackBlocks
  let (offsets, totalLog) := stackOffsets (blocks.map fun b ↦ kappas.getD b.column 0)
  ((blocks.map (·.column)).zip offsets, max Whir.minLogStack totalLog)

/-- `min_execution_stacked_log(log_bytecode)` (`layout.rs`): the stack of the smallest execution,
the least memory and every table at its floor. The program has no committed column, so the stack
does not depend on its size. -/
def minExecutionStackedLog (_logBytecode : ℕ) : ℕ :=
  (stack (columnKappas tables minLogMemory tableLogFloors)).2

/-- `build_layout(bytecode, log_memory, table_rows)` (`layout.rs`); `none` exactly where the Rust
returns an error: a bytecode whose length is not a power of two (`log2_strict`) or whose log-length
is outside `BYTECODE_SLOT_BITS ..= MAX_LOG_BYTECODE + BYTECODE_SLOT_BITS`, a memory outside
`MIN_LOG_MEMORY ..= MAX_LOG_MEMORY`, or a table of more than `2^MAX_TABLE_LOG` rows. It is also
`none` on row counts not one per table, which the verifier never passes (it reads `N_TABLES` of
them). A table's log-height is the least `h` with `rows ≤ 2^h` (`log2Ceil`), at least its floor. A
column with a block has its block's placement; a column `q_keccak` carries is the rows of its slot
in `q_keccak`'s block, at `q_keccak`'s offset plus `slot · 2^kappa`; a `KECCAK` output lane has
none. -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if minLogMemory ≤ logMemory ∧ logMemory ≤ maxLogMemory ∧
        tableRows.all (· ≤ 2 ^ maxTableLog) ∧ bytecodeSlotBits ≤ logLength ∧
        logLength ≤ maxLogBytecode + bytecodeSlotBits ∧ tableRows.length = nTables then
      let logBytecode := logLength - bytecodeSlotBits
      let tableLogHeights :=
        List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows tableLogFloors
      let kappas := columnKappas tables logMemory tableLogHeights
      let (offsets, stackLog) := stack kappas
      let placements := kappas.zipIdx.map fun (kappa, column) ↦
        let index := match qkeccakSlot column with
          | some slot => (offsets.lookup qkeccak).map (· + (slot <<< kappa))
          | none => offsets.lookup column
        index.map fun index ↦ ({ variableCount := kappa, index := index } : Placement)
      some { logMemory := logMemory, logBytecode := logBytecode, bytecode := bytecode
             tables := tables, tableRows := tableRows, placements := placements
             stackLog := stackLog, tableLogHeights := tableLogHeights }
    else none

/-! ### The program's split (`Split`, `bytecode.rs`) -/

/-- The program's slots split by opcode at a point over the instructions, what `Bytecode::split`
returns (`Split`, `bytecode.rs`), one entry per opcode `F`: `count[F] = Σ_k eq(point, k)·[op_k = F]`;
`slots[F][s] = Σ_k eq(point, k)·[op_k = F]·BC_s(k)` for the operand slots `s ≥ 4`, `2^BYTECODE_SLOT_BITS`
entries; `pc[F][s]`, the same with `g^k` inside the sum, for the `(F, s)` asked for, zero
elsewhere. -/
structure Split where
  /-- `count`: each opcode's weight. -/
  count : List E
  /-- `slots`: each opcode's slots. -/
  slots : List (List E)
  /-- `pc`: each opcode's slots read times `pc`. -/
  pc : List (List E)
  deriving Inhabited

/-- An instruction's opcode from its slot `3`, `2^opcode` (`slot(3).trailing_zeros()`,
`Bytecode::new`, `bytecode.rs`): the lowest set bit, `64` for a zero word. A valid program's
(`is_valid_encoding_of_a_leanisa_program`, which `Bytecode::new` checks) is below `N_TABLES`. -/
def opcodeOf (word : K) : ℕ :=
  ((List.range 64).find? fun i ↦ (kToNat word >>> i) % 2 = 1).getD 64

/-- `pc_slots(tables)` (`link.rs`): the `(opcode, slot)` pairs any table reads times `pc`
(`Read::Pc`), in table and access order. -/
def pcSlots (tables : List Table) : List (ℕ × ℕ) :=
  tables.flatMap fun t ↦ t.links.memory.flatMap fun access ↦ access.reads.filterMap fun
    | .pc slot _ => some (t.opcode, slot)
    | _ => none

/-- What `Bytecode::split(point, pc)` returns (`bytecode.rs`), as its specification, the sums over
the program's `n = len / 2^BYTECODE_SLOT_BITS` instructions `k` with the weights `eq(point, k)`
(`eqKernel`), the instruction's opcode `op_k` from slot `3` (`opcodeOf`) and slot `s` of instruction
`k` the word `s·n + k`: `count[F] = Σ_k eq·[op_k = F]`; `slots[F][s] = Σ_k eq·[op_k = F]·BC_s(k)` for
`s ≥ 4`, zero below; `pc[F][s] = Σ_k eq·[op_k = F]·g^k·BC_s(k)` for `s ≥ 4` and `(F, s)` in `pc`,
zero elsewhere; `F` over the opcodes `0 ..= OP_KECCAK`. The Rust groups the instructions by
`(opcode, slot, word)` within blocks of `2^14` and weighs each block's sums once, the same values
(its `split_matches_a_sum_over_instructions` test); `g^k` is `K`'s, `ofK` of it is `gpow k`. -/
def splitAt (bytecode : List K) (point : List E) (pc : List (ℕ × ℕ)) : Split :=
  let n := bytecode.length >>> bytecodeSlotBits
  let slot := fun (s k : ℕ) ↦ bytecode.getD (s * n + k) 0
  let rows := ((eqKernel point).zip (powers gen (2 ^ point.length))).zipIdx
  let ops := List.range (opKeccak + 1)
  let sumOp := fun (F : ℕ) (term : E → E → ℕ → E) ↦
    sumE (rows.map fun ((e, gk), k) ↦ if opcodeOf (slot 3 k) = F then term e gk k else 0)
  { count := ops.map fun F ↦ sumOp F fun e _ _ ↦ e
    slots := ops.map fun F ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      if 4 ≤ s then sumOp F fun e _ k ↦ e * ofK (slot s k) else 0
    pc := ops.map fun F ↦ (List.range (2 ^ bytecodeSlotBits)).map fun s ↦
      if 4 ≤ s ∧ pc.contains (F, s) then sumOp F fun e gk k ↦ e * (gk * ofK (slot s k)) else 0 }

/-- A column claim: the global column's multilinear extension at `point` (over the column's own
variables) is `value` (`ColumnClaim`, `lib.rs`). -/
structure ColumnClaim where
  /-- The global column. -/
  column : ℕ
  /-- The point, over the column's own variables. -/
  point : List E
  /-- The claimed value. -/
  value : E
  deriving Inhabited

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it
(`StackClaim`, `lib.rs`). -/
abbrev StackClaim : Type := (List E → E) × E

end LeanVM.Protocol.Verifier

end
