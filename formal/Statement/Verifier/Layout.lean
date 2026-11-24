module

public import Statement.Verifier.Multilinear
public import Statement.LeanIsa
public import Statement.LeanVmVerifier

/-!
# The verifier's layout (`multilinear.rs`, `layout.rs`, `bus.rs`)
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics

/-! ### Constants (`layout.rs`;
`crates/verifier/src/keccak.rs`) -/

/-- `BUS_BITS`: the bus communicates tuples of `2^BUS_BITS` field elements (`layout.rs`). -/
def busBits : ℕ := 4

/-- `NUM_GLOBAL_COLUMNS`: the columns no instruction table owns, first in the global numbering
(`layout.rs`). -/
def globalColumnCount : ℕ := 5

/-- Global column `MEMORY_0` (`layout.rs`), the memory's low limb; then `MEMORY_1`, its high
limb, `MEMORY_FINAL_COUNTERS`, `BYTECODE_FINAL_COUNTERS`. -/
def memory0 : ℕ := 0
def memory1 : ℕ := 1
def memoryFinalCounters : ℕ := 2
def bytecodeFinalCounters : ℕ := 3
/-- Global column `QKECCAK`, the Keccak reduction's committed column: per step, its input state's
lanes and the state after every `KECCAK_DEPTH` rounds but the last, a lane per slot, and in the
slots left over the `KECCAK` table's own first committed columns (`keccakSlot`; `layout.rs`). -/
def qkeccak : ℕ := 4

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

/-- The bus separators `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE` (`layout.rs`). -/
def sepState : E := 1
def sepMem : E := gen
def sepBytecode : E := gen ^ 2

/-- The opcodes' numbers `OP_XOR`, `OP_MUL`, `OP_SET`, `OP_DEREF`, `OP_JUMP`, `OP_KECCAK`
(`layout.rs`). -/
def opXor : ℕ := 0
def opMul : ℕ := 1
def opSet : ℕ := 2
def opDeref : ℕ := 3
def opJump : ℕ := 4
def opKeccak : ℕ := 5

/-! ### Placements (`Placement`, `multilinear.rs`) -/

/-- Where something sits in the stacked cube: a claim's point fills the low `variableCount`
coordinates, the bits of the selector `index` fixing the rest. -/
structure Placement where
  /-- The coordinates the claim's point fills. -/
  variableCount : ℕ
  /-- The selector whose bits fix the other coordinates. -/
  index : ℕ
  deriving Inhabited, DecidableEq

/-- `Placement::stack_point`: the point on the stacked cube (`multilinear.rs`). -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  point ++ selectorPoint (p.index >>> p.variableCount) (stackLog - p.variableCount)

/-- `Placement::eq_above`: the equality weight of the coordinates above the window
(`multilinear.rs`). -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  eqEval (selectorPoint (p.index >>> p.variableCount) (point.length - p.variableCount))
    (point.drop p.variableCount)

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`multilinear.rs`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

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

/-! ### Flushes (`Flushes`, `layout.rs`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  /-- The tuples pushed. -/
  push : List (List Form) := []
  /-- The tuples pulled, each paired with the push at its position. -/
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes::pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes::state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes::state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes::counted`: a pull at `count` and a push at `counter`, the same otherwise. -/
def counted (f : Flushes) (pre : List Form) (counter : Form) (count : ℕ) (suffix : List Form) :
    Flushes :=
  f.pair (pre ++ [counter] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes::bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] (Form.col count 1) count
    (Form.const (gpow opcode) :: operands)

/-- `Flushes::memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] (Form.col count 1) count values

/-- `Flushes::memory_if`: `memory` when the column `flag` is `1`. The push's counter is
`count·(1 + flag·(g + 1))`: `g·count` at `1`, and the pull's `count` at `0`, so the pair cancels
and touches no cell. -/
def memoryIf (f : Flushes) (flag : ℕ) (address : Form) (count : ℕ) (values : List Form) :
    Flushes :=
  f.counted [Form.const sepMem, address]
    (Form.sum [Form.col count, Form.prod flag count 1, Form.prod flag count]) count values

/-- `Flushes::memory_cols`: the columns, a missing high limb zero. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (2 - columns.length) (Form.const 0))

end Flushes

/-! ### The instruction tables (`layout.rs`) -/

/-- `cols(columns, names)`, one name: the index of a column by name (every name the tables use is
in its list, as the Rust's `expect` checks, `layout.rs`). -/
def columnIndexByName (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS` (`layout.rs`). -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "vb_0", "vb_1", "cnt_a", "cnt_b", "cnt_c",
    "cnt_bc"]

/-- `SET_COLUMNS` (`layout.rs`). -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS` (`layout.rs`). -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "cnt_ptr", "cnt_target",
    "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS` (`layout.rs`). -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- The decimal numeral of `n` (`format!`'s `{}`): its digits below `100`, the column names'
numbers (`toString` past them). -/
def decimalNumeral (n : ℕ) : String :=
  if n < 10 then (Char.ofNat (48 + n)).toString
  else if n < 100 then (Char.ofNat (48 + n / 10)).toString ++ (Char.ofNat (48 + n % 10)).toString
  else toString n

/-- The names of the `25` lanes of a state, with a prefix: `prefix_0, …, prefix_24`. -/
def laneNames (namePrefix : String) : List String :=
  (List.range 25).map fun l ↦ namePrefix ++ "_" ++ decimalNumeral l

/-- `keccak_columns()` (`layout.rs`): the operands, the layout flags, the
bytecode's flags for the output cells written (`out_two`: cell `1`; `out_all`: cells `2…12`), the
read limb that holds no lane (`free`), the fifty value lanes (`in_l`, one of `q_keccak`'s slots
each; `out_l`, claimed by the Keccak reduction, committed nowhere), then the read counts. The
first `QKECCAK_SPARE` (`14`) committed columns, `pc` through `out_all`, ride `q_keccak`'s spare
slots `50…63` (`keccakSlotOf`). -/
def keccakColumns : List String :=
  ["pc", "fp", "o_m0", "o_m1", "o_m2", "o_m3", "o_tail", "o_b8", "o_cap", "o_out", "odd_in",
    "odd_out", "out_two", "out_all", "free"] ++ laneNames "in" ++ laneNames "out" ++
    (List.range 26).map (fun c ↦ "cnt_" ++ decimalNumeral c) ++ ["cnt_bc"]

/-- `KECCAK_IN` (`layout.rs`): the local column of input lane `0`. -/
def keccakIn : ℕ := columnIndexByName keccakColumns "in_0"

/-- `KECCAK_OUT` (`layout.rs`): the local column of output lane `0`. -/
def keccakOut : ℕ := columnIndexByName keccakColumns "out_0"

/-- `KECCAK_CNT` (`layout.rs`): the local column of the first read count. -/
def keccakCnt : ℕ := columnIndexByName keccakColumns "cnt_0"

/-- `QKECCAK_SLOTS = STATE_LANES * (ROUNDS / KECCAK_DEPTH)` (`layout.rs`): the slots of
`q_keccak` the states take. -/
def qkeccakSlots : ℕ := 25 * keccakSegments

/-- `QKECCAK_SPARE`, `2^qkeccakSlotBits - QKECCAK_SLOTS` (`layout.rs`): the slots of
`q_keccak` left over, which carry `KECCAK` columns. -/
def qkeccakSpare : ℕ := 2 ^ qkeccakSlotBits - qkeccakSlots

/-- The local `KECCAK` columns outside the value lanes, `KECCAK_IN ≤ local < KECCAK_CNT`, in
order: the `k`-th is `spare_local(k)` (`layout.rs`). -/
def keccakCommitted : List ℕ :=
  (List.range keccakColumns.length).filter fun l ↦ ¬ (keccakIn ≤ l ∧ l < keccakCnt)

/-- The `q_keccak` slot of a local `KECCAK` column, if it has one (`qkeccak_slot`,
`layout.rs`, past the table's base): input lane `l` (local column `KECCAK_IN + l`) is
slot `l`, and the first `QKECCAK_SPARE` committed columns take the slots from `QKECCAK_SLOTS` on,
in order. The Rust tries the spare slots first; the two parts have disjoint keys
(`keccakSlotOf_disjoint`), so the order in which they are tried does not matter. -/
def keccakSlotOf (l : ℕ) : Option ℕ :=
  if keccakIn ≤ l ∧ l < keccakIn + 25 then some (l - keccakIn)
  else ((keccakCommitted.take qkeccakSpare).idxOf? l).map (qkeccakSlots + ·)

/-- `TOWER_LANES`: each limb of an `E` product, its terms `g^e · va_j · vb_k` as `(j, k, e)`,
folded by `y² = x·y + 1` and `x = g` (`layout.rs`). -/
def towerLanes : List (List (ℕ × ℕ × ℕ)) :=
  [[(0, 0, 0), (1, 1, 0)], [(0, 1, 0), (1, 0, 0), (1, 1, 1)]]

/-- `flushes_arith(opcode, multiply)` (`layout.rs`). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := columnIndexByName arithColumns
  let va := [c "va_0", c "va_1"]
  let vb := [c "vb_0", c "vb_1"]
  let result : List Form :=
    if multiply then
      towerLanes.map fun lane ↦
        Form.sum (lane.map fun (j, k, e) ↦ Form.prod (va.getD j 0) (vb.getD k 0) e)
    else (List.range 2).map fun i ↦ (Form.col (va.getD i 0)).add (Form.col (vb.getD i 0))
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opcode
    [Form.col (c "o_a"), Form.col (c "o_b"), Form.col (c "o_c"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod (c "fp") (c "o_a")) (c "cnt_a") va
  let f := f.memoryCols (Form.prod (c "fp") (c "o_b")) (c "cnt_b") vb
  f.memory (Form.prod (c "fp") (c "o_c")) (c "cnt_c") result

/-- `flushes_set()` (`layout.rs`). -/
def flushesSet : Flushes :=
  let c := columnIndexByName setColumns
  let k := [c "k_0", c "k_1"]
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (Form.col (c "o") :: k.map (Form.col ·) ++ [Form.const 0, Form.const 0])
  f.memoryCols (Form.prod (c "fp") (c "o")) (c "cnt") k

/-- `flushes_deref()` (`layout.rs`). -/
def flushesDeref : Flushes :=
  let c := columnIndexByName derefColumns
  let pc := c "pc"
  let fp := c "fp"
  let fPc := c "f_pc"
  let fFp := c "f_fp"
  let v3 := [c "v3_0", c "v3_1"]
  let gated := fun lane ↦ [Form.col lane, Form.prod fPc lane, Form.prod fFp lane]
  let store : List Form :=
    [Form.sum (gated (v3.getD 0 0) ++ [Form.prod fPc pc 2, Form.prod fFp fp]),
      Form.sum (gated (v3.getD 1 0))]
  let f : Flushes := {}
  let f := f.stateStep pc fp
  let f := f.bytecode pc (c "cnt_bc") opDeref
    [Form.col (c "o1"), Form.col (c "o2"), Form.col (c "o3"), Form.col fPc, Form.col fFp]
  let f := f.memoryCols (Form.prod fp (c "o1")) (c "cnt_ptr") [c "ptr"]
  let f := f.memory (Form.prod (c "ptr") (c "o2")) (c "cnt_target") store
  f.memoryCols (Form.prod fp (c "o3")) (c "cnt_local") v3

/-- `flushes_jump()` (`layout.rs`): `next_pc = b·dest + (b + 1)·g·pc`,
`next_fp = b·frame + (b + 1)·fp`. -/
def flushesJump : Flushes :=
  let c := columnIndexByName jumpColumns
  let pc := c "pc"
  let fp := c "fp"
  let b := c "b"
  let f : Flushes := {}
  let f := f.stateDerived pc fp
    (((Form.prod b (c "v_pc")).add (Form.prod b pc 1)).add (Form.col pc 1))
    (((Form.prod b (c "v_fp")).add (Form.prod b fp)).add (Form.col fp))
  let f := f.bytecode pc (c "cnt_bc") opJump
    [Form.col (c "o_c"), Form.col (c "o_d"), Form.col (c "o_f"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod fp (c "o_c")) (c "cnt_c") [c "v_cond"]
  let f := f.memoryCols (Form.prod fp (c "o_d")) (c "cnt_d") [c "v_pc"]
  f.memoryCols (Form.prod fp (c "o_f")) (c "cnt_f") [c "v_fp"]

/-- `jump_constraints(columns)`: `b + cond·w` and `cond·(b + 1)` (`layout.rs`). -/
def jumpConstraints (columns : List E) : List E :=
  let c := columnIndexByName jumpColumns
  let condition := columns.getD (c "v_cond") 0
  let inverse := columns.getD (c "w") 0
  let flag := columns.getD (c "b") 0
  [flag + condition * inverse, condition * (flag + 1)]

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

/-- `flushes_keccak()` (`layout.rs`): the state step, the bytecode read, then the
thirteen cells read (four addressed ones, the tail run, `b8`, the cap run) and the thirteen
written, each holding its lanes in the layout its flag names (`keccak_cell_lanes`,
`layout.rs`, which is `cellLanes`, `LeanIsa.lean`): a read cell's free limb is the column
`free`, a written one's zero. Output cell `0` is always written, cell `1` when `out_two` is `1`,
and cells `2…12` when `out_all` is `1` (`memoryIf`). -/
def flushesKeccak : Flushes :=
  let c := columnIndexByName keccakColumns
  let oM := ["o_m0", "o_m1", "o_m2", "o_m3"].map c
  let fp := c "fp"
  let f : Flushes := {}
  let f := f.stateStep (c "pc") fp
  let f := f.bytecode (c "pc") (c "cnt_bc") opKeccak
    ((oM ++ ["o_tail", "o_b8", "o_cap", "o_out", "odd_in", "odd_out", "out_two",
      "out_all"].map c).map (Form.col ·))
  let address := fun (cell : ℕ) ↦
    if cell < 4 then Form.prod fp (oM.getD cell 0)
    else if cell < 8 then Form.prod fp (c "o_tail") (cell - 4)
    else if cell = 8 then Form.prod fp (c "o_b8")
    else Form.prod fp (c "o_cap") (cell - 9)
  let sides : List (ℕ × ℕ × Option ℕ) := [(keccakIn, c "odd_in", some (c "free")),
    (keccakOut, c "odd_out", none)]
  sides.zipIdx.foldl (fun f ((lanes, flag, missing), side) ↦
    let lane := fun (l : Option ℕ) ↦ l.map (lanes + ·)
    (List.range 13).foldl (fun f cell ↦
      let values := ([0, 1] : List ℕ).map (fun h ↦
        let pick := fun (p : Option ℕ × Option ℕ) ↦ if h = 0 then p.1 else p.2
        layoutLimb (lane (pick (cellLanes false cell)))
          (lane (pick (cellLanes true cell))) flag missing)
      let count := keccakCnt + 13 * side + cell
      if side = 0 then f.memory (address cell) count values
      else if cell = 0 then f.memory (Form.prod fp (c "o_out")) count values
      else f.memoryIf (if cell = 1 then c "out_two" else c "out_all")
        (Form.prod fp (c "o_out") cell) count values) f) f

/-- One instruction's table: its columns, its bus flushes, its constraints
(`layout.rs`). -/
structure Table where
  /-- Its opcode, also its index in `tables()`. -/
  opcode : ℕ
  /-- Its columns' names, in order. -/
  columns : List String
  /-- Its bus flushes. -/
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-- `Table::width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table::n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table::count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-- `tables()`, in opcode order (`layout.rs`). -/
def tables : List Table :=
  [⟨opXor, arithColumns, flushesArith opXor false, fun _ ↦ []⟩,
    ⟨opMul, arithColumns, flushesArith opMul true, fun _ ↦ []⟩,
    ⟨opSet, setColumns, flushesSet, fun _ ↦ []⟩,
    ⟨opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩,
    ⟨opJump, jumpColumns, flushesJump, jumpConstraints⟩,
    ⟨opKeccak, keccakColumns, flushesKeccak, fun _ ↦ []⟩]

/-- `Table::padding` (`layout.rs`): the row a padding row holds, zero but for
`KECCAK`'s output lanes `KECCAK_OUT …`, a padding row permuting zeros (`keccak_f` of the zero
state). -/
def Table.padding (t : Table) : List E :=
  let output := keccakF1600 (Vector.replicate 25 0)
  (List.range t.width).map fun i ↦
    if t.opcode = opKeccak ∧ keccakOut ≤ i ∧ i < keccakOut + 25 then
      eOfNat (Keccak.lane output (i - keccakOut)).toNat
    else 0

/-- `TABLE_WIDTHS` (`layout.rs`). -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column (`layout.rs`). -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ globalColumnCount + (tableWidths.take t).sum

/-- `TABLE_LOG_FLOORS` (`layout.rs`): each table's least log-height, `0` but for
`KECCAK`, the Keccak reduction's block of steps. -/
def tableLogFloors : List ℕ := [0, 0, 0, 0, 0, keccakMinStepsLog]

/-! ### The bus layout (`layout.rs`, `bus.rs`, `lib.rs`) -/

/-- One block of a bus side, owned by a table (`BusBlock`, `layout.rs`). -/
structure BusBlock where
  /-- The owner's log-height: the block spans `2 ^ logRows` rows. -/
  logRows : ℕ
  /-- The owner's row count: the first `rows` rows flush, the others are padding rows, whose
  leaves are `1`. -/
  rows : ℕ
  /-- The tuple flushed, over the owner's local columns. -/
  coordinates : List Form
  /-- The owner's opcode. -/
  owner : ℕ
  deriving Inhabited

/-- Where a side's blocks sit in the stacked leaf cube: its log-size, the framework blocks'
placements, and the table blocks', in the side's block order (`BusLayout`, `bus.rs`). -/
structure BusLayout where
  /-- The log-size of the stacked leaf cube. -/
  depth : ℕ
  /-- The framework blocks' placements. -/
  framework : List Placement
  /-- The table blocks' placements, in the side's block order. -/
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`bus.rs`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the global column's multilinear extension at `point` (over the column's own
variables) is `value` (`ColumnClaim`, `bus.rs`). -/
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

/-! ### `build_layout` (`layout.rs`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  /-- The memory's log-size, `κ`. -/
  logMemory : ℕ
  /-- The bytecode's log-size, in tuples of `2^BUS_BITS` words. -/
  logBytecode : ℕ
  /-- The bytecode's words. -/
  bytecode : List K
  /-- The push side's blocks. -/
  push : List BusBlock
  /-- The pull side's blocks. -/
  pull : List BusBlock
  /-- The count side's blocks. -/
  count : List BusBlock
  /-- Every global column's placement; `none` for a `KECCAK` output lane. -/
  placements : List (Option Placement)
  /-- The stack's log-size: the committed columns stacked in one cube. -/
  stackLog : ℕ
  /-- The tables' log-heights, each the least `h` with `rows ≤ 2 ^ h`, at least its floor. -/
  tableLogHeights : List ℕ

/-- The placement of a committed column (`layout.placements[column]`), which the verifier reads
of `MEMORY_0` and `QKECCAK`. -/
def Layout.placement (layout : Layout) (column : ℕ) : Placement :=
  (layout.placements.getD column none).getD default

/-- `ColumnClaim::on_stack` (`bus.rs`): the claim as an equality weight on the
stack; `none` for a column nothing commits (a `KECCAK` output lane), whose claim never reaches
the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : Option StackClaim :=
  (layout.placements.getD c.column none).map fun placement ↦
    (fun x ↦ eqEval (placement.stackPoint c.point layout.stackLog) x, c.value)

/-- The bus blocks of every table, side by side: pushes, pulls, counts, each block at its
table's log-height and row count (`layout.rs`). -/
def busBlocks (tableLogHeights tableRows : List ℕ) :
    List BusBlock × List BusBlock × List BusBlock :=
  let rows := List.zip tables (List.zip tableLogHeights tableRows)
  (rows.flatMap fun (t, h, n) ↦ t.flushes.push.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.flushes.pull.map fun c ↦ ⟨h, n, c, t.opcode⟩,
    rows.flatMap fun (t, h, n) ↦ t.countColumns.map fun l ↦ ⟨h, n, [Form.col l], t.opcode⟩)

/-- The `q_keccak` slot of a global column (`qkeccak_slot`, `layout.rs`): a `KECCAK`
input lane's, or a spare slot's column's; `none` for every other column, those of the other tables
(below the `KECCAK` base, where `checked_sub` fails) among them. -/
def keccakSlot (column : ℕ) : Option ℕ :=
  if globalColumnBases.getD opKeccak 0 ≤ column then
    keccakSlotOf (column - globalColumnBases.getD opKeccak 0)
  else none

/-- The global columns of the `KECCAK` output lanes, in lane order (`outputs`,
`layout.rs`; the columns of `values[KECCAK_OUT..KECCAK_OUT + STATE_LANES]`,
`lib.rs`). -/
def keccakOutputColumns : List ℕ :=
  (List.range 25).map (globalColumnBases.getD opKeccak 0 + keccakOut + ·)

/-- Every column's log-size, in global order: the framework's, `q_keccak`'s, then each table's
block (`column_kappas`, `layout.rs`). -/
def columnKappas (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  let qkeccakKappa := tableLogHeights.getD opKeccak 0 + qkeccakSlotBits
  [logMemory, logMemory, logMemory, logBytecode, qkeccakKappa] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- The placements of every column, and the stack's log-size (`layout.rs`): the
committed columns (every column but those with a `q_keccak` slot, the `KECCAK` input lanes and
the table's first fourteen committed columns, and the `KECCAK` output lanes: `101` of `165`)
stacked by `stack_offsets`, a column with a slot at `q_keccak`'s offset plus its slot's `2^κ`
words, an output lane nowhere. -/
def placementsOf (kappas : List ℕ) : List (Option Placement) × ℕ :=
  let blockCols := (List.range kappas.length).filter fun c ↦
    (keccakSlot c).isNone ∧ c ∉ keccakOutputColumns
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsetOf := fun c ↦ blockOffsets.getD (blockCols.idxOf c) 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match keccakSlot column with
    | some slot =>
      some ({ variableCount := kappa, index := offsetOf qkeccak + slot * 2 ^ kappa } : Placement)
    | none =>
      if column ∈ keccakOutputColumns then none
      else some { variableCount := kappa, index := offsetOf column }
  (placements, max Whir.minLogStack totalLog)

/-- `build_layout(bytecode, log_memory, table_rows)` (`layout.rs`); `none` exactly where
the Rust returns an error: a bytecode whose length is not a power of two (`log2_strict`) or whose
log-length is outside `BUS_BITS ..= 30 + BUS_BITS`, and sizes outside the window. It is also `none`
on row counts not one per table, which the verifier never passes (it reads `N_TABLES` of them). A
table's log-height is the least `h` with `rows ≤ 2^h` (`log2Ceil`), and at least its floor
(`tableLogFloors`). -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableRows : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 1 ≤ logMemory ∧ logMemory ≤ 30 ∧
        tableRows.all (· ≤ 2 ^ 30) ∧ logLength - busBits ≤ 30 ∧
        tableRows.length = tables.length then
      let logBytecode := logLength - busBits
      let tableLogHeights := List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
        tableLogFloors
      let (push, pull, count) := busBlocks tableLogHeights tableRows
      let (placements, stackLog) :=
        placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog,
        tableLogHeights⟩
    else none

end LeanVM.Protocol.Verifier

end
