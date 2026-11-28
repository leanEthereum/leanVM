module

public import Statement.Verifier.Lib

/-!
# The witness of an execution, executable

The run of a trace through the address indices (`powIndex`, `gLogIn`: a word's index looked up in a
hash map), recording each state stepped from, its bytecode slot and the instruction fetched there
(`runSteps`); then the six instruction tables' rows in one pass over the steps (`rowsOf`), as the
Rust's `Table::fill` writes them (`crates/lean_vm_core/src/tables.rs`): each row's `pc` and `fp` as
`K` words, the words it commits, and its pointers as one-hot words (`Chunks.encode`): the cycle
pointer names the step, the bytecode pointer the instruction, and a memory pointer its cell (a block's
pointer its first cell). The address indices and the public boundary are the knowledge extractor's
too (`lean_vm`, `LeanVM/Protocol/Extraction/Fast/Address.lean`).
-/

@[expose] public section

namespace LeanVM.Extraction

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

/-! ## The address indices and the public boundary -/

/-- Insert `g^i ↦ i` into `m`, keyed by the lane of `g^i`, for the `n` indices `i` from `i₀`,
where `x = g^i₀`: one multiplication and one insertion per index. -/
def powIndexFrom : ℕ → ℕ → K → Std.HashMap UInt64 ℕ → Std.HashMap UInt64 ℕ
  | 0, _, _, m => m
  | n + 1, i, x, m => powIndexFrom n (i + 1) (x * g) (m.insert x.lane i)

/-- **The index of the address space of `2^κ` words**: the lane of `g^i` ↦ `i`, for `i < 2^κ`. -/
def powIndex (κ : ℕ) : Std.HashMap UInt64 ℕ := powIndexFrom (2 ^ κ) 0 1 ∅

/-- The index of address `a` among `2^κ` words, looked up in `idx`: `some i` when `idx` maps the
lane of `a` to `i < 2^κ` (`addressIndex?`, computed). -/
def gLogIn (idx : Std.HashMap UInt64 ℕ) (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  match idx[a.lane]? with
  | some i => if h : i < 2 ^ κ then some ⟨i, h⟩ else none
  | none => none

/-- **The public boundary** (`HoldsPublicInput`), decided: the memory has between `2^minLogMem`
and `2^maxLogMem` words, and words `0` and `1` (at the addresses `g^0`, `g^1`) hold the public input. -/
def boundaryOK {prog : LeanIsaProgram} (input : PublicInput) (t : Execution prog) : Bool :=
  if h : minLogMem ≤ t.logMemorySize ∧ t.logMemorySize ≤ maxLogMem then
    decide (t.memory ⟨0, Nat.two_pow_pos t.logMemorySize⟩ = input.word0) &&
      decide (t.memory ⟨1, Nat.one_lt_two_pow (by unfold minLogMem at h; omega)⟩ = input.word1)
  else false

end LeanVM.Extraction

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

/-! ## One-hot pointer words (`crates/lean_vm_core/src/link/pointer.rs`) -/

/-- `Chunks::digit(sigma, i)`: chunk `i`'s value in the index `σ`. -/
def Chunks.digit (chunks : Chunks) (sigma i : ℕ) : ℕ :=
  (sigma >>> chunks.indexShifts.getD i 0) % 2 ^ chunks.widths.getD i 0

/-- `Chunks::encode(sigma)`: the one-hot word of the index `σ`, chunk `i`'s value `v` the bit
`word_shifts[i] + v`. -/
def Chunks.encode (chunks : Chunks) (sigma : ℕ) : ℕ :=
  ((List.range chunks.d).map fun i ↦ 2 ^ (chunks.wordShifts.getD i 0 + chunks.digit sigma i)).sum

/-- `Chunks::bits(word, i)`: chunk `i`'s indicator bits of a word, at bit `0`. -/
def Chunks.bits (chunks : Chunks) (word : ℕ) (i : ℕ) : ℕ :=
  (word >>> chunks.wordShifts.getD i 0) % 2 ^ 2 ^ chunks.widths.getD i 0

/-- `Chunks::indices(word, f)`: every index of a word, one per choice of a set bit in each chunk, the
lowest chunk's choice varying slowest (the Rust's walk); none when a chunk has no bit set. -/
def Chunks.indices (chunks : Chunks) (word : ℕ) : List ℕ :=
  (List.range chunks.d).foldl (fun sigmas i ↦
    let bits := chunks.bits word i
    sigmas.flatMap fun sigma ↦ ((List.range (2 ^ chunks.widths.getD i 0)).filter
      fun v ↦ (bits >>> v) % 2 = 1).map fun v ↦ sigma + v <<< chunks.indexShifts.getD i 0) [0]

/-- `Chunks::shifted(sigma, s)`: the index `s` cells past `σ`, `none` past its window. -/
def Chunks.shifted (chunks : Chunks) (sigma s : ℕ) : Option ℕ :=
  if sigma % 2 ^ chunks.widths.getD 0 0 + s < 2 ^ chunks.widths.getD 0 0 then some (sigma + s)
  else none

end LeanVM.Protocol.Verifier

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## The run -/

/-- One step of a run: the state stepped from, the bytecode slot of its counter, and the
instruction fetched there. -/
structure Step where
  /-- The program counter stepped from. -/
  pc : K
  /-- The frame pointer stepped from. -/
  fp : K
  /-- The bytecode slot of `pc`: `pc = g^slot`. -/
  slot : ℕ
  /-- The instruction fetched at `pc`. -/
  ins : LeanIsaInstruction

/-- The memory reader through the index `memIdx` (`MemoryImage.read`, computed). -/
def readIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (a : K) : Option E :=
  (gLogIn memIdx κ a).map img

/-- `n` steps from `r` (`run`, computed through the indices, the instruction of slot `i` read
from `code`, `prog.code` tabulated), the steps taken pushed on `acc`: the steps and the state
reached; `none` if a step fails or the machine halts first. -/
def stepsFrom (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram)
    (code : Vector LeanIsaInstruction (2 ^ prog.logSize)) {κ : ℕ} (img : MemoryImage κ) :
    ℕ → Registers K → Array Step → Option (Array Step × Registers K)
  | 0, r, acc => some (acc, r)
  | n + 1, r, acc =>
    if r = Registers.final prog then none
    else
      match gLogIn codeIdx prog.logSize r.pc with
      | none => none
      | some i =>
        match executeWith (readIn memIdx img) r code[i] with
        | none => none
        | some r' =>
          stepsFrom memIdx codeIdx prog code img n r' (acc.push ⟨r.pc, r.fp, i.val, code[i]⟩)

/-- **The run of a trace**: its `t.steps` steps from the initial state, when they end in the
final state; `none` otherwise. The program's instructions are tabulated once. -/
def runSteps (memIdx codeIdx : Std.HashMap UInt64 ℕ) (prog : LeanIsaProgram) (t : Execution prog) :
    Option (Array Step) :=
  match stepsFrom memIdx codeIdx prog (Vector.ofFn prog.instructions) t.memory t.stepCount
      Registers.initial
    #[] with
  | some (acc, r) => if r = Registers.final prog then some acc else none
  | none => none

/-- The table of an opcode, in the tables' order (`OP_XOR` … `OP_KECCAK`, `layout.rs`). -/
def opTableIdx : Opcode → ℕ
  | .xor => opXor
  | .mulNative => opMul
  | .setConstant => opSet
  | .deref => opDeref
  | .jump => opJump
  | .keccak => opKeccak

/-- The rows of each table a run executes (`Trace::row_counts`). -/
def rowCounts (steps : Array Step) : List ℕ :=
  (List.range nTables).map fun t ↦ steps.countP fun st ↦ decide (opTableIdx st.ins.opcode = t)

/-! ## The rows (`Table::fill`, `crates/lean_vm_core/src/tables.rs`) -/

/-- The limbs of the word at `a`, zero when there is none (`MemoryImage.limbsAt`, computed). -/
def limbsIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (a : K) : Vector K 2 :=
  match readIn memIdx img a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-- The cells a `KECCAK` with these operands reads at `fp`, the zero word where a read fails
(`keccakInputCells`, computed). -/
def keccakInputIn (memIdx : Std.HashMap UInt64 ℕ) {κ : ℕ} (img : MemoryImage κ) (fp : K)
    (om : Fin 4 → K) (otail ob8 ocap : K) (c : Fin 13) : E :=
  (readIn memIdx img (fp * keccakInputCellOffset om otail ob8 ocap c)).getD 0

/-- The lane `l` of a state, as a `K` word. -/
def laneK (S : KeccakState) (l : ℕ) : K := K.ofLane (Keccak.lane S l)

/-- What a table's fill reads: the memory index and image, and the pointers' chunks. -/
structure FillCtx (κ : ℕ) where
  /-- The memory's address index. -/
  memIdx : Std.HashMap UInt64 ℕ
  /-- The memory image. -/
  img : MemoryImage κ
  /-- The pointers' chunks. -/
  chunks : Chunks

/-- `FillCtx::ptr(sigma)`: the one-hot word of the index `σ`. -/
def FillCtx.ptr {κ : ℕ} (ctx : FillCtx κ) (sigma : ℕ) : K := K.ofBits (ctx.chunks.encode sigma)

/-- The one-hot word of the cell at address `a` (`ctx.ptr(fp + o)`): its index's, `0` for an
address outside the memory, which no valid run reads. -/
def FillCtx.cell {κ : ℕ} (ctx : FillCtx κ) (a : K) : K :=
  ctx.ptr ((gLogIn ctx.memIdx κ a).map (·.val) |>.getD 0)

/-- The two `K` lanes of the word at `a`. -/
def FillCtx.limbs {κ : ℕ} (ctx : FillCtx κ) (a : K) : Vector K 2 := limbsIn ctx.memIdx ctx.img a

/-- **The row of step `cycle`**, of its instruction's table, the columns in the verifier's order
(`xorColumns` … `keccakColumns`, `layout.rs`), as `Table::fill` writes it: `pc` and `fp` as words,
the words a row commits, and its pointers, the cells' (`fp·o`), the instruction's (`ix_bc`, the
slot) and the cycle's (`ix_cycle`, the step). `DEREF`'s target is the cell `ptr·o2`; `JUMP`'s
successor is the jump's when `v_cond ≠ 0`, `(g·pc, fp)` otherwise, with `w = v_cond⁻¹`, zero when
`v_cond` is, and `b = [v_cond ≠ 0]`; `KECCAK`'s input lanes are the state its thirteen cells hold
in its input layout, its output lanes their permutation, and each operand's pointer names its
first cell. -/
def rowOf {κ : ℕ} (ctx : FillCtx κ) (cycle : ℕ) (st : Step) : Array K :=
  let (pc, fp) := (st.pc, st.fp)
  let (bc, cyc) := (ctx.ptr st.slot, ctx.ptr cycle)
  match st.ins with
  | .xor oA oB oC => #[pc, fp, ctx.cell (fp * oA), ctx.cell (fp * oB), ctx.cell (fp * oC), bc, cyc]
  | .mulNative oA oB oC =>
    let a := ctx.limbs (fp * oA)
    #[pc, fp, a[0], a[1], ctx.cell (fp * oA), ctx.cell (fp * oB), ctx.cell (fp * oC), bc, cyc]
  | .setConstant o _ => #[pc, fp, ctx.cell (fp * o), bc, cyc]
  | .deref o1 o2 o3 mode =>
    let ptr := (ctx.limbs (fp * o1))[0]
    let s : K := match mode with | .cell => 0 | _ => 1
    #[pc, fp, ptr, o2, s, ctx.cell (fp * o1), ctx.cell (ptr * o2), ctx.cell (fp * o3), bc, cyc]
  | .jump oc od of =>
    let (cond, dest, frame) := ((ctx.limbs (fp * oc))[0], (ctx.limbs (fp * od))[0],
      (ctx.limbs (fp * of))[0])
    let taken := cond ≠ 0
    let (pcNext, fpNext) := if taken then (dest, frame) else (pc * g, fp)
    #[pc, fp, cond, dest, frame, pcNext, fpNext, if taken then cond⁻¹ else 0,
      if taken then 1 else 0, ctx.cell (fp * oc), ctx.cell (fp * od), ctx.cell (fp * of), bc, cyc]
  | .keccak om otail ob8 ocap oout inOdd outOdd outCells =>
    let input := keccakInputIn ctx.memIdx ctx.img fp om otail ob8 ocap
    let S := stateOfCells input inOdd
    let out := keccakF1600 S
    let offsets := [om 0, om 1, om 2, om 3, otail, ob8, ocap, oout]
    #[pc, fp, oout, layoutFlagWord inOdd, layoutFlagWord outOdd, (keccakOutputFlags outCells).1,
        (keccakOutputFlags outCells).2, if inOdd then (input 0).limb 0 else (input 8).limb 1] ++
      Array.ofFn (fun l : Fin 25 ↦ laneK S l) ++ Array.ofFn (fun l : Fin 25 ↦ laneK out l) ++
      (offsets.map fun o ↦ ctx.cell (fp * o)).toArray ++ #[bc, cyc]

/-- **The rows of a run**: each table's executed rows, in the order its steps ran (the Rust's
trace, `crates/lean_vm_core/src/cpu/trace.rs`), the tables in opcode order. -/
def rowsOf {κ : ℕ} (ctx : FillCtx κ) (steps : Array Step) : Array (Array (Array K)) :=
  (steps.zipIdx.foldl (fun tabs (st, cycle) ↦
    tabs.modify (opTableIdx st.ins.opcode) (·.push (rowOf ctx cycle st)))
    (Array.replicate nTables #[]))

end LeanVM.Prover

end
