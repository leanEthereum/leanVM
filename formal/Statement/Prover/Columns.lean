module

public import Statement.Prover.Witness

/-!
# The columns and the stack of an execution, executable

From the rows of a run (`rowsOf`, `Witness.lean`) and the verifier's layout of its sizes
(`buildLayout`): every column of the instance as an array, by the verifier's global column number
(`colsOf`), the `KECCAK` states computed once per row for `QKECCAK` and the output lanes; and the
stack, each column written at its placement.
`witness?` puts them together.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## Columns -/

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellAt (R : Array (Array K)) (x i : ℕ) : K := ((R[x]?).bind (·[i]?)).getD 0

/-- Column `i` of a table at the height `2^h`: its rows' cells, zero past them. -/
def tableColumn (R : Array (Array K)) (h i : ℕ) : Array K :=
  Array.ofFn (n := 2 ^ h) fun x ↦ cellAt R x.val i

/-- Rounds `12m` to `12m + 11` of Keccak-f[1600]. -/
def segment (m : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop (12 * m)).take 12).foldl Keccak.round a

/-- The zero state. -/
def zeroState : KeccakState := Vector.replicate 25 0

/-- The input state of row `x` of the `KECCAK` table: its cells `15 … 39`. -/
def inState (R : Array (Array K)) (x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ (cellAt R x (15 + l.val)).lane

/-- The state after twelve rounds of every step of the `KECCAK` table at the height `2^h`, once
per row; a padding row's is that of the zero state, computed once. -/
def midStates (R : Array (Array K)) (h : ℕ) : Array KeccakState :=
  let zMid := segment 0 zeroState
  Array.ofFn (n := 2 ^ h) fun x ↦ if x.val < R.size then segment 0 (inState R x.val) else zMid

/-- The state after twenty-four rounds of every step, from its state after twelve. -/
def outStates (R : Array (Array K)) (mids : Array KeccakState) : Array KeccakState :=
  let zOut := segment 1 (segment 0 zeroState)
  Array.ofFn (n := mids.size) fun x ↦ if x.val < R.size then segment 1 mids[x] else zOut

/-- `QKECCAK` of the `KECCAK` table at the height `2^h`: slot `l < 25` of step `x` is input lane
`l` of row `x`, slot `25 + l` lane `l` of its state after twelve rounds, slot `50 + k` its cell of
the column `k`, `pc` through `out_all` (`spare_local` and `qkeccak_slot`,
`crates/verifier/src/layout.rs`). -/
def qkeccakColumn (R : Array (Array K)) (h : ℕ) (mids : Array KeccakState) : Array K :=
  let p := 2 ^ h
  Array.ofFn (n := 2 ^ (h + 6)) fun i ↦
    let x := i.val % p
    let k := i.val / p
    if k < 25 then cellAt R x (15 + k)
    else if k < 50 then laneK (mids.getD x zeroState) (k - 25)
    else cellAt R x (k - 50)

/-- The opcode table of a global column from `5` on (by `GLOBAL_COLUMN_BASES`). -/
def tableIndexOf (c : ℕ) : ℕ :=
  if c < 18 then 0 else if c < 31 then 1 else if c < 38 then 2 else if c < 52 then 3
  else if c < 66 then 4 else 5

/-- The column of global number `c`: the memory's two limbs and finalize counts `0 … 2`, `BFCNT`
`3`, `QKECCAK` `4`, then column `c - base` of the opcode table `c` falls in, the `KECCAK` output lanes
(its columns `40 … 64`) derived from the twelve-round states `mids`, through the twenty-four-round
states `outs`. -/
def columnAt {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ)
    (mids outs : Array KeccakState) (c : ℕ) : Array K :=
  if c = 0 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 0
  else if c = 1 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 1
  else if c = 2 then acc.mem
  else if c = 3 then acc.bc
  else if c = 4 then qkeccakColumn (acc.tabs.getD 5 #[]) (logs.getD 5 0) mids
  else
    let j := tableIndexOf c
    let i := c - globalColumnBases.getD j 0
    if j = 5 ∧ 40 ≤ i ∧ i < 65 then
      Array.ofFn (n := 2 ^ logs.getD 5 0) fun x ↦ laneK (outs.getD x.val zeroState) (i - 40)
    else tableColumn (acc.tabs.getD j #[]) (logs.getD j 0) i

/-- **Every column of the instance**, by its global column number (`158` of them); the
`KECCAK` states computed once per row, for `QKECCAK` and the output lanes. -/
def colsOf {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (logs : List ℕ) : Array (Array K) :=
  let mids := midStates (acc.tabs.getD 5 #[]) (logs.getD 5 0)
  let outs := outStates (acc.tabs.getD 5 #[]) mids
  Array.ofFn (n := 158) fun c ↦ columnAt img acc logs mids outs c.val

/-! ## The stack -/

/-- **The stack**: every placed column written from its placement's index on, over `2 ^ stackLog`
zeros (`Placement.stack_point`'s cells); a column with a `q_keccak` slot writes again cells of
`QKECCAK`. -/
def stackArray (layout : Layout) (cols : Array (Array K)) : Array K :=
  (layout.placements.zip cols.toList).foldl (init := Array.replicate (2 ^ layout.stackLog) 0)
    fun stack (placement?, col) ↦ match placement? with
      | some placement =>
        Nat.fold col.size (fun i _ stack ↦ stack.set! (placement.index + i) col[i]) stack
      | none => stack

/-! ## The witness -/

/-- The prover's data of an execution: the announced row counts, the verifier's layout, every
column by global number, and the stack. -/
structure Witness where
  /-- The six opcode tables' row counts, in the ensemble's order. -/
  rows : List ℕ
  /-- The verifier's layout of the announced sizes. -/
  layout : Layout
  /-- Every column, by global column number. -/
  cols : Array (Array K)
  /-- The stack, `2 ^ layout.stackLog` cells. -/
  stack : Array K

/-- The prover's data of the rows `acc` of a run on the memory `img`, at the layout `layout`. -/
def buildWitness {κ : ℕ} (img : MemoryImage κ) (acc : Rows) (layout : Layout) : Witness :=
  let cols := colsOf img acc layout.tableLogHeights
  ⟨acc.tabs.toList.map (·.size), layout, cols, stackArray layout cols⟩

/-- **The prover's data of an execution**: `none` unless the trace has the public boundary of
`input`, its run ends in the final state, its committed size is at most `2^30`, and its sizes pass
`build_layout`. -/
def witness? (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) : Option Witness :=
  if boundaryOK input t then
    let memIdx := powIndex t.logMemorySize
    match runSteps memIdx (powIndex prog.logSize) prog t with
    | some steps =>
      if committedSizeOf prog.logSize t.logMemorySize (opCount steps) ≤ maxCommitted then
        let acc := rowsOf memIdx t.memory prog.logSize steps
        (buildLayout (bytecodeWords prog) t.logMemorySize (acc.tabs.toList.map (·.size))).map
          (buildWitness t.memory acc)
      else none
    | none => none
  else none

/-- The eight scalars announcing the sizes and the rate `ρ` (`announce`): the memory log-size,
the six row counts, the rate, each the word `n` in limb `0` (`eOfNat`). -/
def Witness.announce (W : Witness) (ρ : ℕ) : List E :=
  (W.layout.logMemory :: W.rows ++ [ρ]).map eOfNat

end LeanVM.Prover

end
