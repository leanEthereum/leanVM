module

public import Statement.Prover.Witness

/-!
# The columns and the stack of an execution, executable

From the rows of a run (`rowsOf`, `Witness.lean`) and the verifier's layout of its sizes
(`buildLayout`): every column of the instance as an array, by the verifier's global column number
(`colsOf`): the memory's two limbs, `q_keccak`, then each table's columns at its height, a padding
row past its executed rows (`Table.padding`); and the stack, each column with a block of its own
written whole at its placement (`stackOffsets`), as `build` writes it
(`crates/lean_vm_core/src/cpu/layout.rs`). `q_keccak` holds, a slot of `2^τ` words per lane, every `KECCAK` step's input state and its state after twelve rounds, the
padding steps' those of the zero state (`commit_states`, `crates/keccak_gkr/src/witness.rs`), then
in its spare slots the `KECCAK` table's columns that ride there (`spareLocal`). `witness?` puts
them together.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Verifier

/-! ## Columns -/

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellAt (R : Array (Array K)) (x i : ℕ) : K := ((R[x]?).bind (·[i]?)).getD 0

/-- The padding row of table `t` as `K` words (every padding value is `K`-valued). -/
def paddingRow (t : ℕ) : Array K := ((tables.getD t default).padding.map (·.limb 0)).toArray

/-- Column `i` of a table at the height `2^h`: its rows' cells, the padding row's past them. -/
def tableColumn (R : Array (Array K)) (pad : Array K) (h i : ℕ) : Array K :=
  Array.ofFn (n := 2 ^ h) fun x ↦ if x.val < R.size then cellAt R x.val i else pad.getD i 0

/-- Rounds `12m` to `12m + 11` of Keccak-f[1600]. -/
def segment (m : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop (12 * m)).take 12).foldl Keccak.round a

/-- The zero state. -/
def zeroState : KeccakState := Vector.replicate 25 0

/-- The input state of row `x` of the `KECCAK` table: its input lanes, columns `KECCAK_IN …`. -/
def inState (R : Array (Array K)) (x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ (cellAt R x (keccakIn + l.val)).lane

/-- **`q_keccak`** of the `KECCAK` table's rows `R` at the height `2^h`, slot by slot, `2^h` words a
slot: slot `l < 25` is input lane `l` of every step, slot `25 + l` lane `l` of its state after
twelve rounds (a padding step's those of the zero state, computed once), slot `50 + k` the column
`spareLocal k` (`qkeccak_slot`, `layout.rs`; `build`, `crates/lean_vm_core/src/cpu/layout.rs`). -/
def qkeccakColumn (R : Array (Array K)) (h : ℕ) : Array K :=
  let p := 2 ^ h
  let pad := paddingRow opKeccak
  let zMid := segment 0 zeroState
  let mids : Array KeccakState :=
    Array.ofFn (n := p) fun x ↦ if x.val < R.size then segment 0 (inState R x.val) else zMid
  Array.ofFn (n := 2 ^ (h + qkeccakSlotBits)) fun i ↦
    let x := i.val % p
    let k := i.val / p
    if k < keccakStateLanes then (if x < R.size then cellAt R x (keccakIn + k) else 0)
    else if k < qkeccakSlots then laneK (mids.getD x zMid) (k - keccakStateLanes)
    else if x < R.size then cellAt R x (spareLocal (k - qkeccakSlots))
    else pad.getD (spareLocal (k - qkeccakSlots)) 0

/-- The table a global column from `NUM_GLOBAL_COLUMNS` on belongs to (`GLOBAL_COLUMN_BASES`). -/
def tableOf (c : ℕ) : ℕ :=
  ((List.range nTables).reverse.find? fun t ↦ globalColumnBases.getD t 0 ≤ c).getD 0

/-- The number of global columns (`N_COLUMNS`, `crates/lean_vm_core/src/cpu/layout.rs`). -/
def nColumns : ℕ := numGlobalColumns + tableWidths.sum

/-- **Every column of the instance**, by its global column number: the memory's two limbs
(`MEMORY_0`, `MEMORY_1`), `q_keccak`, then each table's columns at its log-height `logs[t]`. A
column `q_keccak` carries is also a column of its table here, as the Rust's views of it read the
same words. -/
def colsOf {κ : ℕ} (img : MemoryImage κ) (tabs : Array (Array (Array K))) (logs : List ℕ) :
    Array (Array K) :=
  let pads := Array.ofFn (n := nTables) fun t ↦ paddingRow t
  Array.ofFn (n := nColumns) fun c ↦
    if c.val = memory0 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 0
    else if c.val = memory1 then Array.ofFn (n := 2 ^ κ) fun x ↦ (img x).limb 1
    else if c.val = qkeccak then qkeccakColumn (tabs.getD opKeccak #[]) (logs.getD opKeccak 0)
    else
      let t := tableOf c.val
      tableColumn (tabs.getD t #[]) (pads.getD t #[]) (logs.getD t 0)
        (c.val - globalColumnBases.getD t 0)

/-! ## The stack -/

/-- **The stack**: every column with a block of its own (`stackBlocks`: not one `q_keccak` carries,
not a `KECCAK` output lane) written at its placement over `2 ^ stackLog` zeros, row `i` at
`index + i` (`split_stack`). -/
def stackArray (layout : Layout) (cols : Array (Array K)) : Array K :=
  (layout.placements.zip cols.toList).zipIdx.foldl (init := Array.replicate (2 ^ layout.stackLog) 0)
    fun stack ((placement?, col), c) ↦ match placement?, qkeccakSlot c with
      | some placement, none =>
        Nat.fold col.size (fun i _ stack ↦ stack.set! (placement.index + i) col[i]) stack
      | _, _ => stack

/-! ## The witness -/

/-- The prover's data of an execution: the announced row counts, the verifier's layout, the
pointers' chunks, every column by global number, and the stack. -/
structure Witness where
  /-- The six tables' row counts, in opcode order. -/
  rows : List ℕ
  /-- The verifier's layout of the announced sizes. -/
  layout : Layout
  /-- The pointers' chunks (`Chunks::new(pointer_width)`). -/
  chunks : Chunks
  /-- Every column, by global column number. -/
  cols : Array (Array K)
  /-- The stack, `2 ^ layout.stackLog` cells. -/
  stack : Array K

/-- **The prover's data of an execution**: `none` unless the trace has the public boundary of
`input` and its run ends in the final state, its sizes pass `build_layout` with a stack of at most
`2^MAX_STACKED_LOG` words (`Execution.committedSize ≤ 2^30`, `Statement/LeanVm.lean`), and its
pointers fit one word (`Chunks.new`): exactly the sizes the verifier accepts, as `prove` refuses the
others (`WitnessOutOfRange`, `PointerWidth`, `crates/lean_vm_core/src/cpu/mod.rs`). -/
def witness? (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) : Option Witness :=
  if boundaryOK input t then
    let memIdx := powIndex t.logMemorySize
    match runSteps memIdx (powIndex prog.logSize) prog t with
    | some steps =>
      let rows := rowCounts steps
      match buildLayout (bytecodeWords prog) t.logMemorySize rows with
      | some layout =>
        if layout.stackLog ≤ Whir.maxLogStack then
          match Chunks.new (pointerWidth t.logMemorySize prog.logSize rows.sum) with
          | some chunks =>
            let tabs := rowsOf ⟨memIdx, t.memory, chunks⟩ steps
            let cols := colsOf t.memory tabs layout.tableLogHeights
            some ⟨rows, layout, chunks, cols, stackArray layout cols⟩
          | none => none
        else none
      | none => none
    | none => none
  else none

/-- The eight scalars announcing the sizes and the rate `ρ` (`announce_public`,
`crates/lean_vm_core/src/cpu/mod.rs`): the memory log-size, the six row counts, the rate, each the
word `n` in limb `0` (`eOfNat`). -/
def Witness.announce (W : Witness) (ρ : ℕ) : List E :=
  (W.layout.logMemory :: W.rows ++ [ρ]).map eOfNat

/-- The local columns of table `t`, from the global ones. -/
def Witness.tableCols (W : Witness) (t : ℕ) : Array (Array K) :=
  W.cols.extract (globalColumnBases.getD t 0)
    (globalColumnBases.getD t 0 + tableWidths.getD t 0)

end LeanVM.Prover

end
