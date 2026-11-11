/-
  LeanVM.Protocol.LeanIsa

  The leanISA instance of the M3 model, and the two maps of the adaptor: the committed stack of
  a constraint-system witness, and the witness read back off any stack.
-/

module

public import LeanVM.Protocol.ToClean.ComponentPolynomial
public import LeanVM.Arithmetization.Statement
public import LeanVM.Protocol.Bus
public import LeanVM.Protocol.FixedColumns
public import LeanVM.Protocol.Stack

/-!
# The leanISA instance

The proof system is stated over an abstract `M3Instance`; this module builds the one leanVM
proves, from leanISA's constraint system (`leanIsaEnsemble prog`, Clean), the public program
`prog` and the announced sizes `s`. It is the only place where the proof system meets leanISA,
and it is data: what the adaptor's theorems say of it is in `LeanIsa/Sound.lean` and
`LeanIsa/Complete.lean`.

**Sizes.** `Sizes` is what the prover announces: the memory log-size and the six opcode tables'
row counts (`crates/verifier/src/lib.rs`); the bytecode's log-size is the program's. A table's
log-height is `max(log2_ceil(rows), floor)`, the floor `0` but for `KECCAK`'s `9`
(`TABLE_LOG_FLOORS`, `crates/verifier/src/layout.rs:489-490`; `KECCAK_MIN_STEPS_LOG`).
`Sizes.Admissible prog s` is the part of the verifier's checks on sizes (`build_layout`,
`crates/verifier/src/layout.rs:497-503`, and `lib.rs:228-231`): the memory window `[16, 32]`, the
row cap `2^32`, and the stacked size `leanIsaμ prog s ≤ 28` (`crates/leanvm_core/src/pcs.rs:49-51`;
its floor `15` holds by construction). `validRate` is the WHIR rate check, read off the same
announcement and used by the commitment, not by the instance.

**The tables.** Nine, in the order of the Rust's global columns
(`crates/leanvm_core/src/cpu/layout.rs:14-28`): the memory columns `MEMORY_0, MEMORY_1, MFCNT`
at height `2^logMem`; the bytecode finalize count `BFCNT` at `2^prog.logSize`; the Keccak
reduction's column `QKECCAK` at `2^(τ_KECCAK + 6)` (`layout.rs:223`, `SLOT_LOG = 6`); then the six
opcode tables at their log-heights, each `Component.toM3` of its Clean component with leanISA's
separators, directions and counted channels (`channelSep`, `channelDir`, the memory and bytecode
pulls). The first three are column groups: no constraint, flush or count, so the table sumcheck
never visits them.

**The bus.** The opcode tables' flushes, and six boundary blocks equal to the interactions of
leanISA's three remaining components: the verifier's state push `(1, 1)` and pull
`(g^(N - 1), 1)` (`leanIsaVerifier`), the memory block's seed push `(g^i, 1, m_i)` and finalize
pull `(g^i, MFCNT_i, m_i)` (`memTable`), and the bytecode block's seed push and finalize pull of
the program's entries (`bytecodeTable`, with the program's thirteen entry columns known to both
parties, `Coord.known`; `bytecode_columns`, `layout.rs:295`). The index column is the verifier's
(`idxColumn`), as the Rust's `Coord::Index` is.

**The stack** (`crates/leanvm_core/src/witness.rs:56-95`). Every committed column has a
log-size, its table's; the `KECCAK` table's columns `0 … 64` but `14` have none (`IsVirtual`: the
fifty value lanes and the fourteen columns riding `QKECCAK`'s spare slots; `Placement::VIRTUAL`,
`witness.rs:20`; `layout.rs:228-240`), so `94` of the `158` columns are committed. The committed
columns, in global order, are sorted by log-size, largest first, ties in global order
(`stack_offsets`), and laid end to end at aligned offsets (`Blocks.layout`); the stack has
`μ = max(⌈log₂ total⌉, 15)` variables (`placements_of`). Input lane `l` of the `KECCAK` table is
read at slot `l` of `QKECCAK`, and its columns `0 … 13` at slots `50 … 63` (`qSlot`,
`Blocks.sliceLayout`; `qkeccak_slot`, `crates/verifier/src/layout.rs:422-432, 559-563`): cell `x`
of the column at slot `k` is cell `x + k · 2^τ_KECCAK` of the region. The output lanes are *derived*
(`derived`): lane `l` at row `x` is lane `l` of the
last twelve rounds of Keccak-f[1600] (`keccakSegment 1`) of the state after twelve rounds that
`QKECCAK` commits for step `x` (slots `25 … 49`, `midState`), so a stack carries no output lane, as
the Rust commits none. This is what the Keccak reduction proves of the claims on them: its first
claim checks the output against the second segment of the committed middle state and the middle
state against the first segment of the input, at the point the table sumcheck drew. With the
Keccak predicate of `M3Holds` (every step's middle state is the first segment of its input), an
output lane is the lane of Keccak-f[1600] of the row's input lanes (`keccakF_eq_segments`). The layout is `Layout.piecewise` of the blocks and the
slices, renamed to the instance's columns; an output lane is routed to its input lane's slice,
a reading no one makes, since the instance reads a derived column through `derived`.

**The public lines** (§8.2). Two: cells `0, 1` of `MEMORY_0` are `input₀, input₂`, of
`MEMORY_1` are `input₁, input₃`. None is sent: the verifier computes every limb's value on its line
itself (`publicInputPhase`).

**The Keccak region** is `QKECCAK`, with `2^τ_KECCAK` steps: `M3Holds` asks of it that every
step's slots `25 … 49` hold the first twelve rounds of its slots `0 … 24`. Its slots `50 … 63`
are bound only by the table's claims on the columns they carry: the Keccak reduction weighs them
nothing.

**The maps.** `stackOf s w` stacks the columns a witness `w` carries: the memory and bytecode
blocks' committed cells, the opcode tables' rows, and, as `QKECCAK`, the `KECCAK` rows' input
lanes, their states after twelve rounds (padding steps: the zero state) and their cells of the
spare columns (`keccakWitness`). `witnessOf prog s q`
reads a witness off any stack `q`, at the memory size `logMem`: the six opcode tables from their
rows, the memory block from the memory columns and the index `g^i`, the bytecode block from the
program and `BFCNT`, the public input from cells `0, 1` of `MEMORY_0, MEMORY_1`; its prover data is
derived from the tables (Clean's `withDerivedData`), so its image is the memory block's limbs.
Clean indexes rows by `u64`: a table that would pass `2^64` rows is read as empty, which
admissible sizes never ask for (`Sizes.Admissible.logMem_lt`, `rows_le_size`). Both maps are total
and computable.

**The bus phase's conditions.** `leanIsa_conditions`: at every size the instance meets
`Bus.Conditions`, so leanVM's master theorems apply to it: the pull side has as many leaves as the
push side (each table pulls as often as it pushes, and the boundary blocks pair up), the count
side has no more (each count is a pull's), and `JUMP`, the one table with constraints, pushes.
With `d = 2` it meets the table sumcheck's degree bound by definition.

The layout, the boundary blocks and the sizes are transcribed from `crates/leanvm_core/src` and
`crates/verifier/src` at leanVM `40f877dc`; the instance's polynomials are Clean's, through
`Component.toM3`.

## Wrong readings excluded

* The `KECCAK` value lanes are not committed columns: a stack carrying the input lanes twice
  would let a prover commit lanes different from `QKECCAK`'s, and nothing would tie the bus to
  the permutation (the region is the sole copy, `layout.rs:19-26`). Likewise the spare columns
  have their one copy in `QKECCAK`'s slots `50 … 63`, as the Rust places them.
* The output lanes are not free: an instance reading them off the stack would let a prover flush
  any output, since the Keccak reduction proves the permutation of the inputs, not a committed
  column.
* The output lanes are not Keccak-f[1600] of the input lanes: the reduction's claims are checked
  against the committed middle state at one point, which, without the Keccak predicate on the whole
  region, says nothing of the permutation of the inputs; the predicate is the relation's own clause,
  which the table sumcheck carries to that point (`Spine/KeccakZero.lean`).
* Ties in the stacking order are broken by global index, the shared columns first; a
  tables-first order places a table whose height equals `2^logMem` before the memory columns.
* The memory index column is the verifier's, never a committed column.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization CompPoly CPoly
open CMlPolynomialEval
open Air.Flat (Component EnsembleWitness)

@[expose] public section

namespace LeanIsa

/-! ## The components -/

/-- The six opcode tables, in the ensemble's order. -/
def opcodeComponent : Fin 6 → Component K
  | 0 => Arithmetization.opcodeComponent xorTable
  | 1 => Arithmetization.opcodeComponent mulTable
  | 2 => Arithmetization.opcodeComponent setTable
  | 3 => Arithmetization.opcodeComponent derefTable
  | 4 => Arithmetization.opcodeComponent jumpTable
  | 5 => Arithmetization.opcodeComponent keccakTable

/-- The channels whose coordinate `1` is a read count: the memory and bytecode pulls (§6.2). -/
def counted (c : RawChannel K) : Bool := c.name = MemPull.name || c.name = BytecodePull.name

/-- Opcode table `j` as an M3 table. -/
def opcodeTable (j : Fin 6) : M3Table K Arithmetization.Direction :=
  (opcodeComponent j).toM3 channelSep channelDir counted

/-- The side of the bus a direction flushes on. -/
def sideOf : Arithmetization.Direction → Side
  | .push => .push
  | .pull => .pull

/-! ## Sizes -/

/-- The announced sizes: the memory log-size, positive, and the six opcode tables'
log-heights. -/
structure Sizes where
  /-- The memory log-size `log_mem`. -/
  logMem : ℕ
  /-- The memory has at least two cells. -/
  logMem_pos : 0 < logMem
  /-- The opcode tables' row counts, in the ensemble's order. -/
  rows : Fin 6 → ℕ

/-- An opcode table's log-height: the least `τ` with `rows ≤ 2^τ` (`log2_ceil`), at least the
table's floor (`TABLE_LOG_FLOORS`, `crates/verifier/src/layout.rs:489-490`): `9` for `KECCAK`, `0`
otherwise. -/
def Sizes.τ (s : Sizes) (j : Fin 6) : ℕ :=
  max (Nat.clog 2 (s.rows j)) (Verifier.tableLogFloors.getD j 0)

/-- An opcode table's rows fit in its height. -/
theorem Sizes.rows_le (s : Sizes) (j : Fin 6) : s.rows j ≤ 2 ^ s.τ j :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

/-- The `KECCAK` table has at least `2^9` rows (`KECCAK_MIN_STEPS_LOG`). -/
theorem Sizes.minSteps_le (s : Sizes) : Verifier.keccakMinStepsLog ≤ s.τ 5 :=
  le_max_right _ _

/-! ## The tables -/

/-- The index of opcode table `j` among the instance's tables. -/
def opIdx (j : Fin 6) : Fin 9 := ⟨j + 3, by omega⟩

/-- The widths: the three memory columns, `BFCNT`, `QKECCAK`, then the opcode tables'. -/
def width : Fin 9 → ℕ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨j + 3, h⟩ => (opcodeComponent ⟨j, by omega⟩).width

/-- The log-heights: the memory's, the program's, `QKECCAK`'s `τ_KECCAK + 6`, then the opcode
tables'. -/
def height (prog : LeanIsaProgram) (s : Sizes) : Fin 9 → ℕ
  | ⟨0, _⟩ => s.logMem
  | ⟨1, _⟩ => prog.logSize
  | ⟨2, _⟩ => s.τ 5 + 6
  | ⟨j + 3, h⟩ => s.τ ⟨j, by omega⟩

/-- The tables of the instance. -/
def shape (prog : LeanIsaProgram) (s : Sizes) : Shape := ⟨9, height prog s, width⟩

/-- The row counts: every row of the memory, bytecode and `QKECCAK` column groups, then the
announced ones. -/
def rows (prog : LeanIsaProgram) (s : Sizes) : Fin 9 → ℕ
  | ⟨0, _⟩ => 2 ^ s.logMem
  | ⟨1, _⟩ => 2 ^ prog.logSize
  | ⟨2, _⟩ => 2 ^ (s.τ 5 + 6)
  | ⟨j + 3, h⟩ => s.rows ⟨j, by omega⟩

/-- Every table's rows fit in its height. -/
theorem rows_le (prog : LeanIsaProgram) (s : Sizes) : ∀ j, rows prog s j ≤ 2 ^ height prog s j
  | ⟨0, _⟩ => le_rfl
  | ⟨1, _⟩ => le_rfl
  | ⟨2, _⟩ => le_rfl
  | ⟨j + 3, h⟩ => s.rows_le ⟨j, by omega⟩

/-- The constraint polynomials: the opcode tables' only. -/
def constraints : (j : Fin 9) → List (CMvPolynomial (width j) K)
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).constraints

/-- The flushes: the opcode tables' only, each on its channel's side. -/
def flushes : (j : Fin 9) → List (Side × Vector (CMvPolynomial (width j) K) 16)
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).flushes.map fun f ↦ (sideOf f.1, f.2)

/-- The count columns: the opcode tables' only. -/
def counts : (j : Fin 9) → List (Fin (width j))
  | ⟨0, _⟩ => []
  | ⟨1, _⟩ => []
  | ⟨2, _⟩ => []
  | ⟨j + 3, h⟩ => (opcodeTable ⟨j, by omega⟩).count

/-- Every assert expression of an opcode table has syntactic degree at most two. -/
theorem opcode_constraints_degreeBound :
    ∀ j : Fin 6, ∀ e ∈ (opcodeComponent j).rowOperations.constraints, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every message coordinate of an opcode table has syntactic degree at most two. -/
theorem opcode_flushes_degreeBound :
    ∀ j : Fin 6, ∀ i ∈ (opcodeComponent j).rowOperations.interactions,
      ∀ e ∈ i.msg.toList, e.degreeBound ≤ 2 := by
  decide +kernel

/-- Every constraint has total degree at most two. -/
theorem constraints_degree : ∀ j, ∀ C ∈ constraints j, C.totalDegree ≤ 2
  | ⟨0, _⟩ => by simp [constraints]
  | ⟨1, _⟩ => by simp [constraints]
  | ⟨2, _⟩ => by simp [constraints]
  | ⟨j + 3, h⟩ => toM3_constraints_degree _ _ _ _ (opcode_constraints_degreeBound ⟨j, by omega⟩)

/-- Every flush coordinate has total degree at most two. -/
theorem flushes_degree : ∀ j, ∀ f ∈ flushes j, ∀ k, (f.2.get k).totalDegree ≤ 2
  | ⟨0, _⟩ => by simp [flushes]
  | ⟨1, _⟩ => by simp [flushes]
  | ⟨2, _⟩ => by simp [flushes]
  | ⟨j + 3, h⟩ => by
    intro f hf k
    obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
    exact toM3_flushes_degree _ _ _ _ (opcode_flushes_degreeBound ⟨j, by omega⟩) f' hf' k

/-! ## The columns -/

/-- A column of the instance: table `j`, column `i`. -/
abbrev Col : Type := Σ j : Fin 9, Fin (width j)

/-- Memory column `i`: `MEMORY_0, MEMORY_1, MFCNT`. -/
def memCol (i : Fin 3) : Col := ⟨⟨0, by decide⟩, i⟩

/-- The bytecode finalize count `BFCNT`. -/
def bfcntCol : Col := ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

/-- The Keccak reduction's column `QKECCAK`. -/
def keccakCol : Col := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩

/-- The `KECCAK` table has ninety-two columns. -/
theorem width_keccak : width (opIdx 5) = 92 := by decide +kernel

/-- Input lane `l` of the `KECCAK` table: its column `15 + l`. -/
def inCol (l : Fin 25) : Col := ⟨opIdx 5, ⟨15 + l, by rw [width_keccak]; omega⟩⟩

/-- Output lane `l` of the `KECCAK` table: its column `40 + l`. -/
def outCol (l : Fin 25) : Col := ⟨opIdx 5, ⟨40 + l, by rw [width_keccak]; omega⟩⟩

/-- The column is a `KECCAK` value lane, input or output: not committed in a block of its own
(`KECCAK_IN … KECCAK_CNT`, `crates/verifier/src/layout.rs:394-396`; `KeccakLane::Input`/`Output`,
`crates/leanvm_core/src/cpu/layout.rs`). -/
def IsLane (c : Col) : Prop := c.1 = opIdx 5 ∧ 15 ≤ c.2.val ∧ c.2.val < 65

instance (c : Col) : Decidable (IsLane c) := inferInstanceAs (Decidable (_ ∧ _))

/-- The column is one of the `KECCAK` table's first fourteen committed columns (its columns
`0 … 13`: `pc`, `fp`, the operands, the layout flags and the output flags `out_two`, `out_all`),
which ride the spare slots `50 … 63` of `QKECCAK` (`qkeccak_slot`,
`crates/verifier/src/layout.rs:422-432`;
`KeccakLane::Slot`, `crates/leanvm_core/src/cpu/layout.rs:56-111`). -/
def IsSpare (c : Col) : Prop := c.1 = opIdx 5 ∧ c.2.val < 14

instance (c : Col) : Decidable (IsSpare c) := inferInstanceAs (Decidable (_ ∧ _))

/-- The column has no block of its own: a `KECCAK` value lane or a column riding a spare slot of
`QKECCAK`, the `KECCAK` table's columns `0 … 64` but `14` (`free`, committed in a block of its
own) (the Rust's virtual columns, `keccak_value`, `crates/leanvm_core/src/cpu/layout.rs:228-240`). -/
def IsVirtual (c : Col) : Prop := c.1 = opIdx 5 ∧ c.2.val < 65 ∧ c.2.val ≠ 14

instance (c : Col) : Decidable (IsVirtual c) := inferInstanceAs (Decidable (_ ∧ _))

/-- A lane is virtual. -/
theorem IsLane.isVirtual {c : Col} (h : IsLane c) : IsVirtual c :=
  ⟨h.1, by have := h.2; omega, by have := h.2; omega⟩

/-- A spare column is virtual. -/
theorem IsSpare.isVirtual {c : Col} (h : IsSpare c) : IsVirtual c :=
  ⟨h.1, by have := h.2; omega, by have := h.2; omega⟩

/-- A virtual column is a lane or a spare column. -/
theorem IsVirtual.lane_or_spare {c : Col} (h : IsVirtual c) : IsLane c ∨ IsSpare c := by
  by_cases h' : 15 ≤ c.2.val ∧ c.2.val < 65
  · exact .inl ⟨h.1, h'⟩
  · exact .inr ⟨h.1, by have := h.2; omega⟩

/-- The column is a `KECCAK` output lane: derived from the input lanes. -/
def IsOut (c : Col) : Prop := c.1 = opIdx 5 ∧ 40 ≤ c.2.val ∧ c.2.val < 65

instance (c : Col) : Decidable (IsOut c) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every column, in global order: table by table, column by column. -/
def columns : List Col := (List.finRange 9).flatMap fun j ↦ (List.finRange (width j)).map (⟨j, ·⟩)

/-- The committed columns, in global order: every column but the virtual ones, the `KECCAK`
value lanes and the columns riding `QKECCAK`'s spare slots. -/
def committedColumns : List Col := columns.filter fun c ↦ !decide (IsVirtual c)

/-- A column that is not virtual is committed. -/
theorem mem_committedColumns {c : Col} (h : ¬ IsVirtual c) : c ∈ committedColumns := by
  simp only [committedColumns, columns, List.mem_filter, List.mem_flatMap, List.mem_finRange,
    List.mem_map, true_and, h, decide_false, Bool.not_false, and_true]
  exact ⟨c.1, c.2, rfl⟩

/-! ## The stack -/

variable (prog : LeanIsaProgram) (s : Sizes)

/-- The log-height of a column: its table's. -/
abbrev kappa (c : Col) : ℕ := height prog s c.1

/-- The committed columns in stacking order: largest first, ties in global order
(`witness.rs:56-75`; `List.mergeSort` is stable). -/
def stackOrder : List Col :=
  committedColumns.mergeSort fun a b ↦ decide (kappa prog s b ≤ kappa prog s a)

/-- Largest first. -/
theorem stackOrder_pairwise :
    (stackOrder prog s).Pairwise fun a b ↦ decide (kappa prog s b ≤ kappa prog s a) :=
  List.pairwise_mergeSort (fun _ _ _ h₁ h₂ ↦ by simp only [decide_eq_true_eq] at *; omega)
    (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The committed columns as aligned blocks, in stacking order. -/
def blocks : Blocks where
  n := (stackOrder prog s).length
  size b := kappa prog s (stackOrder prog s)[b]
  descending a b hab := by
    rcases (Fin.le_iff_val_le_val.mp hab).eq_or_lt with h | h
    · rw [Fin.ext h]
    · have := List.pairwise_iff_getElem.mp (stackOrder_pairwise prog s) a b a.isLt b.isLt h
      simp only [decide_eq_true_eq] at this
      exact this

/-- The minimum stacked size, `MIN_MU` (`pcs.rs:49`). -/
def minMu : ℕ := 15

/-- The maximum stacked size, `MAX_MU` (`pcs.rs:51`). -/
def maxMu : ℕ := 28

/-- The stack's number of variables: the blocks' total, rounded up to a power of two, at least
`2 ^ MIN_MU` (`placements_of`, `witness.rs:91`). -/
def leanIsaμ : ℕ := max (Nat.clog 2 (blocks prog s).total) minMu

/-- The blocks fit on the stack. -/
theorem blocks_fits : (blocks prog s).total ≤ 2 ^ leanIsaμ prog s :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))

variable {prog s} in
/-- The block of a committed column. -/
def blockOf (c : Col) (h : ¬ IsVirtual c) : Fin (blocks prog s).n :=
  ⟨(stackOrder prog s).idxOf c,
    List.idxOf_lt_length_of_mem (List.mem_mergeSort.mpr (mem_committedColumns h))⟩

/-- The block of a committed column holds that column. -/
theorem stackOrder_blockOf (c : Col) (h : ¬ IsVirtual c) :
    (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = c :=
  List.getElem_idxOf _

/-- A committed column's block has the column's log-height. -/
theorem size_blockOf (c : Col) (h : ¬ IsVirtual c) :
    (blocks prog s).size (blockOf c h) = kappa prog s c := by
  show kappa prog s (stackOrder prog s)[(blockOf (prog := prog) (s := s) c h : ℕ)] = _
  rw [stackOrder_blockOf]

/-- `QKECCAK` is committed. -/
theorem not_isVirtual_keccakCol : ¬ IsVirtual keccakCol := by decide

/-- The block of `QKECCAK`. -/
def keccakBlock : Fin (blocks prog s).n := blockOf keccakCol not_isVirtual_keccakCol

/-- The block of `QKECCAK` has `τ_KECCAK + 6` variables. -/
theorem size_keccakBlock : (blocks prog s).size (keccakBlock prog s) = s.τ 5 + 6 :=
  size_blockOf prog s _ _

/-- The slot of `QKECCAK` a virtual column is read at: input lane `l`'s is `l`, output lane `l`
is routed to input lane `l`'s (a reading no one makes, `derived`), and the spare columns `0 … 13`
are slots `50 … 63` (`qkeccak_slot`, `crates/verifier/src/layout.rs:422-432`); `0` for a column
with no slot. -/
def qSlot (c : Col) : Fin 64 :=
  ⟨if c.2.val < 14 then 50 + c.2.val else if c.2.val < 65 then (c.2.val - 15) % 25 else 0, by
    split_ifs <;> omega⟩

/-- Input lane `l` is read at slot `l`. -/
theorem qSlot_inCol (l : Fin 25) : qSlot (inCol l) = ⟨l, by omega⟩ := by
  apply Fin.ext
  show (if 15 + l.val < 14 then 50 + (15 + l.val) else
    if 15 + l.val < 65 then (15 + l.val - 15) % 25 else 0) = l.val
  split_ifs <;> omega

/-- Where a column is read: a committed column at its block, a virtual one at its slot of
`QKECCAK`. -/
def route (c : Col) : Fin (blocks prog s).n ⊕ Fin 64 :=
  if h : IsVirtual c then .inr (qSlot c) else .inl (blockOf c h)

/-- A route keeps the column's log-height. -/
theorem route_kappa (c : Col) :
    Sum.elim (blocks prog s).size (fun _ ↦ s.τ 5) (route prog s c) = kappa prog s c := by
  unfold route
  split_ifs with h
  · simp only [Sum.elim_inr, kappa, h.1]
    rfl
  · simp only [Sum.elim_inl, size_blockOf]

/-- The layout of the stack: the committed columns at their aligned blocks, a virtual column of
the `KECCAK` table at its slot of `QKECCAK` (`qSlot`). -/
def layout : Layout (leanIsaμ prog s) Col (kappa prog s) :=
  (((blocks prog s).layout (blocks_fits prog s)).piecewise
    ((blocks prog s).sliceLayout (blocks_fits prog s) (keccakBlock prog s) 6
      (fun l : Fin 64 ↦ (⟨l, by omega⟩ : Fin (2 ^ 6)))
      (κ := fun _ ↦ s.τ 5) fun _ ↦ size_keccakBlock prog s)).comap (route prog s)
    (route_kappa prog s)

/-- A virtual column has `KECCAK`'s log-height. -/
theorem kappa_of_isVirtual {c : Col} (h : IsVirtual c) : kappa prog s c = s.τ 5 := by
  simp only [kappa, h.1]
  rfl

/-- A lane has `KECCAK`'s log-height. -/
theorem kappa_of_isLane {c : Col} (h : IsLane c) : kappa prog s c = s.τ 5 :=
  kappa_of_isVirtual prog s h.isVirtual

/-- The Keccak region: `QKECCAK`, `2 ^ τ_KECCAK` steps. -/
def keccakRegion : KeccakRegion (shape prog s) := ⟨keccakCol, s.τ 5, rfl⟩

/-- The state after twelve rounds the stack commits at step `x`: slots `25 … 49` of `QKECCAK`. -/
def midState (q : Column (leanIsaμ prog s)) (x : Fin (2 ^ s.τ 5)) : KeccakState :=
  (keccakRegion prog s).state ((layout prog s).read q keccakCol) 25 x

/-- The output column `c`: at row `x`, its lane of the last twelve rounds of Keccak-f[1600] of
the state after twelve rounds committed at step `x` (`midState`). With the Keccak predicate (the
committed state is the first twelve rounds of the row's input lanes), this is the lane of
Keccak-f[1600] of the input lanes (`keccakF_eq_segments`). -/
def outColumn (q : Column (leanIsaμ prog s)) (c : Col) (h : IsOut c) : Column (kappa prog s c) :=
  ⟨Vector.ofFn fun x ↦
    stateLanes (keccakSegment 1 (midState prog s q
      (Fin.cast (congrArg (2 ^ ·) (kappa_of_isLane prog s ⟨h.1, by have := h.2.1; omega, h.2.2⟩))
        x))) ⟨c.2.val - 40, by have := h.2.2; omega⟩⟩

/-- The derived columns: the `KECCAK` output lanes. -/
def derived (c : Col) : Option (Column (leanIsaμ prog s) → Column (kappa prog s c)) :=
  if h : IsOut c then some fun q ↦ outColumn prog s q c h else none

/-! ## The bus -/

/-- Sixteen coordinates: the given ones, then constant zeros. -/
def coords {S : Shape} {κ : ℕ} (cs : List (Coord S κ)) : Vector (Coord S κ) 16 :=
  Vector.ofFn fun k ↦ cs.getD k (.const 0)

/-- Column `k` of the program's entries, `bytecode_columns` (`layout.rs:295`): the entry's
coordinate `k` at every slot, coordinate `3 + k` of the bytecode tuple. -/
def entryColumn (k : Fin 13) : Column prog.logSize :=
  ⟨Vector.ofFn fun i ↦ (busEntry (prog.instructions i))[k]⟩

/-- The six boundary blocks (`layout.rs:425-468`): the state boundary, the memory seed and
finalize, the bytecode seed and finalize. -/
def boundary : List (BoundaryBlock (shape prog s)) :=
  let entries : List (Coord (shape prog s) prog.logSize) :=
    (List.finRange 13).map fun k ↦ .known (entryColumn prog k)
  [⟨0, .push, coords [.const (channelSep StatePush.toRaw), .const 1, .const 1]⟩,
    ⟨s.logMem, .push, coords [.const (channelSep MemPush.toRaw), .known (idxColumn s.logMem),
      .const 1, .committed (memCol 0) rfl, .committed (memCol 1) rfl]⟩,
    ⟨prog.logSize, .push, coords ([.const (channelSep BytecodePush.toRaw),
      .known (idxColumn prog.logSize), .const 1] ++ entries)⟩,
    ⟨0, .pull, coords [.const (channelSep StatePull.toRaw), .const prog.pcFinal, .const 1]⟩,
    ⟨s.logMem, .pull, coords [.const (channelSep MemPull.toRaw), .known (idxColumn s.logMem),
      .committed (memCol 2) rfl, .committed (memCol 0) rfl, .committed (memCol 1) rfl]⟩,
    ⟨prog.logSize, .pull, coords ([.const (channelSep BytecodePull.toRaw),
      .known (idxColumn prog.logSize), .committed bfcntCol rfl] ++ entries)⟩]

/-- The two public lines (§8.2): `MEMORY_0` holds `input₀, input₂` at cells `0, 1`, `MEMORY_1`
holds `input₁, input₃`; none is sent. -/
def publicLines (input : PublicInput) : Vector (PublicLine (shape prog s)) 2 :=
  #v[⟨memCol 0, input.lanes 0, input.lanes 2, false, s.logMem_pos⟩,
    ⟨memCol 1, input.lanes 1, input.lanes 3, false, s.logMem_pos⟩]

/-- The verifier's padding row of a table, in `K` (`Table::padding`,
`crates/verifier/src/layout.rs:455-460`): zero, but for the `KECCAK` output lanes, which hold
Keccak-f[1600] of the zero state. -/
def padRowK (t : Verifier.Table) : List K :=
  (List.range t.width).map fun i ↦
    if t.opcode = Verifier.opKeccak ∧ Verifier.keccakOut ≤ i ∧ i < Verifier.keccakOut + 25 then
      K.ofBits (Keccak.lane (keccakF1600 (Vector.replicate 25 0)) (i - Verifier.keccakOut)).toNat
    else 0

theorem padRowK_length (t : Verifier.Table) : (padRowK t).length = t.width := by
  simp [padRowK]

/-- The verifier's padding row is `padRowK`, lifted to `E`. -/
theorem padding_eq_map_ofK (t : Verifier.Table) : t.padding = (padRowK t).map ofK := by
  simp only [Verifier.Table.padding, padRowK, List.map_map]
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-! ### The `KECCAK` padding row, by column -/

/-- The `KECCAK` table has ninety-two column names. -/
theorem keccakColumns_length : Verifier.keccakColumns.length = 92 := by decide +kernel

/-- `KECCAK_OUT` is column `40`. -/
theorem keccakOut_eq : Verifier.keccakOut = 40 := by decide +kernel

/-- The zero state's lanes. -/
theorem laneState_zero : laneState (fun _ ↦ 0) = Vector.replicate 25 0 := by
  apply Vector.ext
  intro i hi
  simp only [laneState, Vector.getElem_ofFn, Vector.getElem_replicate]
  rfl

/-- The `KECCAK` padding row, column by column: the output lanes hold Keccak-f[1600] of the zero
state, every other column zero. -/
theorem padRowK_keccak_getD (i : ℕ) (hi : i < 92) :
    (padRowK (Verifier.tables.getD 5 default)).getD i 0 =
      if h : 40 ≤ i ∧ i < 65 then
        stateLanes (keccakF1600 (laneState fun _ ↦ 0)) ⟨i - 40, by omega⟩
      else 0 := by
  have hw : (Verifier.tables.getD 5 default).width = 92 := by decide +kernel
  have ho : (Verifier.tables.getD 5 default).opcode = Verifier.opKeccak := rfl
  rw [padRowK, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega),
    Option.map_some, Option.getD_some, keccakOut_eq]
  by_cases h : 40 ≤ i ∧ i < 65
  · rw [ite_eq_left ⟨ho, h⟩, dite_eq_left h, laneState_zero]
    simp only [stateLanes, K.ofLane, K.ofBits]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [ite_eq_right (fun h' ↦ h h'.2), dite_eq_right h]

/-- The public row a padding row holds: the verifier's (`padRowK`) for an opcode table, zero for
the column groups, which have no padding row. -/
def padRow (j : Fin 9) (i : Fin (width j)) : K :=
  if 3 ≤ j.val then (padRowK (Verifier.tables.getD (j.val - 3) default)).getD i 0 else 0

/-- Off the `KECCAK` table, the padding row is zero. -/
theorem padRow_of_ne_keccak :
    ∀ j : Fin 6, j ≠ 5 → ∀ i : Fin (width (opIdx j)), padRow (opIdx j) i = 0 := by
  decide +kernel

/-- The `KECCAK` padding row: Keccak-f[1600] of the zero state at the output lanes, zero
elsewhere. -/
theorem padRow_keccak (i : Fin (width (opIdx 5))) :
    padRow (opIdx 5) i = if h : 40 ≤ i.val ∧ i.val < 65 then
      stateLanes (keccakF1600 (laneState fun _ ↦ 0)) ⟨i.val - 40, by omega⟩ else 0 :=
  padRowK_keccak_getD i.val (width_keccak ▸ i.isLt)

end LeanIsa

open LeanIsa

/-- The leanISA instance of the public program `prog` at the announced sizes `s`. -/
abbrev leanIsaInstance (prog : LeanIsaProgram) (s : Sizes) : M3Instance where
  toShape := shape prog s
  Stmt := PublicInput
  constraints := constraints
  flushes := flushes
  d := 2
  constraints_degree := constraints_degree
  flushes_degree := flushes_degree
  counts := counts
  rows := rows prog s
  rows_le := rows_le prog s
  padRow := padRow
  boundary := boundary prog s
  μ := leanIsaμ prog s
  layout := layout prog s
  derived := derived prog s
  nLines := 2
  publicLines := publicLines prog s
  keccak := some (keccakRegion prog s)

namespace LeanIsa

/-! ## Admissible sizes -/

/-- The checks the verifier makes of the announced sizes (`build_layout`,
`crates/verifier/src/layout.rs:497-503`, and `lib.rs:228-231`): the memory window, the row cap,
and the stacked size's cap. The bytecode cap is `Program`'s by type, and the stacked size's floor
holds by construction (`leanIsaμ`). -/
def Sizes.Admissible (prog : LeanIsaProgram) (s : Sizes) : Prop :=
  minLogMem ≤ s.logMem ∧ s.logMem ≤ maxLogMem ∧ (∀ j, s.rows j ≤ 2 ^ maxLogRows) ∧
    leanIsaμ prog s ≤ maxMu

instance (prog : LeanIsaProgram) (s : Sizes) : Decidable (s.Admissible prog) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The WHIR rate check (`pcs/src/whir_config.rs:44-56`): the inverse rate's logarithm is in
`[1, 4]`. A parameter of the commitment, read off the same announcement. -/
def validRate (ρ : ℕ) : Prop := 1 ≤ ρ ∧ ρ ≤ 4

instance (ρ : ℕ) : Decidable (validRate ρ) := inferInstanceAs (Decidable (_ ∧ _))

/-- The sizes a witness carries: the memory log-size of its image and the row counts of its six
opcode tables; none when the image has a single word. -/
def Sizes.ofWitness {prog : LeanIsaProgram} {κ : ℕ} (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    Option Sizes :=
  if h : 0 < (imageOf w.data).1 then
    some ⟨_, h, fun j ↦ (tableAt w ⟨j, by omega⟩).table.length⟩
  else none

/-! ## The witness read off a stack -/

section WitnessOf

variable (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s))

/-- Cell `x` of column `c`, read off the stack. -/
abbrev cell (c : Col) (x : Fin (2 ^ kappa prog s c)) : K :=
  ((leanIsaInstance prog s).column q c).values.get x

/-- The executed rows of opcode table `j`, read off the stack: its padding rows are not the
witness's. -/
def opcodeRows (j : Fin 6) : List (Array K) :=
  List.ofFn fun x : Fin (s.rows j) ↦
    Array.ofFn ((leanIsaInstance prog s).row q (opIdx j) (Fin.castLE (s.rows_le j) x))

/-- The memory block's rows: the two limbs, the index `g^x`, the finalize count `MFCNT`. -/
def memBlockRowsOf : List (Array K) :=
  List.ofFn fun x : Fin (2 ^ s.logMem) ↦ (toElements (⟨#v[cell prog s q (memCol 0) x,
    cell prog s q (memCol 1) x], addressOfIndex x, cell prog s q (memCol 2) x⟩ : MemRow K)).toArray

/-- The bytecode block's rows: the program's, with the finalize counts `BFCNT`. -/
def bytecodeBlockRowsOf : List (Array K) :=
  List.ofFn fun i : Fin (2 ^ prog.logSize) ↦
    (toElements (bytecodeRowOf prog i (cell prog s q bfcntCol i))).toArray

/-- The memory image: the two limb columns, word by word. -/
def imageRows : Array (Vector K 2) :=
  Array.ofFn fun x : Fin (2 ^ s.logMem) ↦ #v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x]

/-- Cell `0` of a memory column. -/
def cell0 (i : Fin 3) : K := cell prog s q (memCol i) ⟨0, Nat.two_pow_pos _⟩

/-- Cell `1` of a memory column. -/
def cell1 (i : Fin 3) : K := cell prog s q (memCol i) ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩

/-- The public input: cells `0` and `1` of `MEMORY_0` and `MEMORY_1`. -/
def publicInputOf : PublicIO K :=
  ⟨#v[cell0 prog s q 0, cell0 prog s q 1, cell1 prog s q 0, cell1 prog s q 1]⟩

/-- A table of rows of the component's width, at most `2^64` of them and agreeing with its fixed
cells, with prover data of its own rows only: `witnessOf` replaces it by the data derived from
all the tables (`Air.Flat.withDerivedData`), as Clean's witness generator does. -/
def tableOf (c : Component K) (rows : List (Array K)) (h : ∀ r ∈ rows, r.size = c.width)
    (hlen : rows.length ≤ UInt64.size) (hfix : c.FixedRowsMatch rows) : Air.Flat.Table K where
  component := c
  table := rows
  data name n :=
    if name = c.circuit.name then (rows.map (Air.Flat.rowPrefix n)).toArray else #[]
  uniform_width := h
  length_le := hlen
  fixed_rows_match := hfix
  data_consistent := by simp

/-- The typed rows of a list of rows built from typed rows are those rows. -/
theorem fromElements_ofFn {Row : TypeMap} [ProvableType Row] {n : ℕ} (f : Fin n → Row K) (i : ℕ)
    (hi : i < (List.ofFn fun x ↦ (toElements (f x)).toArray).length) :
    (fromElements (Air.Flat.rowPrefix (size Row)
        (List.ofFn fun x ↦ (toElements (f x)).toArray)[i]) : Row K) =
      f ⟨i, by simpa using hi⟩ := by
  rw [List.getElem_ofFn]
  have : Air.Flat.rowPrefix (size Row) (toElements (f ⟨i, by simpa using hi⟩)).toArray =
      toElements (f ⟨i, by simpa using hi⟩) :=
    Vector.toArray_inj.mp (rowPrefix_toArray (by simp))
  rw [this, ProvableType.fromElements_toElements]

/-- The stack's memory block has `2^logMem` rows. -/
theorem memBlockRowsOf_length : (memBlockRowsOf prog s q).length = 2 ^ s.logMem :=
  List.length_ofFn

/-- Row `i` of the stack's memory block, typed: the limbs of word `i`, `g^i`, `MFCNT_i`. -/
theorem memBlockRowsOf_row (x : Fin (2 ^ s.logMem)) :
    (fromElements (Air.Flat.rowPrefix (size MemRow) ((memBlockRowsOf prog s q)[x.val]'(by
      rw [memBlockRowsOf_length]; exact x.isLt))) : MemRow K) =
      ⟨#v[cell prog s q (memCol 0) x, cell prog s q (memCol 1) x], addressOfIndex x,
        cell prog s q (memCol 2) x⟩ := by
  unfold memBlockRowsOf
  exact fromElements_ofFn _ x.val (by simp)

/-- The stack's bytecode block has `2^N` rows. -/
theorem bytecodeBlockRowsOf_length : (bytecodeBlockRowsOf prog s q).length = 2 ^ prog.logSize :=
  List.length_ofFn

/-- Row `i` of the stack's bytecode block, typed: the program's row of slot `i`, `BFCNT_i`. -/
theorem bytecodeBlockRowsOf_row (i : Fin (2 ^ prog.logSize)) :
    (fromElements (Air.Flat.rowPrefix (size BytecodeRow) ((bytecodeBlockRowsOf prog s q)[i.val]'(by
      rw [bytecodeBlockRowsOf_length]; exact i.isLt))) : BytecodeRow K) =
      bytecodeRowOf prog i (cell prog s q bfcntCol i) := by
  unfold bytecodeBlockRowsOf
  exact fromElements_ofFn _ i.val (by simp)

/-- Opcode table `j` read off the stack: its executed rows, none past `2^64` of them. -/
def opTableOf (j : Fin 6) : Air.Flat.Table K :=
  if h : s.rows j ≤ UInt64.size then
    tableOf (opcodeComponent j) (opcodeRows prog s q j) (by
      simp only [opcodeRows, List.mem_ofFn, forall_exists_index]
      rintro _ x rfl
      exact Array.size_ofFn) (by simpa [opcodeRows] using h) (by fin_cases j <;> trivial)
  else tableOf (opcodeComponent j) [] (by simp) (by simp) (by fin_cases j <;> trivial)

/-- The memory block read off the stack: its `2^logMem` rows, the index column the row's `g^x`;
no row past `2^64` words. -/
def memTableOf : Air.Flat.Table K :=
  if h : s.logMem < 64 then
    tableOf (memComponent s.logMem) (memBlockRowsOf prog s q) (by
      simp only [memBlockRowsOf, List.mem_ofFn, forall_exists_index]
      rintro _ x rfl
      rw [Vector.size_toArray, memComponent_width]
      rfl) (by
      rw [memBlockRowsOf, List.length_ofFn]
      exact (Nat.pow_lt_pow_right (by norm_num) h).le) (by
      have h64 : 2 ^ s.logMem < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) h
      refine ⟨by rw [memBlockRowsOf_length, memMode, UInt64.toNat_ofNat_of_lt' h64],
        fun i hi ↦ ?_⟩
      have hi' : i < 2 ^ s.logMem := memBlockRowsOf_length prog s q ▸ hi
      have hu : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (hi'.trans h64)
      refine (memMode_fixedAt (by rw [hu]; exact hi') _).mpr ?_
      show (fromElements (Air.Flat.rowPrefix (size MemRow) (memBlockRowsOf prog s q)[i]) :
        MemRow K).idx = _
      rw [memBlockRowsOf_row prog s q ⟨i, hi'⟩, hu])
  else tableOf (memComponent s.logMem) [] (by simp) (by simp) (by
      refine ⟨?_, fun i hi ↦ absurd hi (by simp)⟩
      show 0 = (UInt64.ofNat (2 ^ s.logMem)).toNat
      obtain ⟨k, hk⟩ : ∃ k, s.logMem = 64 + k := ⟨s.logMem - 64, by omega⟩
      rw [hk, pow_add, UInt64.toNat_ofNat', Nat.mul_mod_right])

/-- The bytecode block read off the stack: the program's rows, with the finalize counts `BFCNT`. -/
def bytecodeTableOf : Air.Flat.Table K :=
  have h64 : 2 ^ prog.logSize < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num)
    (lt_of_le_of_lt prog.logSize_le (by decide))
  tableOf (bytecodeComponent prog) (bytecodeBlockRowsOf prog s q) (by
    simp only [bytecodeBlockRowsOf, List.mem_ofFn, forall_exists_index]
    rintro _ x rfl
    rw [Vector.size_toArray, bytecodeComponent_width]
    rfl) (by
    rw [bytecodeBlockRowsOf, List.length_ofFn]
    exact h64.le) (by
    refine ⟨by rw [bytecodeBlockRowsOf_length, bytecodeMode, UInt64.toNat_ofNat_of_lt' h64],
      fun i hi ↦ ?_⟩
    have hi' : i < 2 ^ prog.logSize := bytecodeBlockRowsOf_length prog s q ▸ hi
    have hu : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (hi'.trans h64)
    refine (bytecodeMode_fixedAt prog (by rw [hu]; exact hi') _).mpr ?_
    change (fromElements (Air.Flat.rowPrefix (size BytecodeRow) (bytecodeBlockRowsOf prog s q)[i]) :
      BytecodeRow K) = bytecodeRowOf prog _ (fromElements (Air.Flat.rowPrefix (size BytecodeRow)
        (bytecodeBlockRowsOf prog s q)[i]) : BytecodeRow K).cntFin
    rw [bytecodeBlockRowsOf_row prog s q ⟨i, hi'⟩]
    simp only [hu]
    rfl)

/-- The tables read off the stack, each with the data of its own rows. -/
def witnessTables : List (Air.Flat.Table K) :=
  [opTableOf prog s q 0, opTableOf prog s q 1, opTableOf prog s q 2, opTableOf prog s q 3,
    opTableOf prog s q 4, opTableOf prog s q 5, memTableOf prog s q, bytecodeTableOf prog s q]

/-- The tables' components are the ensemble's. -/
theorem witnessTables_components :
    (witnessTables prog s q).map (·.component) = (leanIsaEnsemble prog s.logMem).tables := by
  simp only [witnessTables, opTableOf, memTableOf, bytecodeTableOf, List.map_cons, List.map_nil]
  split_ifs <;> rfl

/-- The tables' components have the ensemble's distinct names. -/
theorem witnessTables_names :
    ((witnessTables prog s q).map fun t ↦ t.component.circuit.name).Nodup := by
  have h := (leanIsaEnsemble prog s.logMem).unique_names
  rw [← witnessTables_components, List.map_map] at h
  exact h

/-- The witness a stack carries: the six opcode tables from their rows, the memory and
bytecode blocks from the memory columns, the program and `BFCNT`, the public input from the first
two cells of `MEMORY_0` and `MEMORY_1`. Its prover data is derived from its tables: the image is the
memory block's limbs. -/
def witnessOf : EnsembleWitness (leanIsaEnsemble prog s.logMem) where
  tables := Air.Flat.withDerivedData (witnessTables prog s q) (witnessTables_names prog s q)
  publicInput := publicInputOf prog s q
  same_length := by simp [Air.Flat.withDerivedData, witnessTables, leanIsaEnsemble]
  same_circuits i hi := by
    have h := congrArg (·[i]?) ((Air.Flat.withDerivedData_map_component _
      (witnessTables_names prog s q)).trans (witnessTables_components prog s q))
    simp only [List.getElem?_map] at h
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by
      have := congrArg List.length ((Air.Flat.withDerivedData_map_component _
        (witnessTables_names prog s q)).trans (witnessTables_components prog s q))
      simp only [List.length_map] at this
      omega)] at h
    exact (Option.some.inj h).symm
  same_data := Air.Flat.withDerivedData_data _ _

/-- The witness's tables are the ones read off the stack, rows for rows. -/
theorem witnessOf_table (j : Fin 8) :
    (tableAt (witnessOf prog s q) j).table =
      ((witnessTables prog s q)[(j : ℕ)]'(by simp [witnessTables])).table := by
  have h := congrArg (·[(j : ℕ)]?) (Air.Flat.withDerivedData_map (witnessTables prog s q)
    (witnessTables_names prog s q))
  simp only [List.getElem?_map] at h
  have hl := congrArg List.length (Air.Flat.withDerivedData_map (witnessTables prog s q)
    (witnessTables_names prog s q))
  simp only [List.length_map] at hl
  rw [List.getElem?_eq_getElem (by rw [hl]; simp [witnessTables]),
    List.getElem?_eq_getElem (by simp [witnessTables])] at h
  exact (congrArg Prod.snd (Option.some.inj h))

/-- Opcode table `j` read off the stack holds the executed rows, when they number at most
`2^64`. -/
theorem opTableOf_table {j : Fin 6} (h : s.rows j ≤ UInt64.size) :
    (opTableOf prog s q j).table = opcodeRows prog s q j := by
  simp [opTableOf, h, tableOf]

/-- The memory block read off the stack holds the stack's rows, when they number less than
`2^64`. -/
theorem memTableOf_table (h : s.logMem < 64) :
    (memTableOf prog s q).table = memBlockRowsOf prog s q := by
  simp [memTableOf, h, tableOf]

/-- The bytecode block read off the stack holds the program's rows with the stack's `BFCNT`. -/
theorem bytecodeTableOf_table : (bytecodeTableOf prog s q).table = bytecodeBlockRowsOf prog s q :=
  rfl

/-- The image the witness's data names is the stack's limb columns, when the memory has fewer than
`2^64` words: the data is derived from the memory block, whose rows begin with the limbs. -/
theorem memRows_witnessOf (h : s.logMem < 64) :
    memRows (witnessOf prog s q).data = imageRows prog s q := by
  rw [memRows_data, show memBlockRows (witnessOf prog s q) = memBlockRowsOf prog s q from
    (witnessOf_table prog s q 6).trans (memTableOf_table prog s q h)]
  apply Array.ext
  · simp [imageRows, memBlockRowsOf_length]
  · intro i h1 h2
    have hi : i < 2 ^ s.logMem := by simpa [imageRows] using h2
    simp only [List.getElem_toArray, List.getElem_map, imageRows, Array.getElem_ofFn]
    unfold memBlockRowsOf
    rw [List.getElem_ofFn]
    apply Vector.ext
    intro k hk
    interval_cases k <;>
      simp [Air.Flat.rowPrefix, explicit_provable_type, ProvableStruct.toComponents, toElements,
        ProvableStruct.componentsToElements, components, toComponents,
        ProvableStruct.structToElements_eq]

end WitnessOf

/-- Admissible sizes fit the `u64` row indices: fewer than `2^64` memory words. -/
theorem Sizes.Admissible.logMem_lt {prog : LeanIsaProgram} {s : Sizes} (h : s.Admissible prog) :
    s.logMem < 64 :=
  lt_of_le_of_lt h.2.1 (by decide)

/-- Admissible sizes fit the `u64` row indices: at most `2^64` rows per opcode table. -/
theorem Sizes.Admissible.rows_le_size {prog : LeanIsaProgram} {s : Sizes} (h : s.Admissible prog)
    (j : Fin 6) : s.rows j ≤ UInt64.size :=
  (h.2.2.1 j).trans (by norm_num [maxLogRows, UInt64.size])

/-! ## The stack of a witness -/

section StackOf

variable (prog : LeanIsaProgram) (s : Sizes) {κ : ℕ}

/-- Cell `i` of row `x` of a table, `0` when missing. -/
def cellOf (t : Air.Flat.Table K) (x i : ℕ) : K := ((t.table[x]?).bind (·[i]?)).getD 0

/-- The memory block's cell of memory column `i`: the limbs at `0, 1`, `MFCNT` at `3`. -/
def memRowCell : Fin 3 → ℕ := ![0, 1, 3]

/-- Input lane `l` of row `x` of the `KECCAK` table; a padding row's is zero (`padRow`). -/
def inLaneOf (w : EnsembleWitness (leanIsaEnsemble prog κ)) (x : ℕ) (l : Fin 25) : K :=
  if x < s.rows 5 then cellOf (tableAt w 5) x (15 + l) else 0

/-- The `KECCAK` column spare slot `50 + k` of `QKECCAK` carries: column `k`, the table's first
fourteen committed columns in order (`spare_local`, `crates/verifier/src/layout.rs:399-404`). -/
def spareColumn (k : ℕ) : ℕ := k

/-- A spare column's slot is `50` or above, and `spareColumn` names the column back. -/
theorem qSlot_spare {c : Col} (h : IsSpare c) :
    50 ≤ (qSlot c).val ∧ spareColumn ((qSlot c).val - 50) = c.2.val := by
  show 50 ≤ (if c.2.val < 14 then 50 + c.2.val else
      if c.2.val < 65 then (c.2.val - 15) % 25 else 0) ∧
    spareColumn ((if c.2.val < 14 then 50 + c.2.val else
      if c.2.val < 65 then (c.2.val - 15) % 25 else 0) - 50) = c.2.val
  unfold spareColumn
  have h' := h.2
  split_ifs
  omega

/-- `QKECCAK` of a witness (`crates/leanvm_core/src/keccak.rs`, `cpu/layout.rs:56-111`): slot
`l < 25` of step `x` is input lane `l` of row `x`, slot `25 + l` lane `l` of its state after
twelve rounds, and slot `50 + k` the row's cell of the `KECCAK` column `spareColumn k`. -/
def keccakWitness (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Vector K (2 ^ (s.τ 5 + 6)) :=
  Vector.ofFn fun i ↦
    if h : i.val / 2 ^ s.τ 5 < 25 then inLaneOf prog s w (i.val % 2 ^ s.τ 5) ⟨_, h⟩
    else if h' : i.val / 2 ^ s.τ 5 < 50 then
      stateLanes (keccakSegment 0 (laneState (inLaneOf prog s w (i.val % 2 ^ s.τ 5))))
        ⟨i.val / 2 ^ s.τ 5 - 25, by omega⟩
    else cellOf (tableAt w 5) (i.val % 2 ^ s.τ 5) (spareColumn (i.val / 2 ^ s.τ 5 - 50))

/-- The column `c` a witness carries: the memory and bytecode blocks' committed cells,
`QKECCAK` of the `KECCAK` rows, the opcode tables' cells. -/
def witnessColumn (w : EnsembleWitness (leanIsaEnsemble prog κ)) :
    (c : Col) → Vector K (2 ^ kappa prog s c)
  | ⟨⟨0, _⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 6) x (memRowCell i)
  | ⟨⟨1, _⟩, _⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w 7) x 1
  | ⟨⟨2, _⟩, _⟩ => keccakWitness prog s w
  | ⟨⟨j + 3, h⟩, i⟩ => Vector.ofFn fun x ↦ cellOf (tableAt w ⟨j, by omega⟩) x i

/-- The stack of a witness at the sizes `s`: its committed columns at their blocks, zero past
the last. -/
def stackOf (w : EnsembleWitness (leanIsaEnsemble prog κ)) : Column (leanIsaμ prog s) :=
  (blocks prog s).stackColumn (fun b ↦ witnessColumn prog s w (stackOrder prog s)[b])
    (leanIsaμ prog s)

end StackOf

end LeanIsa

/-! ## The bus phase's conditions -/

namespace LeanIsa

/-- Summing over a list with repetitions. -/
private theorem sum_flatMap_replicate {α : Type} (l : List α) (a : α → ℕ) (f : α → ℕ)
    (g : ℕ → ℕ) :
    ((l.flatMap fun x ↦ List.replicate (a x) (f x)).map g).sum =
      (l.map fun x ↦ a x * g (f x)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_replicate,
      List.sum_replicate, smul_eq_mul, List.map_cons, List.sum_cons]

/-- Every table has at most as many count columns as push flushes. -/
theorem counts_le_pushes : ∀ j : Fin 9,
    (counts j).length ≤ ((flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

/-- A table with a constraint has a push flush. -/
theorem constrained_pushes : ∀ j : Fin 9, 0 < (LeanIsa.constraints j).length →
    0 < ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length := by
  decide +kernel

variable (prog : LeanIsaProgram) (s : Sizes)

/-- A side's leaf count, from its blocks' log-heights. -/
private theorem leafCount_eq (I : M3Instance) (k : Fin 3) :
    Bus.leafCount I k = (((Bus.sources I k).map Bus.Source.κ).map (2 ^ ·)).sum := by
  rw [Bus.leafCount, List.map_map]
  rfl

/-- The leaves of the push side, by table. -/
private theorem leafCount_push :
    Bus.leafCount (leanIsaInstance prog s) 0 =
      (((boundary prog s).filter fun b ↦ decide (b.side = .push)).map fun b ↦ 2 ^ b.κ).sum +
      ((List.finRange 9).map fun j ↦
        ((LeanIsa.flushes j).filter fun f ↦ decide (f.1 = Side.push)).length *
          2 ^ height prog s j).sum := by
  rw [leafCount_eq]
  change ((((Bus.sideSources _ .push).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  rfl

/-- The pull side has as many leaves as the push side: a table pulls as often as it pushes, and the
boundary blocks pair up. -/
private theorem leafCount_pull :
    Bus.leafCount (leanIsaInstance prog s) 1 = Bus.leafCount (leanIsaInstance prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.sideSources _ .pull).map Bus.Source.κ).map (2 ^ ·))).sum = _
  rw [Bus.sideSources_map_κ, List.map_append, List.sum_append, sum_flatMap_replicate,
    List.map_map]
  congr 1

/-- The count side has at most as many leaves as the push side. -/
private theorem leafCount_count_le :
    Bus.leafCount (leanIsaInstance prog s) 2 ≤ Bus.leafCount (leanIsaInstance prog s) 0 := by
  rw [leafCount_push, leafCount_eq]
  change ((((Bus.countSources _).map Bus.Source.κ).map (2 ^ ·))).sum ≤ _
  rw [Bus.countSources_map_κ, sum_flatMap_replicate]
  refine le_add_left (List.sum_le_sum fun j _ ↦ ?_)
  exact Nat.mul_le_mul_right _ (counts_le_pushes j)

/-- Every flush's first coordinate is its channel's separator, a constant. -/
theorem flushes_separator : ∀ j : Fin 9, ∀ g ∈ LeanIsa.flushes j, ∀ r r' : Fin (width j) → K,
    (g.2[0]).eval r = (g.2[0]).eval r'
  | ⟨0, _⟩ => by simp [LeanIsa.flushes]
  | ⟨1, _⟩ => by simp [LeanIsa.flushes]
  | ⟨2, _⟩ => by simp [LeanIsa.flushes]
  | ⟨j + 3, h⟩ => by
    intro g hg r r'
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact toM3_separator _ _ _ _ hg' r r'

/-- The leanISA instance meets the bus phase's side conditions, at every size. -/
theorem leanIsa_conditions : Bus.Conditions (leanIsaInstance prog s) where
  one_le_d := by norm_num
  constrained j hj := by
    have hfit : Bus.leafCount (leanIsaInstance prog s) 0 ≤ 2 ^ (leanIsaInstance prog s).μBus :=
      (Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _)
    have hpos := constrained_pushes j (List.length_pos_iff.mpr hj)
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (le_trans ?_ hfit)
    rw [leafCount_push]
    refine le_add_left ((Nat.le_mul_of_pos_left _ hpos).trans ?_)
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  pull_fits := by
    rw [leafCount_pull, ← Bus.blocks_total]
    exact Bus.push_fits _
  count_fits := (leafCount_count_le prog s).trans
    ((Bus.blocks_total _ 0).symm.trans_le (Bus.push_fits _))
  separator j f r r' := flushes_separator j _ (List.getElem_mem f.isLt) r r'

end LeanIsa

end
end LeanVM.Protocol
