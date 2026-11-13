import LeanVM.Arithmetization.Completeness.Basics
import LeanVM.Arithmetization.Completeness.Satisfied

/-!
# Tests: the constraint statement

A classic test for kernel evaluation: the fixture decides `K` and `E` arithmetic, one
Keccak-f[1600] permutation, and the bus permutations in the kernel.

**The fixture** is one hand-built witness of `SatisfiedBy` for the program of the execution
tests, the executor's `mul_128bit_word` (`crates/leanvm_core/src/cpu/mod.rs:888-903` at leanVM
`4af2cddd`, `tests/LeanVMTests/Semantics/Execution.lean`), extended with closed walks: a `JUMP` to
the sentinel after the three instructions, and three blocks run in frames disjoint from the
program's own, each a loop ending in a `JUMP` back to its first instruction: one `XOR`, one
`DEREF`, one `KECCAK`. The `KECCAK` row is the first permutation of the executor test
`keccak_permutes_in_both_layouts` (`cpu/mod.rs:842-875` at leanVM `4af2cddd`): the input cells
`a, b, a, b` (the two `m` pairs aliasing one another), the padding's first byte `0x01` in the
tail's first cell, `b8 = (0x8000000000000000, 0x5555, 0)` whose high limb holds no lane in the
even layout (the row's free limb), a zero capacity, and the thirteen output cells in the odd
layout, the output lanes the pinned verifier's `keccak_f` computes
(`crates/verifier/src/hash.rs:50-69`, computed outside Lean, as in the table and execution tests).
The statement accepts rows that are not steps of the run as long as the state pair balances (Prop.
6.1: one walk from the initial to the final registers, and closed walks), and the fixture exercises
that. The thirty-two-slot program `walkProg` runs four steps from `(1, 1)` to `(g^31, 1)`
(`walk_run`, a `ValidExecution`), and its honest witness `walkW kLout 1 g memCnt` at the memory
size `2^16` satisfies every conjunct of
`SatisfiedBy` (`walk_satisfiedBy`) and represents the trace (`walk_represents`): the completeness
instance for this program, by hand (`walk_t1_instance`). The witness is parametric in the
`KECCAK` row's output lanes (written consistently in the row and in the image), the first
`SET_CONSTANT` row's read count, the product row's read count of `x`, and the memory block's
finalize counts, so that the rejections below are the honest witness with one thing changed.

**What the proofs exercise.** The eight tables are the witness's `tables` in the ensemble's
order, the memory block's `2^16` rows built by `List.ofFn` and never enumerated: its constraints
hold row-generically (the block has none), its interactions on a foreign channel are `[]` by a
lemma (`memT_filter`), and its share of the memory pair is split (`List.ofFn_add`) into the
forty-four cells the run touches, decided in the kernel with the tables' reads, and the
untouched suffix, whose seed and finalize messages coincide because its finalize counts are `1`
(`memCnt_of_ge`). The kernel evaluates a table's interactions through Clean's
`Component.rowOperations` (`table_interactions_eq`), since `Component.operations` reaches them
through `instantiate` and `toSubcircuit`, which the kernel does not unfold. The `KECCAK` table's
and the bytecode block's sends, the costliest, are first put in the closed form of
`keccak_sends_gen` and `bytecode_sends_gen` (`keccak_sends_closed`, `bytecode_sends_closed`), so
that each decision reads them off the rows' fields instead of evaluating the row and the circuit
again. `KeccakRowsValid` is one kernel evaluation of Keccak-f[1600] (`keccak_lanes`).

**Rejections**, each the honest witness with one thing changed, are `StatementRejections.lean`.
-/

-- The kernel decisions one at a time: elaborated in parallel, the fixture's bus permutations and
-- its Keccak-f[1600] evaluation reserve more than a 40 GB address-space cap (about 41 GB, against
-- about 20 GB in sequence, at the same wall time).
set_option Elab.async false

namespace LeanVMTests.Arithmetization.Statement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component EnsembleWitness)

/-! ## The fixture: `mul_128bit_word` with closed walks -/

-- The operands and product of the executor test `mul_128bit_word` (`cpu/mod.rs:853-869` at
-- `leanvm-rev`).
def mulX : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef)
def mulY : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0x1b4ac62c35ac2ecc) (K.ofBits 0x421e3037aaa197d0)

-- The executor test `keccak_permutes_in_both_layouts` at leanVM 4af2cddd, its first permutation
-- (as in `tests/LeanVMTests/Arithmetization/Tables.lean` and `Semantics/Execution.lean`): the
-- input cells, the words `a, b` (each read twice through the aliased `m` pairs), the padding's
-- first byte in the tail, its last bit in `b8` (whose free high limb `0x5555` holds no lane), and
-- a zero capacity; the input lanes they hold in the even layout, and their image under `keccak_f`
-- (`hash.rs:50-69`, computed outside Lean).
def kA : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210)
def kB : E := E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d)
def kPad : E := E.ofLimbs (K.ofBits 0x01) 0
def kEnd : E := E.ofLimbs (K.ofBits 0x8000000000000000) (K.ofBits 0x5555)

def kLin : Vector K 25 :=
  #v[K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210, K.ofBits 0xdeadbeefcafebabe,
    K.ofBits 0xbadf00d0badf00d, K.ofBits 0x123456789abcdef, K.ofBits 0xfedcba9876543210,
    K.ofBits 0xdeadbeefcafebabe, K.ofBits 0xbadf00d0badf00d, K.ofBits 0x1, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x8000000000000000, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0,
    K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0, K.ofBits 0x0]

def kLout : Vector K 25 :=
  #v[K.ofBits 0x8dbfafed17b66d45, K.ofBits 0x30fd63be3bf8b935, K.ofBits 0x77167d7a851a2a5a,
    K.ofBits 0xd9174937e0d9005e, K.ofBits 0xa6a08643e0752e62, K.ofBits 0x96fa9d5eb49e3867,
    K.ofBits 0xd3075d1a22781d5, K.ofBits 0x81ae728bf7328686, K.ofBits 0xf51da81b6f1b6499,
    K.ofBits 0xdaf2a8af5b43dbf9, K.ofBits 0xdbf85b3cc1312641, K.ofBits 0x993d35c56291827e,
    K.ofBits 0x47fd59ac60e225e2, K.ofBits 0x36607d1d9e6abed, K.ofBits 0x6cee5561314ca0f3,
    K.ofBits 0x3e20ee955c09012e, K.ofBits 0x8a928dc9e22c3dcf, K.ofBits 0x7f24a1dac6837929,
    K.ofBits 0xd22b33eacce5fcd2, K.ofBits 0x2b1e71fdcd52b881, K.ofBits 0x427618061608ac91,
    K.ofBits 0x44c480aa40bfdbf9, K.ofBits 0x7a29ee993739ddb0, K.ofBits 0xf7f9aa87f90247d1,
    K.ofBits 0xe5177d767bf6bd92]

/-- The thirteen output cells of the lanes `L` in the odd layout: lane `0` alone in the high limb
of cell `0`, then the lane pairs `(2c - 1, 2c)`. At `kLout` they are the executor's (`kOut` of
the execution tests). -/
def outCells (L : Vector K 25) : List E :=
  [E.ofLimbs 0 L[0], E.ofLimbs L[1] L[2], E.ofLimbs L[3] L[4], E.ofLimbs L[5] L[6],
    E.ofLimbs L[7] L[8], E.ofLimbs L[9] L[10], E.ofLimbs L[11] L[12],
    E.ofLimbs L[13] L[14], E.ofLimbs L[15] L[16], E.ofLimbs L[17] L[18],
    E.ofLimbs L[19] L[20], E.ofLimbs L[21] L[22], E.ofLimbs L[23] L[24]]

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- A word of `K` as a cell. -/
def cellK (a : K) : E := E.ofLimbs a 0

/-- The program: the executor's three instructions in frame `1` (slots `0..2`), a `JUMP` to the
sentinel (`3`), an `XOR` loop in frame `g^5` (`4`, `5`), a `DEREF` loop in the same frame
(`6`, `7`), a `KECCAK` loop of one row in frame `g^14` (`8`, `9`), never-executed slots
(`10..30`) and the sentinel (`31`, not a `JUMP`). Each block's `JUMP` reads `c = 1`, its
block's first counter `d`, and its own frame `f`. The `KECCAK` operands are the executor
test's layout moved into the frame: `m = [0, 1, 0, 1]`, `tail = 2`, `b8 = 6`, `cap = 7`,
`out = 11`, even layout in, odd layout out. -/
def walkProg : LeanIsaProgram :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (addressOfIndex 2) mulX
    | 1 => .setConstant (addressOfIndex 3) mulY
    | 2 => .mulNative (addressOfIndex 2) (addressOfIndex 3) (addressOfIndex 4)
    | 3 => .jump (addressOfIndex 41) (addressOfIndex 42) (addressOfIndex 43)
    | 4 => .xor 1 1 1
    | 5 => .jump g (addressOfIndex 2) (addressOfIndex 6)
    | 6 => .deref (addressOfIndex 6) 1 1 .cell
    | 7 => .jump g (addressOfIndex 3) (addressOfIndex 6)
    | 8 => .keccak ![1, g, 1, g] (addressOfIndex 2) (addressOfIndex 6) (addressOfIndex 7) (addressOfIndex 11) false true
        .all
    | 9 => .jump (addressOfIndex 24) (addressOfIndex 25) (addressOfIndex 26)
    | _ => .xor 1 1 1⟩

/-- The forty-four cells the run and the loops touch, by index, the `KECCAK` output cells holding
the lanes `L`; every other cell of the image is `0`. Frame `1`: the public words (`0`, `1`), the
operands and the product (`2..4`), the sentinel `JUMP`'s `c, d, f` (`41..43`). Frame `g^5`: the
`XOR` and `DEREF` cell (`5`), `c` (`6`), the two blocks' `d` (`7`, `8`), the pointer and `f`
(`11`). Frame `g^14`: the `KECCAK` cells in the executor's layout, `a, b` (`14`, `15`), the tail
(`16..19`), `b8` (`20`), the capacity (`21..24`), the output (`25..37`), and the block's
`c, d, f` (`38..40`). -/
def walkCells (L : Vector K 25) : Array E :=
  ([cellK 1, cellK (K.ofBits 2), mulX, mulY, mulXY,
    0, cellK 1, cellK (addressOfIndex 4), cellK (addressOfIndex 6), 0, 0, cellK (addressOfIndex
        5), 0, 0,
    kA, kB, kPad, 0, 0, 0, kEnd, 0, 0, 0, 0] ++ outCells L ++
    [cellK 1, cellK (addressOfIndex 8), cellK (addressOfIndex 14), cellK 1, cellK (addressOfIndex
        31), cellK 1]).toArray

/-- The image, of `2^16` cells. -/
def walkImage (L : Vector K 25) : MemoryImage 16 := fun i ↦ ((walkCells L)[(i : ℕ)]?).getD 0

/-- The trace: four steps, over the honest image. -/
def walkTrace : Execution walkProg := ⟨16, walkImage kLout, 4⟩

/-- The honest finalize counts `g^A[i]` of the touched cells; `1` elsewhere (`memCnt`). The
`KECCAK` row reads `a` and `b` twice, every other cell of its frame once. -/
def walkCounts : Array K :=
  #[1, 1, g ^ 2, g ^ 2, g, g ^ 5, g ^ 2, g, g, 1, 1, g ^ 3, 1, 1,
    g ^ 2, g ^ 2, g, g, g, g, g, g, g, g, g,
    g, g, g, g, g, g, g, g, g, g, g, g, g,
    g, g, g, g, g, g]

/-- The finalize count of cell `i`. -/
def memCnt (i : ℕ) : K := (walkCounts[i]?).getD 1

/-- Past the touched cells every finalize count is `1`: the cell was never read. -/
theorem memCnt_of_ge {i : ℕ} (h : 44 ≤ i) : memCnt i = 1 := by
  have hs : walkCounts.size = 44 := rfl
  unfold memCnt
  rw [Array.getElem?_eq_none (hs ▸ h)]
  rfl

/-- The finalize count of slot `i`: every slot up to `9` executes once. -/
def bcCnt (i : ℕ) : K := if i ≤ 9 then g else 1

/-- The same, as the bytecode block's finalize-count column. -/
def bcCntFin (i : Fin (2 ^ walkProg.logSize)) : K := bcCnt i

/-! ## The rows -/

-- Frame `1`: the run.
/-- Slot `0`, `SET_CONSTANT g^2 ← x`, with read count `c` (`1` for the honest prover). -/
def setRow0 (c : K) : SetRow K :=
  ⟨addressOfIndex 0, 1, addressOfIndex 2, #v[mulX.limb 0, mulX.limb 1], c, 1⟩
/-- Slot `1`, `SET_CONSTANT g^3 ← y`. -/
def setRow1 : SetRow K := ⟨addressOfIndex 1, 1, addressOfIndex 3, #v[mulY.limb 0, mulY.limb 1], 1, 1⟩
/-- Slot `2`, `MUL_NATIVE`: the read of `x` with count `rA` (`g` for the honest prover, the
second read), the second read of `y`, the first of the product. -/
def mulRow (rA : K) : MulRow K :=
  ⟨addressOfIndex 2, 1, addressOfIndex 2, addressOfIndex 3, addressOfIndex 4, #v[mulX.limb 0,
      mulX.limb 1],
    #v[mulY.limb 0, mulY.limb 1], rA, g, 1, 1⟩
/-- Slot `3`, the `JUMP` to the sentinel: `(g^3, 1) → (g^31, 1)`. -/
def jumpRow3 : JumpRow K := ⟨addressOfIndex 3, 1, addressOfIndex 41, addressOfIndex 42,
    addressOfIndex 43, 1, addressOfIndex 31, 1, 1, 1, 1, 1⟩

-- Frame `g^5`: the `XOR` and `DEREF` blocks.
/-- Slot `4`, `XOR 1 1 1` on the zero cell `g^5`: three reads. -/
def xorRow : XorRow K := ⟨addressOfIndex 4, addressOfIndex 5, 1, 1, 1, #v[0, 0], #v[0, 0], 1,
    g, g ^ 2, 1⟩
/-- Slot `5`, the `JUMP` back to slot `4`. -/
def jumpRow5 : JumpRow K := ⟨addressOfIndex 5, addressOfIndex 5, g, addressOfIndex 2, addressOfIndex
    6, 1, addressOfIndex 4, addressOfIndex 5, 1, 1, 1, 1⟩
/-- Slot `6`, `DEREF` in `cell` mode: the pointer `g^5` at `g^11`, the local and target cell
both `g^5` (its fourth and fifth reads). -/
def derefRow : DerefRow K :=
  ⟨addressOfIndex 6, addressOfIndex 5, addressOfIndex 6, 1, 1, 0, 0, addressOfIndex 5, #v[0, 0],
      g, g ^ 4, g ^ 3, 1⟩
/-- Slot `7`, the `JUMP` back to slot `6`. -/
def jumpRow7 : JumpRow K := ⟨addressOfIndex 7, addressOfIndex 5, g, addressOfIndex 3, addressOfIndex
    6, 1, addressOfIndex 6, addressOfIndex 5, g, 1, g ^ 2, 1⟩

-- Frame `g^14`: the `KECCAK` block.
/-- The `KECCAK` row's read counts: the first reads of `a, b`, their second reads (the aliased
`m` pairs), then the first read of every other cell. -/
def kCnt : Vector K 26 :=
  #v[1, 1, g, g, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
/-- Slot `8`, the executor's `KECCAK` row in frame `g^14`, with output lanes `L` (`kLout` for the
honest prover): even layout in (flag `0`), odd layout out (flag `1`), all thirteen output cells
written (flags `1, 1`), the free limb `0x5555`. -/
def kRow (L : Vector K 25) : KeccakRow K :=
  ⟨addressOfIndex 8, addressOfIndex 14, #v[1, g, 1, g], addressOfIndex 2, addressOfIndex 6,
      addressOfIndex 7, addressOfIndex 11, 0, 1, 1, 1, K.ofBits 0x5555, kLin,
    L, kCnt, 1⟩
/-- Slot `9`, the `JUMP` back to slot `8`. -/
def jumpRow9 : JumpRow K :=
  ⟨addressOfIndex 9, addressOfIndex 14, addressOfIndex 24, addressOfIndex 25, addressOfIndex 26, 1,
      addressOfIndex 8, addressOfIndex 14, 1, 1, 1, 1⟩

/-- The `JUMP` rows as raw rows `jumpRaw r 1 1`, their two local witnesses `w = 1`, `b = 1`
(every condition is `1`), have the table's width. -/
theorem jumpRaws_size (rs : List (JumpRow K)) :
    ∀ r ∈ rs.map (jumpRaw · 1 1), r.size = size JumpRow + 2 := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  rw [jumpRaw, Array.size_append, rawRow_size]
  rfl

/-- Row `i` of the memory block: `(mem[i], g^i, cnt i)`, the raw form of the typed row
(`memRowOf`: the limbs first, as the committed columns). -/
def memRowArr (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ 16)) : Array K :=
  rawRow (memRowOf (walkImage L) i (cnt i))

/-- The memory row's four cells, without evaluating the block's row list. -/
theorem memRowArr_eq (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ 16)) :
    memRowArr L cnt i =
      #[(walkImage L i).limb 0, (walkImage L i).limb 1, addressOfIndex i, cnt i] := by
  with_unfolding_all rfl

/-- The memory block's rows, with any finalize counts, agree with its fixed index column: the
block is preallocated, `2^16` rows, row `i` at `g^i`. -/
theorem memRows_fixed (L : Vector K 25) (cnt : ℕ → K) :
    (memComponent 16).FixedRowsMatch (List.ofFn (memRowArr L cnt)) := by
  show (List.ofFn (memRowArr L cnt)).length = (UInt64.ofNat (2 ^ 16)).toNat ∧
    ∀ i (hi : i < (List.ofFn (memRowArr L cnt)).length), (memMode 16).FixedAt
      (UInt64.ofNat i) (fromElements (Air.Flat.rowPrefix (size MemRow)
        (List.ofFn (memRowArr L cnt))[i]))
  have h64 : 2 ^ 16 < 2 ^ 64 := by decide
  refine ⟨by rw [List.length_ofFn, UInt64.toNat_ofNat_of_lt' h64], fun i hi ↦ ?_⟩
  have hi' : i < 2 ^ 16 := by rwa [List.length_ofFn] at hi
  have hnat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (lt_trans hi' h64)
  refine (memMode_fixedAt (by rw [hnat]; exact hi') _).mpr ?_
  rw [List.getElem_ofFn, memRowArr, fromElements_rowPrefix_rawRow, hnat]
  rfl

/-- The bytecode block's rows: the program's (`bytecodeRowOf`), with the honest counts. -/
def bcRows : List (Array K) :=
  List.ofFn fun i ↦ rawRow (bytecodeRowOf walkProg i (bcCntFin i))

/-- They agree with the block's fixed counter and entry columns. -/
theorem bcRows_fixed : (bytecodeComponent walkProg).FixedRowsMatch bcRows := by
  show bcRows.length = (UInt64.ofNat (2 ^ walkProg.logSize)).toNat ∧
    ∀ i (hi : i < bcRows.length), (bytecodeMode walkProg).FixedAt (UInt64.ofNat i)
      (fromElements (Air.Flat.rowPrefix (size BytecodeRow) bcRows[i]))
  have h64 : 2 ^ walkProg.logSize < 2 ^ 64 := by decide
  refine ⟨by rw [bcRows, List.length_ofFn, UInt64.toNat_ofNat_of_lt' h64], fun i hi ↦ ?_⟩
  have hi' : i < 2 ^ walkProg.logSize := by rwa [bcRows, List.length_ofFn] at hi
  have hnat : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (lt_trans hi' h64)
  refine (bytecodeMode_fixedAt walkProg (by rw [hnat]; exact hi') _).mpr ?_
  have e : bcRows[i]'hi = rawRow (bytecodeRowOf walkProg ⟨i, hi'⟩ (bcCntFin ⟨i, hi'⟩)) := by
    simp only [bcRows, List.getElem_ofFn]
  rw [e, fromElements_rowPrefix_rawRow]
  congr 1
  exact Fin.ext hnat.symm

/-! ## The tables and the witness -/

/-- An opcode table holding the raw rows `rows`, its prover data its own (`ownTable`): the
witness replaces it by Clean's derived data. Its rows are made by demand, so no fixed cell. -/
def opT {Row : TypeMap} [ProvableType Row] (c : GeneralFormalCircuit K Row Registers)
    (rows : List (Array K)) (hw : ∀ r ∈ rows, r.size = (opcodeComponent c).width)
    (hlen : rows.length ≤ UInt64.size := by
      simp only [List.length_map, List.length_cons, List.length_nil]; decide) : Air.Flat.Table K :=
  ownTable (opcodeComponent c) rows hw hlen trivial

def xorT : Air.Flat.Table K := opT xorTable ([xorRow].map rawRow) (rawRows_size [xorRow])
/-- The `MUL_NATIVE` table, its row's read count of `x` `rA`. -/
def mulT (rA : K) : Air.Flat.Table K := opT mulTable ([mulRow rA].map rawRow) (rawRows_size [mulRow rA])
/-- The `SET_CONSTANT` table, its first row's read count `c`. -/
def setT (c : K) : Air.Flat.Table K :=
  opT setTable ([setRow0 c, setRow1].map rawRow) (rawRows_size [setRow0 c, setRow1])
def derefT : Air.Flat.Table K := opT derefTable ([derefRow].map rawRow) (rawRows_size [derefRow])
def jumpT : Air.Flat.Table K :=
  opT jumpTable ([jumpRow3, jumpRow5, jumpRow7, jumpRow9].map (jumpRaw · 1 1))
    (jumpRaws_size [jumpRow3, jumpRow5, jumpRow7, jumpRow9])
/-- The `KECCAK` table: the one row, its output lanes `L`. -/
def kT (L : Vector K 25) : Air.Flat.Table K :=
  opT keccakTable ([kRow L].map rawRow) (rawRows_size [kRow L])
/-- The memory block, with finalize counts `cnt`. -/
def memT (L : Vector K 25) (cnt : ℕ → K) : Air.Flat.Table K :=
  ownTable (memComponent 16) (List.ofFn (memRowArr L cnt))
    (by
      intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)
    (by rw [List.length_ofFn]; decide) (memRows_fixed L cnt)
/-- The bytecode block: the program's rows. -/
def bcT : Air.Flat.Table K :=
  ownTable (bytecodeComponent walkProg) bcRows
    (by
      intro r hr
      rw [bcRows, List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)
    (by rw [bcRows, List.length_ofFn]; decide) bcRows_fixed

/-- A witness whose tables are `ts`, eight tables of the ensemble's components in order, with the
prover data Clean derives from them (`withDerivedData`) and the public input `mulInput`. -/
theorem mkW_names (ts : List (Air.Flat.Table K))
    (hc : ts.map (·.component) = (leanIsaEnsemble walkProg 16).tables) :
    (ts.map fun t ↦ t.component.circuit.name).Nodup := by
  have h := (leanIsaEnsemble walkProg 16).unique_names
  rw [← hc, List.map_map] at h
  exact h

theorem mkW_components (ts : List (Air.Flat.Table K))
    (hc : ts.map (·.component) = (leanIsaEnsemble walkProg 16).tables) :
    (Air.Flat.withDerivedData ts (mkW_names ts hc)).map (·.component) =
      (leanIsaEnsemble walkProg 16).tables := by
  rw [Air.Flat.withDerivedData_map_component, hc]

def mkW (ts : List (Air.Flat.Table K))
    (hc : ts.map (·.component) = (leanIsaEnsemble walkProg 16).tables := by rfl) :
    EnsembleWitness (leanIsaEnsemble walkProg 16) where
  tables := Air.Flat.withDerivedData ts (mkW_names ts hc)
  publicInput := PublicIO.ofInput mulInput
  same_length := by simp only [← mkW_components ts hc, List.length_map]
  same_circuits := by
    intro i hi
    simp only [List.getElem_of_eq (mkW_components ts hc).symm hi, List.getElem_map]
  same_data := Air.Flat.withDerivedData_data _ _

/-- The witness, with the `KECCAK` row's output lanes `L` (in the row and in the image), the
first `SET_CONSTANT` row's read count `c`, the product row's read count of `x` `rA`, and the
memory block's finalize counts `cnt`; the honest one is `walkW kLout 1 g memCnt`. -/
def walkW (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    EnsembleWitness (leanIsaEnsemble walkProg 16) :=
  mkW [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT]

/-! ## The tables of the witness, read back -/

/-- The witness's tables are `ts` but for their data. -/
theorem mkW_map (ts : List (Air.Flat.Table K)) (hc) :
    (mkW ts hc).tables.map (fun t ↦ (t.component, t.table)) =
      ts.map (fun t ↦ (t.component, t.table)) :=
  Air.Flat.withDerivedData_map _ (mkW_names ts hc)

/-- A function of the components and rows, summed over the witness's tables, is summed over
`ts`. -/
theorem mkW_flatMap (ts : List (Air.Flat.Table K)) (hc) {α : Type}
    (F : Component K → List (Array K) → List α) :
    (mkW ts hc).tables.flatMap (fun t ↦ F t.component t.table) =
      ts.flatMap (fun t ↦ F t.component t.table) := by
  calc _ = ((mkW ts hc).tables.map fun t ↦ (t.component, t.table)).flatMap
          (fun p ↦ F p.1 p.2) := by rw [List.flatMap_map]
    _ = _ := by rw [mkW_map, List.flatMap_map]

/-- A table of the witness has the component and the rows of one of `ts`. -/
theorem mem_mkW {ts : List (Air.Flat.Table K)} {hc} {t : Air.Flat.Table K}
    (ht : t ∈ (mkW ts hc).tables) : ∃ t₀ ∈ ts, t.component = t₀.component ∧ t.table = t₀.table := by
  have hm : (t.component, t.table) ∈ (mkW ts hc).tables.map fun t ↦ (t.component, t.table) :=
    List.mem_map_of_mem (f := fun t : Air.Flat.Table K ↦ (t.component, t.table)) ht
  rw [mkW_map, List.mem_map] at hm
  obtain ⟨t₀, ht₀, he⟩ := hm
  exact ⟨t₀, ht₀, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- The same among the first six tables. -/
theorem mem_mkW_take {ts : List (Air.Flat.Table K)} {hc} {t : Air.Flat.Table K}
    (ht : t ∈ (mkW ts hc).tables.take 6) :
    ∃ t₀ ∈ ts.take 6, t.component = t₀.component ∧ t.table = t₀.table := by
  have hm : (t.component, t.table) ∈ ((mkW ts hc).tables.take 6).map
      fun t ↦ (t.component, t.table) :=
    List.mem_map_of_mem (f := fun t : Air.Flat.Table K ↦ (t.component, t.table)) ht
  rw [List.map_take, mkW_map, ← List.map_take, List.mem_map] at hm
  obtain ⟨t₀, ht₀, he⟩ := hm
  exact ⟨t₀, ht₀, (congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩

/-- The rows of the witness's table `j` are those of `ts[j]`. -/
theorem mkW_tableAt (ts : List (Air.Flat.Table K)) (hc) (j : Fin 8) (hj : (j : ℕ) < ts.length) :
    (tableAt (mkW ts hc) j).table = ts[(j : ℕ)].table := by
  have hj' : (j : ℕ) < ((mkW ts hc).tables.map fun t ↦ (t.component, t.table)).length := by
    rw [List.length_map, ← (mkW ts hc).same_length]; exact j.isLt
  have e := List.getElem_of_eq (mkW_map ts hc) hj'
  rw [List.getElem_map, List.getElem_map] at e
  exact congrArg Prod.snd e

/-- The three blocks the statement names, read off the witness. By `dsimp`, never by `rfl`: a
definitional comparison of a stuck projection against a `List.ofFn` unrolls the `2^16` rows. -/
theorem walk_table5 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (tableAt (walkW L c rA cnt) 5).table = [kRow L].map rawRow :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 5 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, kT, opT, ownTable])
theorem walk_table6 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    memBlockRows (walkW L c rA cnt) = List.ofFn (memRowArr L cnt) :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 6 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, memT, ownTable])
theorem walk_table7 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    bytecodeBlockRows (walkW L c rA cnt) = bcRows :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 7 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, bcT, ownTable])

/-! ## The image the data names

Clean derives the `"mem"` table from the memory block (`memRows_data`): its rows cut at three
cells, the limbs. -/

/-- The `"mem"` table of the witness's data is the image's. -/
theorem walk_memRows (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    memRows (walkW L c rA cnt).data = imageRows (walkImage L) := by
  rw [memRows_data, walk_table6, List.map_ofFn, imageRows, List.toArray_ofFn]
  congr 1
  funext i
  exact rowPrefix_two_rawRow (walkW L c rA cnt) _

/-- The image the data names, as one equality of dependent pairs. -/
theorem walk_imageOf (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    imageOf (walkW L c rA cnt).data = ⟨16, walkImage L⟩ :=
  imageOf_of_memRows (walk_memRows L c rA cnt) (by decide)

/-! ## The run -/

/-- The instruction at `g^i`. -/
theorem fetch_at (i : ℕ) (ins : LeanIsaInstruction) (hi : i < 2 ^ walkProg.logSize := by decide)
    (hd : walkProg.instructions ⟨i, hi⟩ = ins :=
        by rfl) : walkProg.fetch (addressOfIndex i) = some ins := by
  rw [show addressOfIndex i = addressOfIndex ((⟨i, hi⟩ : Fin (2 ^ walkProg.logSize)) : ℕ) from rfl,
    LeanIsaProgram.fetch_gpow, hd]

/-- The instruction at the counter `1 = g^0`. -/
theorem fetch_one : walkProg.fetch 1 = some (.setConstant (addressOfIndex 2) mulX) := by
  simpa using fetch_at 0 (.setConstant (addressOfIndex 2) mulX)

/-- The word at `g^k`. -/
theorem read_at (L : Vector K 25) (k : ℕ) (v : E) (hk : k < 2 ^ 16 := by decide)
    (hv : walkImage L ⟨k, hk⟩ = v := by rfl) : (walkImage L).read (addressOfIndex k) = some v := by
  rw [show addressOfIndex k = addressOfIndex ((⟨k, hk⟩ : Fin (2 ^ 16)) : ℕ) from rfl,
    MemoryImage.read_gpow (by decide), hv]

theorem walk_step0 : step walkProg (walkImage kLout) ⟨1, 1⟩ = some ⟨addressOfIndex 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) fetch_one]
  show execute (walkImage kLout) ⟨1, 1⟩ (.setConstant (addressOfIndex 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_at kLout 2 mulX]
  decide +kernel

theorem walk_step1 : step walkProg (walkImage kLout) ⟨addressOfIndex 1, 1⟩ = some ⟨addressOfIndex 2,
    1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 1, 1⟩) (fetch_at 1 (.setConstant (addressOfIndex
      3) mulY))]
  show execute (walkImage kLout) ⟨addressOfIndex 1, 1⟩ (.setConstant (addressOfIndex 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_at kLout 3 mulY]
  decide +kernel

theorem walk_step2 : step walkProg (walkImage kLout) ⟨addressOfIndex 2, 1⟩ = some ⟨addressOfIndex 3,
    1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 2, 1⟩) (fetch_at 2 (.mulNative (addressOfIndex 2)
      (addressOfIndex 3) (addressOfIndex 4)))]
  show execute (walkImage kLout) ⟨addressOfIndex 2, 1⟩ (.mulNative (addressOfIndex 2)
      (addressOfIndex 3) (addressOfIndex 4)) = _
  simp only [execute, executeWith, one_mul, read_at kLout 2 mulX, read_at kLout 3 mulY,
    read_at kLout 4 mulXY]
  decide +kernel

theorem walk_step3 : step walkProg (walkImage kLout) ⟨addressOfIndex 3, 1⟩ = some ⟨addressOfIndex
    31, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨addressOfIndex 3, 1⟩) (fetch_at 3 (.jump (addressOfIndex 41)
      (addressOfIndex 42) (addressOfIndex 43)))]
  show execute (walkImage kLout) ⟨addressOfIndex 3, 1⟩ (.jump (addressOfIndex 41) (addressOfIndex
      42) (addressOfIndex 43)) = _
  simp only [execute, executeWith, one_mul, read_at kLout 41 (cellK 1),
    read_at kLout 42 (cellK (addressOfIndex 31)), read_at kLout 43 (cellK 1)]
  decide +kernel

theorem walk_run1 : run walkProg (walkImage kLout) 1 ⟨1, 1⟩ = some ⟨addressOfIndex 1, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, Option.bind_eq_bind,
    Option.bind_some, run_zero]

theorem walk_run2 : run walkProg (walkImage kLout) 2 ⟨1, 1⟩ = some ⟨addressOfIndex 2, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run3 : run walkProg (walkImage kLout) 3 ⟨1, 1⟩ = some ⟨addressOfIndex 3, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run4 : run walkProg (walkImage kLout) 4 ⟨1, 1⟩ = some ⟨addressOfIndex 31, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    walk_step3, Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The run: four steps from `(1, 1)` to the final registers `(g^31, 1)`. -/
theorem walk_run : run walkProg (walkImage kLout) 4 Registers.initial = some (Registers.final walkProg) :=
  walk_run4

/-- The public words are in place. -/
theorem walk_boundary : HoldsPublicInput mulInput walkTrace :=
  ⟨(by decide : minLogMem ≤ 16), by decide, read_at kLout 0 (cellK 1), read_at kLout 1 (cellK (K.ofBits 2))⟩

/-- The extended program is a valid execution of the executor's on the same input. -/
example : ValidExecution walkProg mulInput walkTrace := ⟨walk_boundary, walk_run⟩

/-- Its register sequence. -/
theorem walk_regs :
    walkTrace.regs = [⟨1, 1⟩, ⟨addressOfIndex 1, 1⟩, ⟨addressOfIndex 2, 1⟩, ⟨addressOfIndex 3, 1⟩,
        ⟨addressOfIndex 31, 1⟩] := by
  show (List.range 5).filterMap (fun n ↦ run walkProg (walkImage kLout) n ⟨1, 1⟩) = _
  simp only [List.range_succ, List.range_zero, List.nil_append, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, run_zero, walk_run1, walk_run2, walk_run3, walk_run4,
    List.singleton_append]
  rfl

/-! ## Proof helpers: the messages the kernel evaluates

A table's messages are its rows' sends over the witness's data (`messagesOn_eq_sends`,
`tables_sends_data`), which Clean derives (`withDerivedData`); the kernel evaluates the rows'
sends, never the data. -/

/-- The sends of a table's rows over the data `d`. -/
def sendsOver (t : Air.Flat.Table K) (d : ProverData K) : List (String × Array K) :=
  t.table.flatMap fun row ↦ rowSends t.component (Environment.fromArray row d)

/-- The `KECCAK` table's sends, over any data, are its circuit's on the row. -/
theorem kT_sendsOver (L : Vector K 25) (d : ProverData K) :
    sendsOver (kT L) d =
      rowSends (opcodeComponent keccakTable) (Environment.fromArray (rawRow (kRow L)) d) := by
  simp only [sendsOver, kT, opT, ownTable, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- A bytecode block row's sends, as `bytecode_sends_gen` gives them. -/
def bcSendsOf (r : BytecodeRow K) : List (String × Array K) :=
  [(BytecodePush.name,
    #[r.idx, 1, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5], r.op[6],
      r.op[7], r.op[8], r.op[9], r.op[10], r.op[11]]),
   (BytecodePull.name,
    #[r.idx, r.cntFin, r.opcode, r.op[0], r.op[1], r.op[2], r.op[3], r.op[4], r.op[5],
      r.op[6], r.op[7], r.op[8], r.op[9], r.op[10], r.op[11]])]

/-- The bytecode block's sends, over any data, read off its typed rows: the kernel then never
flattens a row into its cells nor evaluates the circuit. -/
theorem bcT_sendsOver (d : ProverData K) :
    sendsOver bcT d =
      (List.ofFn fun i ↦ bytecodeRowOf walkProg i (bcCntFin i)).flatMap bcSendsOf := by
  have h (r : BytecodeRow K) :
      rowSends (bytecodeComponent walkProg) (Environment.fromArray (rawRow r) d) = bcSendsOf r := by
    rw [rowSends_bytecodeComponent, bytecode_sends_gen _ _ _ _ (eval_rowVar _ d)]
    rfl
  simp only [sendsOver, bcT, ownTable, bcRows, List.ofFn_eq_map, List.flatMap_map, h]

/-- Before a kernel decision: the `KECCAK` table's sends in the closed form of `keccak_sends_gen`,
read off the row's fields, so that the kernel never flattens the row into its cells nor evaluates
the circuit. -/
macro "keccak_sends_closed" : tactic =>
  `(tactic| rw [LeanVMTests.Arithmetization.Statement.kT_sendsOver, rowSends_mk,
    keccak_sends_gen _ _ _ _ (eval_rowVar _ _)])

/-- The same for the bytecode block. -/
macro "bytecode_sends_closed" : tactic =>
  `(tactic| rw [LeanVMTests.Arithmetization.Statement.bcT_sendsOver])

/-- A witness's messages on a channel: the verifier's two sends, then the sends of the rows of
`ts` over the witness's data. -/
theorem messagesOn_mkW (ts : List (Air.Flat.Table K)) (hc) (c : RawChannel K) :
    messagesOn (mkW ts hc) c =
      ((([(StatePush.name, #[1, 1]), (StatePull.name, #[walkProg.pcFinal, 1])] ++
        ts.flatMap fun t ↦ sendsOver t (mkW ts hc).data).filter (·.1 = c.name)).map (·.2)) := by
  rw [messagesOn_eq_sends, tables_sends_data,
    mkW_flatMap ts hc (fun comp rows ↦ rows.flatMap fun row ↦
      rowSends comp (Environment.fromArray row (mkW ts hc).data))]
  rfl

/-- The same for the fixture, which is never unfolded: its default proof that the components are
the ensemble's has the type of `rfl`. -/
theorem messagesOn_walkW (L : Vector K 25) (c rA : K) (cnt : ℕ → K) (ch : RawChannel K) :
    messagesOn (walkW L c rA cnt) ch =
      ((([(StatePush.name, #[1, 1]), (StatePull.name, #[walkProg.pcFinal, 1])] ++
        [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT].flatMap fun t ↦
          sendsOver t (walkW L c rA cnt).data).filter (·.1 = ch.name)).map (·.2)) :=
  messagesOn_mkW _ _ ch

theorem memT_table (L : Vector K 25) (cnt : ℕ → K) :
    (memT L cnt).table = List.ofFn (memRowArr L cnt) := by
  dsimp only [memT, ownTable]

/-- The seed message of cell `i`: `(g^i, 1, mem[i])`. -/
def seedMsg (L : Vector K 25) (i : Fin (2 ^ 16)) : Array K :=
  #[addressOfIndex i, 1, (walkImage L i).limb 0, (walkImage L i).limb 1]

/-- The finalize message of cell `i`: `(g^i, cnt i, mem[i])`. -/
def finMsg (L : Vector K 25) (cnt : ℕ → K) (i : Fin (2 ^ 16)) : Array K :=
  #[addressOfIndex i, cnt i, (walkImage L i).limb 0, (walkImage L i).limb 1]

/-- Row `i` of the memory block pushes its seed and pulls its finalize message, over any data. -/
theorem memRow_sends (L : Vector K 25) (cnt : ℕ → K) (d : ProverData K) (i : Fin (2 ^ 16)) :
    rowSends (memComponent 16) (Environment.fromArray (memRowArr L cnt i) d) =
      [(MemPush.name, seedMsg L i), (MemPull.name, finMsg L cnt i)] := by
  rw [rowSends_memComponent, memRowArr,
    mem_sends_gen _ _ _ _ (eval_rowVar (memRowOf (walkImage L) i (cnt i)) d)]
  rfl

/-- The memory block sends nothing on a channel that is not its pair. -/
theorem memT_filter (L : Vector K 25) (cnt : ℕ → K) (d : ProverData K) (n : String)
    (hn : n ≠ MemPush.name) (hn' : n ≠ MemPull.name) :
    (sendsOver (memT L cnt) d).filter (·.1 = n) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  rw [sendsOver, memT_table, List.mem_flatMap] at hp
  obtain ⟨row, hrow, hp⟩ := hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  rw [show (memT L cnt).component = memComponent 16 from rfl, memRow_sends] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simpa using Ne.symm hn
  · simpa using Ne.symm hn'

/-- The memory block's pushes are the seeds of every cell, in order. -/
theorem memT_pushes (L : Vector K 25) (cnt : ℕ → K) (d : ProverData K) :
    ((sendsOver (memT L cnt) d).filter (·.1 = MemPush.toRaw.name)).map (·.2) =
      List.ofFn (seedMsg L) := by
  have h1 : ∀ i, ((rowSends (memComponent 16)
      (Environment.fromArray (memRowArr L cnt i) d)).filter (·.1 = MemPush.toRaw.name)).map (·.2) =
        [seedMsg L i] := fun i ↦ by
    rw [memRow_sends]
    rfl
  rw [sendsOver, memT_table, List.filter_flatMap, List.map_flatMap, List.ofFn_eq_map,
    List.flatMap_map, List.ofFn_eq_map,
    show (memT L cnt).component = memComponent 16 from rfl]
  simp only [h1]
  rw [← List.map_eq_flatMap]

/-- The memory block's pulls are the finalizes of every cell, in order. -/
theorem memT_pulls (L : Vector K 25) (cnt : ℕ → K) (d : ProverData K) :
    ((sendsOver (memT L cnt) d).filter (·.1 = MemPull.toRaw.name)).map (·.2) =
      List.ofFn (finMsg L cnt) := by
  have h1 : ∀ i, ((rowSends (memComponent 16)
      (Environment.fromArray (memRowArr L cnt i) d)).filter (·.1 = MemPull.toRaw.name)).map (·.2) =
        [finMsg L cnt i] := fun i ↦ by
    rw [memRow_sends]
    rfl
  rw [sendsOver, memT_table, List.filter_flatMap, List.map_flatMap, List.ofFn_eq_map,
    List.flatMap_map, List.ofFn_eq_map,
    show (memT L cnt).component = memComponent 16 from rfl]
  simp only [h1]
  rw [← List.map_eq_flatMap]

/-- The bytecode block sends nothing on a channel that is not its pair. -/
theorem bcT_filter (d : ProverData K) (n : String) (hn : n ≠ BytecodePush.name)
    (hn' : n ≠ BytecodePull.name) :
    (sendsOver bcT d).filter (·.1 = n) = [] := by
  rw [List.filter_eq_nil_iff]
  intro p hp
  rw [sendsOver, show bcT.table = bcRows by dsimp only [bcT, ownTable], bcRows,
    List.mem_flatMap] at hp
  obtain ⟨row, hrow, hp⟩ := hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
  rw [show bcT.component = bytecodeComponent walkProg from rfl, rowSends_bytecodeComponent,
    bytecode_sends_gen _ _ _ _ (eval_rowVar _ d)] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simpa using Ne.symm hn
  · simpa using Ne.symm hn'

/-- The cells the run and the loops touch are the first `touched`; the `untouched` rest
of the `2^16` are seeded and finalized with count `1` and cancel. -/
abbrev touched : ℕ := 44
abbrev untouched : ℕ := 65492
theorem touched_add_untouched : touched + untouched = 2 ^ 16 := by decide

/-- The seeds, split at the touched cells. -/
theorem seeds_split (L : Vector K 25) : List.ofFn (seedMsg L) =
    (List.ofFn fun i : Fin touched ↦ seedMsg L (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedMsg L (Fin.natAdd touched j) := by
  rw [show List.ofFn (seedMsg L) = List.ofFn fun i : Fin (touched + untouched) ↦ seedMsg L i
    from rfl, List.ofFn_add]
  rfl

/-- The finalizes, split the same way: past the touched cells, with counts `1`, they are the
seeds. -/
theorem fins_split (L : Vector K 25) (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    List.ofFn (finMsg L cnt) =
      (List.ofFn fun i : Fin touched ↦ finMsg L cnt (Fin.castAdd untouched i)) ++
        List.ofFn fun j : Fin untouched ↦ seedMsg L (Fin.natAdd touched j) := by
  rw [show List.ofFn (finMsg L cnt) = List.ofFn fun i : Fin (touched + untouched) ↦ finMsg L cnt i
    from rfl, List.ofFn_add]
  refine congrArg₂ _ rfl (congrArg _ (funext fun j ↦ ?_))
  show #[addressOfIndex (touched + j), cnt (touched + j), (walkImage L (Fin.natAdd touched
      j)).limb 0,
    (walkImage L (Fin.natAdd touched j)).limb 1] = _
  rw [h _ (Nat.le_add_right touched j)]
  rfl

/-! ## The witness satisfies the statement -/

/-- Constraints that hold on a table's rows over any data hold on the witness. -/
theorem mkW_constraints (ts : List (Air.Flat.Table K)) (hc)
    (h : ∀ t ∈ ts, ∀ row ∈ t.table, ∀ d : ProverData K,
      t.component.operations.ConstraintsHold (Environment.fromArray row d)) :
    (mkW ts hc).Constraints := by
  intro t ht row hrow
  obtain ⟨t₀, ht₀, hcomp, htab⟩ := mem_mkW ht
  rw [Air.Flat.Table.environment, hcomp]
  rw [htab] at hrow
  exact h t₀ ht₀ row hrow _

/-- Every component's constraints hold, for every count and every output lane: the counts are
never constrained, only balanced (§6.2), and the `KECCAK` table has no constraint, so the
rejections below fail on their conjunct alone. The `JUMP` residuals hold with `w = b = 1`. -/
theorem walk_constraints (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (walkW L c rA cnt).Constraints := by
  refine mkW_constraints _ _ fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ ↦ xor_constraints _
  · exact fun _ _ _ ↦ mul_constraints _
  · exact fun _ _ _ ↦ set_constraints _
  · exact fun _ _ _ ↦ deref_constraints _
  · intro r hr d
    simp only [jumpT, opT, ownTable, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact jumpRaw_constraints _ 1 1 (by decide +kernel) (by decide +kernel) _
  · exact fun _ _ _ ↦ keccak_constraints _
  · exact fun _ _ _ ↦ mem_constraints _ _
  · exact fun _ _ _ ↦ bytecode_constraints _ _

/-- The state pair balances: the run's four steps against the boundary, and the three closed
walks of the loops. -/
theorem walk_state_balanced :
    BalancedPair (walkW kLout 1 g memCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ StatePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ StatePull.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePush.toRaw.name (by decide) (by decide),
    bcT_filter _ StatePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  decide +kernel

/-- The bytecode pair balances: every executed slot read once, the seeds and finalizes of all
thirty-two. -/
theorem walk_bytecode_balanced :
    BalancedPair (walkW kLout 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    memT_filter _ _ _ BytecodePush.toRaw.name (by decide) (by decide),
    memT_filter _ _ _ BytecodePull.toRaw.name (by decide) (by decide)]
  keccak_sends_closed
  bytecode_sends_closed
  decide +kernel

/-- The memory pair, reduced to the touched cells: with the block's seeds and finalizes split
at cell `touched` and the untouched suffix cancelled, balance is a permutation the kernel
decides. -/
theorem mem_balanced_iff (L : Vector K 25) (c rA : K) (cnt : ℕ → K)
    (h : ∀ i, touched ≤ i → cnt i = 1) :
    BalancedPair (walkW L c rA cnt) MemPull.toRaw MemPush.toRaw ↔
      ((List.filter (·.1 = MemPush.toRaw.name)
        ([(StatePush.name, #[1, 1]), (StatePull.name, #[walkProg.pcFinal, 1])] ++
          sendsOver xorT (walkW L c rA cnt).data ++ sendsOver (mulT rA) (walkW L c rA cnt).data ++
          sendsOver (setT c) (walkW L c rA cnt).data ++ sendsOver derefT (walkW L c rA cnt).data ++
          sendsOver jumpT (walkW L c rA cnt).data ++ sendsOver (kT L) (walkW L c rA cnt).data)).map
            (·.2) ++
        List.ofFn fun i : Fin touched ↦ seedMsg L (Fin.castAdd untouched i)).Perm
      ((List.filter (·.1 = MemPull.toRaw.name)
        ([(StatePush.name, #[1, 1]), (StatePull.name, #[walkProg.pcFinal, 1])] ++
          sendsOver xorT (walkW L c rA cnt).data ++ sendsOver (mulT rA) (walkW L c rA cnt).data ++
          sendsOver (setT c) (walkW L c rA cnt).data ++ sendsOver derefT (walkW L c rA cnt).data ++
          sendsOver jumpT (walkW L c rA cnt).data ++ sendsOver (kT L) (walkW L c rA cnt).data)).map
            (·.2) ++
        List.ofFn fun i : Fin touched ↦ finMsg L cnt (Fin.castAdd untouched i)) := by
  unfold BalancedPair
  simp only [messagesOn_walkW, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.filter_append, List.map_append,
    bcT_filter _ MemPush.toRaw.name (by decide) (by decide),
    bcT_filter _ MemPull.toRaw.name (by decide) (by decide), memT_pushes, memT_pulls,
    seeds_split, fins_split L cnt h, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-- The memory pair balances. -/
theorem walk_mem_balanced : BalancedPair (walkW kLout 1 g memCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff kLout 1 g memCnt fun _ ↦ memCnt_of_ge]
  keccak_sends_closed
  decide +kernel

/-- The count product over the first six tables, read off their rows' sends. -/
theorem mkW_countsNonzero (ts : List (Air.Flat.Table K)) (hc)
    (h : ∀ t ∈ ts.take 6, ∀ p ∈ sendsOver t (mkW ts hc).data,
      (p.1 = MemPull.name ∨ p.1 = BytecodePull.name) → ∀ h : 1 < p.2.size, p.2[1] ≠ 0) :
    CountsNonzero (mkW ts hc) := by
  intro t ht i hi hname hsz
  obtain ⟨t₀, ht₀, hcomp, htab⟩ := mem_mkW_take ht
  have htw : t ∈ (mkW ts hc).tables := List.mem_of_mem_take ht
  have hp : (i.channel.name, i.msg) ∈ sendsOver t₀ (mkW ts hc).data := by
    rw [Air.Flat.Table.interactions, List.mem_flatMap] at hi
    obtain ⟨row, hrow, hi⟩ := hi
    rw [sendsOver, List.mem_flatMap]
    refine ⟨row, htab ▸ hrow, ?_⟩
    rw [Air.Flat.Table.environment, (mkW ts hc).same_data t htw, Component.interactionsValues_eq,
      hcomp] at hi
    exact List.mem_map_of_mem (f := fun i : Interaction K ↦ (i.channel.name, i.msg)) hi
  exact h t₀ ht₀ _ hp hname hsz

/-- Every read count is nonzero. -/
theorem walk_countsNonzero : CountsNonzero (walkW kLout 1 g memCnt) :=
  mkW_countsNonzero _ _ (by
    simp only [List.take_succ_cons, List.take_zero, List.forall_mem_cons, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true, and_true]
    keccak_sends_closed
    decide +kernel)

/-- Tables within the row cap are within the caps: the memory log-size is `16`. -/
theorem mkW_caps (ts : List (Air.Flat.Table K)) (hc)
    (h : ∀ t ∈ ts, t.table.length ≤ 2 ^ maxLogRows) : Caps (mkW ts hc) where
  minLogMem_le_logMem := (by decide : minLogMem ≤ 16)
  logMem_le_maxLogMem := by decide
  heights t ht := by
    obtain ⟨t₀, ht₀, -, htab⟩ := mem_mkW ht
    rw [htab]
    exact h t₀ ht₀

/-- The caps: `κ = 16`, heights `1, 1, 2, 1, 4, 1, 2^16, 2^5`; for every count and lane. -/
theorem walk_caps (L : Vector K 25) (c rA : K) (cnt : ℕ → K) : Caps (walkW L c rA cnt) := by
  refine mkW_caps _ _ fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show xorT.table.length = 1 from rfl).trans_le (by decide)
  · exact (show (mulT rA).table.length = 1 from rfl).trans_le (by decide)
  · exact (show (setT c).table.length = 2 from rfl).trans_le (by decide)
  · exact (show derefT.table.length = 1 from rfl).trans_le (by decide)
  · exact (show jumpT.table.length = 4 from rfl).trans_le (by decide)
  · exact (show (kT L).table.length = 1 from rfl).trans_le (by decide)
  · rw [memT_table, List.length_ofFn]; decide
  · rw [show bcT.table = bcRows by dsimp only [bcT, ownTable], bcRows, List.length_ofFn]; decide

/-! ## What the fixed columns and the derived data give

The three facts that were hypotheses of the statement until Clean's fixed columns are theorems of
every witness now (`indexColumnsAreRowIndices`, `seedRowsAreTheImage`,
`bytecodeRowsAreTheProgram`); here they are on the fixture, and the rejections below show the
fixed columns, not a hypothesis, carrying them. -/

/-- The index column is the row index (§6.5), for every count and lane. -/
theorem walk_indexColumns (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    IndexColumnsAreRowIndices (walkW L c rA cnt) :=
  indexColumnsAreRowIndices _ (by decide)

/-- The same, read off the block's rows. -/
example (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    IndexColumnsAreRowIndices (walkW L c rA cnt) := by
  intro i hi
  simp only [walk_table6]
  rw [List.getElem_ofFn, memRowArr, rawRow, memRowAt_toElements]
  rfl

/-- The memory block's rows are the image the data names (§6.2), for every count and lane. -/
theorem walk_seedRows (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    SeedRowsAreTheImage (walkW L c rA cnt) :=
  seedRowsAreTheImage _ (by decide)

/-- The bytecode block's rows are the program's (§8.6). -/
theorem walk_bytecodeRows (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    BytecodeRowsAreTheProgram walkProg (walkW L c rA cnt) :=
  bytecodeRowsAreTheProgram _

/-- The derived data is well shaped: its `"mem"` table has the `2^16` rows of the image. -/
example (L : Vector K 25) (c rA : K) (cnt : ℕ → K) : WellShapedData (walkW L c rA cnt).data :=
  (walk_caps L c rA cnt).well_shaped

/-- The executor's input lanes permute to its output lanes (the table tests' `keccak_lanes`):
one kernel evaluation of Keccak-f[1600]. -/
theorem keccak_lanes :
    ∀ l : Fin 25, stateLanes (keccakF1600 (laneState fun l ↦ kLin[l])) l = kLout[l] := by
  decide +kernel

/-- The honest `KECCAK` row satisfies the relation. -/
theorem kRow_relation : KeccakRelation (kRow kLout) := by
  funext l
  exact (keccak_lanes l).symm

/-- The `KECCAK` table is valid, for every count. -/
theorem walk_keccakValid (c rA : K) (cnt : ℕ → K) : KeccakRowsValid (walkW kLout c rA cnt) := by
  intro r hr
  rw [keccakRows, walk_table5, List.map_singleton, List.mem_singleton] at hr
  subst hr
  rw [rawRow, keccakRowAt_toElements]
  exact kRow_relation

/-- The two public words sit at `g^0` and `g^1` of the image the data names, whatever the output
lanes. -/
theorem walk_word0 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW L c rA cnt).data).2.read (addressOfIndex 0) = some mulInput.word0 := by
  rw [walk_imageOf]
  exact read_at L 0 mulInput.word0

theorem walk_word1 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW L c rA cnt).data).2.read (addressOfIndex 1) = some mulInput.word1 := by
  rw [walk_imageOf]
  exact read_at L 1 mulInput.word1

/-- The honest witness satisfies the constraint statement. -/
theorem walk_satisfiedBy : SatisfiedBy walkProg mulInput (walkW kLout 1 g memCnt) where
  public_input_eq := rfl
  constraints := walk_constraints kLout 1 g memCnt
  state_balanced := walk_state_balanced
  mem_balanced := walk_mem_balanced
  bytecode_balanced := walk_bytecode_balanced
  counts_nonzero := walk_countsNonzero
  caps := walk_caps kLout 1 g memCnt
  keccak_valid := walk_keccakValid 1 g memCnt
  word0_eq := walk_word0 kLout 1 g memCnt
  word1_eq := walk_word1 kLout 1 g memCnt

/-- The former hypotheses follow from it. -/
example : IndexColumnsAreRowIndices (walkW kLout 1 g memCnt) ∧
    SeedRowsAreTheImage (walkW kLout 1 g memCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW kLout 1 g memCnt) :=
  ⟨walk_satisfiedBy.index_columns, walk_satisfiedBy.seed_rows, walk_satisfiedBy.bytecode_rows⟩

/-! ## The witness represents the trace -/

theorem walk_table2 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (tableAt (walkW L c rA cnt) 2).table = [setRow0 c, setRow1].map rawRow :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 2 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, setT, opT, ownTable])
theorem walk_table1 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (tableAt (walkW L c rA cnt) 1).table = [mulRow rA].map rawRow :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 1 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, mulT, opT, ownTable])
theorem walk_table4 (L : Vector K 25) (c rA : K) (cnt : ℕ → K) :
    (tableAt (walkW L c rA cnt) 4).table =
      [jumpRow3, jumpRow5, jumpRow7, jumpRow9].map (jumpRaw · 1 1) :=
  (mkW_tableAt [xorT, mulT rA, setT c, derefT, jumpT, kT L, memT L cnt, bcT] rfl 4 (by simp)).trans
    (by simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.reduceMod, List.getElem_cons_succ,
      List.getElem_cons_zero, jumpT, opT, ownTable])

/-- Each of the run's four steps is one row's state pull and push. -/
theorem walk_regs_embed :
    ∀ k (hk : k + 1 < walkTrace.regs.length),
      RowSteps (walkW kLout 1 g memCnt) walkTrace.regs[k] walkTrace.regs[k + 1] := by
  intro k hk
  have hk' : k < 4 := by rw [walk_regs] at hk; exact Nat.lt_of_succ_lt_succ hk
  simp only [walk_regs]
  interval_cases k
  · show RowSteps (walkW kLout 1 g memCnt) ⟨1, 1⟩ ⟨addressOfIndex 1, 1⟩
    exact ⟨_, tableAt_mem _ 2, rawRow (setRow0 1),
      by rw [walk_table2]; exact List.mem_cons_self,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨addressOfIndex 1, 1⟩ ⟨addressOfIndex 2, 1⟩
    exact ⟨_, tableAt_mem _ 2, rawRow setRow1,
      by rw [walk_table2]; exact List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨addressOfIndex 2, 1⟩ ⟨addressOfIndex 3, 1⟩
    exact ⟨_, tableAt_mem _ 1, rawRow (mulRow g),
      by rw [walk_table1]; exact List.mem_cons_self,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel⟩
  · show RowSteps (walkW kLout 1 g memCnt) ⟨addressOfIndex 3, 1⟩ ⟨addressOfIndex 31, 1⟩
    exact ⟨_, tableAt_mem _ 4, jumpRaw jumpRow3 1 1,
      by rw [walk_table4]; exact List.mem_cons_self,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel,
      by rw [rowMessagesOn_eq_rowSends, tableAt_component]; decide +kernel⟩

/-- The honest witness represents the trace: the completeness instance for this program,
by hand. -/
theorem walk_represents : AssignmentRepresents (walkW kLout 1 g memCnt) walkTrace where
  κ_eq := imageOf_fst _ (by decide)
  image_eq i _ := imageOf_apply_of_memRows (walk_memRows kLout 1 g memCnt) (by decide) i _
  regs_embed := walk_regs_embed

/-- The completeness instance for this program: the trace is a valid execution, the
witness satisfies the statement and represents the trace. -/
theorem walk_t1_instance : ValidExecution walkProg mulInput walkTrace ∧
    SatisfiedBy walkProg mulInput (walkW kLout 1 g memCnt) ∧
      AssignmentRepresents (walkW kLout 1 g memCnt) walkTrace :=
  ⟨⟨walk_boundary, walk_run⟩, walk_satisfiedBy, walk_represents⟩

/-- The image the witness names is the trace's, as one equality. -/
example : imageOf (walkW kLout 1 g memCnt).data = ⟨16, walkImage kLout⟩ :=
  assignmentRepresents_image walk_represents

end LeanVMTests.Arithmetization.Statement
