import LeanVM.Arithmetization.Completeness.Basics

/-!
# Tests: the constraint statement

A classic test for kernel evaluation: the fixture decides `K` and `E` arithmetic and the
bus permutations in the kernel.

**The fixture** is one hand-built witness of `SatisfiedBy` for the program of the execution
tests, the executor's `mul_192bit_word` (`crates/leanvm_core/src/cpu/mod.rs:887-904`, `tests/LeanVMTests/
Semantics/Execution.lean`), extended with closed walks: a `JUMP` to the sentinel after the three
instructions, and three blocks run in frames disjoint from the program's own, each a loop ending in
a `JUMP` back to its first instruction: one `XOR`, one `DEREF`, eight `BLAKE2S` rows. The statement
accepts rows that are not steps of the run as long as the state pair balances (Prop. 6.1: one walk
from the initial to the final registers, and closed walks), and the fixture exercises that.
The thirty-two-slot program `walkProg` runs
four steps from `(1, 1)` to `(g^31, 1)` (`walk_run`, a `ValidExecution`), and its honest witness
`walkW 1 g memCnt` at the minimum memory size `2^16` satisfies every conjunct of `SatisfiedBy`
(`walk_satisfiedBy`) and represents the trace (`walk_represents`): the completeness instance
for this program, by hand (`walk_t1_instance`). The witness is parametric in the first
`SET_CONSTANT` row's read count, the product row's read count of `x`, and the memory block's
finalize counts, so that the rejections below are the honest witness with one thing changed.

**What the proofs exercise.** The eight tables are the witness's `tables` in the ensemble's
order, the memory block's `2^16` rows built by `List.ofFn` and never enumerated: its constraints
hold row-generically (the block has none), its interactions on a foreign channel are `[]` by a
lemma (`memT_filter`), and its share of the memory pair is split (`List.ofFn_add`) into the
twenty-nine cells the run touches, decided in the kernel with the tables' reads, and the
untouched suffix, whose seed and finalize messages coincide because its finalize counts are `1`
(`memCnt_of_ge`). The kernel evaluates a table's interactions through Clean's
`Component.rowOperations` (`table_interactions_eq`), since `Component.operations` reaches them
through `instantiate` and `toSubcircuit`, which the kernel does not unfold.

**Rejections**, each the honest witness with one thing changed, and each failing exactly the
conjunct named. A wrong finalize count unbalances the memory pair (§6.2 "Nothing checks the
finalize counts"): cell `4`'s finalize count `1` instead of `g`. A read count of `0` that
*balances* fails `CountsNonzero` alone (§6.2 "The count product"): the first `SET_CONSTANT`
row reads `x` with count `0`, a pull and a push of one tuple, the product row then reads `x`
first, and every other conjunct still holds (`zero_count_witness`). A wrong digest fails
`Blake2sRowsValid` (§8.5). A memory block whose index column is shifted fails
`IndexColumnsAreRowIndices` (§6.5). A wrong public word fails `word0_eq` (§8.2). A three-row
table and a four-row `BLAKE2S` table are within `Caps`: a table's row count need not be a power
of two, and there is no `BLAKE2S` floor (the protocol pads every table with public padding rows,
`doc/leanvm` §`sec:e2e-pad`).
-/

namespace LeanVMTests.Arithmetization.Statement

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component EnsembleWitness)

/-! ## The fixture: `mul_192bit_word` with closed walks -/

-- The operands and product of the executor test `mul_192bit_word` at leanVM a386121f.
def mulX : E :=
  E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfeedfacedeadbeef) (K.ofBits 0x1111222233334444)
def mulY : E :=
  E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0x13579bdf2468ace0) (K.ofBits 0x5555666677778888)
def mulXY : E :=
  E.ofLimbs (K.ofBits 0xf4bccd9a2e8e525b) (K.ofBits 0xf85ebb9433986f2f) (K.ofBits 0x918137982bf175ac)

-- The executor test `blake2s_computes_the_compression` at leanVM a386121f: the nine cells of its
-- row.
def rustM0 : E := E.ofLimbs (K.ofBits 0x0123456789abcdef) (K.ofBits 0xfedcba9876543210) 0
def rustM1 : E := E.ofLimbs (K.ofBits 0x1111222233334444) (K.ofBits 0x5555666677778888) 0
def rustM2 : E := E.ofLimbs (K.ofBits 0xdeadbeefcafebabe) (K.ofBits 0x0badf00d0badf00d) 0
def rustM3 : E := E.ofLimbs (K.ofBits 0x9999aaaabbbbcccc) (K.ofBits 0xddddeeeeffff0000) 0
def rustCv0 : E := E.ofLimbs (K.ofBits 0x0000000000000007) 0 0
def rustCv1 : E := E.ofLimbs (K.ofBits 0x000000000000000b) 0 0
def rustMd : E := E.ofLimbs (K.ofBits 0x0000000000000040) (K.ofBits 0x00000000ffffffff) 0
def rustOut0 : E := E.ofLimbs (K.ofBits 0x583fffe1350e2137) (K.ofBits 0x0de9e32629a5c508) 0
def rustOut1 : E := E.ofLimbs (K.ofBits 0xf1b0679a15df60bb) (K.ofBits 0x0228c8d4ed9b3a24) 0

/-- The public input `[w(1), w(2)]`. -/
def mulInput : PublicInput := ⟨![1, 0, K.ofBits 2, 0]⟩

/-- A word of `K` as a cell. -/
def cellK (a : K) : E := E.ofLimbs a 0 0

/-- The program: the executor's three instructions in frame `1` (slots `0..2`), a `JUMP` to the
sentinel (`3`), an `XOR` loop in frame `g^5` (`4`, `5`), a `DEREF` loop in the same frame
(`6`, `7`), a `BLAKE2S` loop of eight rows in frame `g^14` (`8..16`), never-executed slots
(`17..30`) and the sentinel (`31`, not a `JUMP`). Each block's `JUMP` reads `c = 1`, its
block's first counter `d`, and its own frame `f`. -/
def walkProg : Program :=
  ⟨5, by decide, fun i ↦
    match (i : ℕ) with
    | 0 => .setConstant (gpow 2) mulX
    | 1 => .setConstant (gpow 3) mulY
    | 2 => .mulNative (gpow 2) (gpow 3) (gpow 4)
    | 3 => .jump (gpow 26) (gpow 27) (gpow 28)
    | 4 => .xor 1 1 1
    | 5 => .jump g (gpow 2) (gpow 6)
    | 6 => .deref (gpow 6) 1 1 .cell
    | 7 => .jump g (gpow 3) (gpow 6)
    | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      .blake2s ![gpow 2, gpow 3, gpow 4, gpow 5] 1 (gpow 6) (gpow 8)
    | 16 => .jump (gpow 9) (gpow 10) (gpow 11)
    | _ => .xor 1 1 1⟩

/-- The twenty-nine cells the run and the loops touch, by index; every other cell of the
image is `0`. Frame `1`: the public words (`0`, `1`), the operands and the product (`2..4`),
the sentinel `JUMP`'s `c, d, f` (`26..28`). Frame `g^5`: the `XOR` and `DEREF` cell (`5`),
`c` (`6`), the two blocks' `d` (`7`, `8`), the pointer and `f` (`11`). Frame `g^14`: the
`BLAKE2S` cells in the executor's layout (`14..22`) and the block's `c, d, f` (`23..25`). -/
def walkCells : Array E :=
  #[cellK 1, cellK (K.ofBits 2), mulX, mulY, mulXY,
    0, cellK 1, cellK (gpow 4), cellK (gpow 6), 0, 0, cellK (gpow 5), 0, 0,
    rustCv0, rustCv1, rustM0, rustM1, rustM2, rustM3, rustOut0, rustOut1, rustMd,
    cellK 1, cellK (gpow 8), cellK (gpow 14),
    cellK 1, cellK (gpow 31), cellK 1]

/-- The image, at the minimum size `2^16`. -/
def walkImage : MemImage minLogMem := fun i ↦ (walkCells[(i : ℕ)]?).getD 0

/-- The trace: four steps. -/
def walkTrace : Trace walkProg := ⟨minLogMem, walkImage, 4⟩

/-- The `"mem"` table of the prover data: the image, one row of limbs per word. -/
def walkRows : Array (Vector K 3) :=
  Array.ofFn fun i : Fin (2 ^ minLogMem) ↦
    #v[(walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2]

/-- The prover data: the image as its `"mem"` table, matched on arity (as in the channel, table
and boundary tests). -/
def walkData : ProverData K := fun _ n ↦
  match n with
  | 3 => walkRows
  | _ => #[]

/-- The table, read back. By `unfold` and not by `rfl`: the match on the arity `3` is stuck for
definitional unfolding, which then unrolls `Array.ofFn` over the `2^16` rows. -/
theorem memRows_walk : memRows walkData = walkRows := by
  unfold memRows walkData
  rfl

/-- The honest finalize counts `g^A[i]` of the touched cells; `1` elsewhere (`memCnt`). -/
def walkCounts : Array K :=
  #[1, 1, g ^ 2, g ^ 2, g, g ^ 5, g ^ 2, g, g, 1, 1, g ^ 3, 1, 1,
    g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g ^ 8, g, g, g, g, g, g]

/-- The finalize count of cell `i`. -/
def memCnt (i : ℕ) : K := (walkCounts[i]?).getD 1

/-- Past the touched cells every finalize count is `1`: the cell was never read. -/
theorem memCnt_of_ge {i : ℕ} (h : 29 ≤ i) : memCnt i = 1 := by
  have hs : walkCounts.size = 29 := rfl
  unfold memCnt
  rw [Array.getElem?_eq_none (hs ▸ h)]
  rfl

/-- The finalize count of slot `i`: every slot up to `16` executes once. -/
def bcCnt (i : ℕ) : K := if i ≤ 16 then g else 1

/-- The same, as the bytecode block's finalize-count column. -/
def bcCntFin (i : Fin (2 ^ walkProg.logSize)) : K := bcCnt i

/-! ## The rows -/

-- Frame `1`: the run.
/-- Slot `0`, `SET_CONSTANT g^2 ← x`, with read count `c` (`1` for the honest prover). -/
def setRow0 (c : K) : SetRow K :=
  ⟨gpow 0, 1, gpow 2, #v[mulX.limb 0, mulX.limb 1, mulX.limb 2], c, 1⟩
/-- Slot `1`, `SET_CONSTANT g^3 ← y`. -/
def setRow1 : SetRow K := ⟨gpow 1, 1, gpow 3, #v[mulY.limb 0, mulY.limb 1, mulY.limb 2], 1, 1⟩
/-- Slot `2`, `MUL_NATIVE`: the read of `x` with count `rA` (`g` for the honest prover, the
second read), the second read of `y`, the first of the product. -/
def mulRow (rA : K) : MulRow K :=
  ⟨gpow 2, 1, gpow 2, gpow 3, gpow 4, #v[mulX.limb 0, mulX.limb 1, mulX.limb 2],
    #v[mulY.limb 0, mulY.limb 1, mulY.limb 2], rA, g, 1, 1⟩
/-- Slot `3`, the `JUMP` to the sentinel: `(g^3, 1) → (g^31, 1)`. -/
def jumpRow3 : JumpRow K := ⟨gpow 3, 1, gpow 26, gpow 27, gpow 28, 1, gpow 31, 1, 1, 1, 1, 1⟩

-- Frame `g^5`: the `XOR` and `DEREF` blocks.
/-- Slot `4`, `XOR 1 1 1` on the zero cell `g^5`: three reads. -/
def xorRow : XorRow K := ⟨gpow 4, gpow 5, 1, 1, 1, #v[0, 0, 0], #v[0, 0, 0], 1, g, g ^ 2, 1⟩
/-- Slot `5`, the `JUMP` back to slot `4`. -/
def jumpRow5 : JumpRow K := ⟨gpow 5, gpow 5, g, gpow 2, gpow 6, 1, gpow 4, gpow 5, 1, 1, 1, 1⟩
/-- Slot `6`, `DEREF` in `cell` mode: the pointer `g^5` at `g^11`, the local and target cell
both `g^5` (its fourth and fifth reads). -/
def derefRow : DerefRow K :=
  ⟨gpow 6, gpow 5, gpow 6, 1, 1, 0, 0, gpow 5, #v[0, 0, 0], g, g ^ 4, g ^ 3, 1⟩
/-- Slot `7`, the `JUMP` back to slot `6`. -/
def jumpRow7 : JumpRow K := ⟨gpow 7, gpow 5, g, gpow 3, gpow 6, 1, gpow 6, gpow 5, g, 1, g ^ 2, 1⟩

-- Frame `g^14`: the `BLAKE2S` block.
/-- The two limbs of a canonical cell. -/
def cell (v : E) : Vector K 2 := #v[v.limb 0, v.limb 1]
/-- Slot `8 + j`, the executor's `BLAKE2S` row in frame `g^14`: the `j`-th read of each of its
nine cells. -/
def blakeRow (j : Fin 8) : Blake2sRow K :=
  ⟨gpow (8 + j), gpow 14, gpow 2, gpow 3, gpow 4, gpow 5, 1, gpow 6, gpow 8,
    cell rustM0, cell rustM1, cell rustM2, cell rustM3, cell rustOut0, cell rustOut1,
    cell rustCv0, cell rustCv1, cell rustMd,
    gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, gpow j, 1⟩
/-- Slot `16`, the `JUMP` back to slot `8`. -/
def jumpRow16 : JumpRow K :=
  ⟨gpow 16, gpow 14, gpow 9, gpow 10, gpow 11, 1, gpow 8, gpow 14, 1, 1, 1, 1⟩

/-- A `JUMP` row with its two local witnesses `w = 1`, `b = 1` (every condition is `1`). -/
def jumpRaw (r : JumpRow K) : Array K := rawRow r ++ #[1, 1]

theorem jumpRaw_size (rs : List (JumpRow K)) :
    ∀ r ∈ rs.map jumpRaw, r.size = size JumpRow + 2 := by
  intro r hr
  rw [List.mem_map] at hr
  obtain ⟨_, -, rfl⟩ := hr
  rw [jumpRaw, Array.size_append, rawRow_size]
  rfl

/-- Row `i` of the memory block: `(g^i, cnt i, mem[i])`, the raw form of the typed row. -/
def memRowArr (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow i, cnt i,
    #v[(walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2]⟩ : MemRow K)).toArray

/-- The memory row's five coordinates, without evaluating the block's row list. -/
theorem memRowArr_eq (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) :
    memRowArr cnt i =
      #[gpow i, cnt i, (walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2] := by
  with_unfolding_all rfl

/-! ## The tables and the witness -/

/-- A table of the witness: a component and its rows, over the fixture's data. -/
def mkT {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (c : GeneralFormalCircuit K Input Output) (width : ℕ) (rows : List (Array K))
    (h : ∀ r ∈ rows, r.size = width) : Air.Flat.Table K :=
  ⟨⟨c⟩, width, rows, walkData, h⟩

def xorT : Air.Flat.Table K :=
  mkT xorTable (size XorRow) ([xorRow].map rawRow) (rawRows_size [xorRow])
/-- The `MUL_NATIVE` table, its row's read count of `x` `rA`. -/
def mulT (rA : K) : Air.Flat.Table K :=
  mkT mulTable (size MulRow) ([mulRow rA].map rawRow) (rawRows_size [mulRow rA])
/-- The `SET_CONSTANT` table, its first row's read count `c`. -/
def setT (c : K) : Air.Flat.Table K :=
  mkT setTable (size SetRow) ([setRow0 c, setRow1].map rawRow) (rawRows_size [setRow0 c, setRow1])
def derefT : Air.Flat.Table K :=
  mkT derefTable (size DerefRow) ([derefRow].map rawRow) (rawRows_size [derefRow])
def jumpT : Air.Flat.Table K :=
  mkT jumpTable (size JumpRow + 2) ([jumpRow3, jumpRow5, jumpRow7, jumpRow16].map jumpRaw)
    (jumpRaw_size [jumpRow3, jumpRow5, jumpRow7, jumpRow16])
def blakeT : Air.Flat.Table K :=
  mkT blake2sTable (size Blake2sRow) ((List.ofFn blakeRow).map rawRow)
    (rawRows_size (List.ofFn blakeRow))
/-- The memory block, with finalize counts `cnt`. -/
def memT (cnt : ℕ → K) : Air.Flat.Table K :=
  mkT memTable (size MemRow) (List.ofFn (memRowArr cnt)) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _)
/-- The bytecode block: the program's rows (`bytecodeRowOf`). -/
def bcT : Air.Flat.Table K :=
  mkT bytecodeTable (size BytecodeRow)
    (List.ofFn fun i ↦ (toElements (bytecodeRowOf walkProg i (bcCntFin i))).toArray) (by
      intro r hr
      rw [List.mem_ofFn] at hr
      obtain ⟨i, rfl⟩ := hr
      exact rawRow_size _)

/-- A witness over the fixture's data and input with the tables `ts`, eight tables of the
ensemble's components in order: the proofs are by cases on the list, so `ts` is a literal. -/
def mkW (ts : List (Air.Flat.Table K))
    (hlen : (leanIsaEnsemble walkProg).tables.length = ts.length := by rfl)
    (hc : ∀ i (hi : i < (leanIsaEnsemble walkProg).tables.length),
      (leanIsaEnsemble walkProg).tables[i] = (ts[i]'(hlen ▸ hi)).component := by
        intro i hi
        have hi' : i < 8 := hi
        interval_cases i <;> rfl)
    (hd : ∀ t ∈ ts, t.data = walkData := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl) :
    EnsembleWitness (leanIsaEnsemble walkProg) :=
  ⟨ts, walkData, PublicIO.ofInput mulInput, hlen, hc, hd⟩

/-- The witness, with the first `SET_CONSTANT` row's read count `c`, the product row's read
count of `x` `rA`, and the memory block's finalize counts `cnt`; the honest one is
`walkW 1 g memCnt`. -/
def walkW (c rA : K) (cnt : ℕ → K) : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW [xorT, mulT rA, setT c, derefT, jumpT, blakeT, memT cnt, bcT]

/-! ## The tables of the witness, read back -/

/-- The three blocks the statement names, read off the witness. -/
theorem tableAt_five (c rA : K) (cnt : ℕ → K) : tableAt (walkW c rA cnt) 5 = blakeT := rfl
theorem tableAt_six (c rA : K) (cnt : ℕ → K) : tableAt (walkW c rA cnt) 6 = memT cnt := rfl
theorem tableAt_seven (c rA : K) (cnt : ℕ → K) : tableAt (walkW c rA cnt) 7 = bcT := rfl

/-- Their rows. By `dsimp`, never by `rfl`: a definitional comparison of a stuck projection
against a `List.ofFn` unrolls the `2^16` rows. -/
theorem blakeT_table : blakeT.table = (List.ofFn blakeRow).map rawRow := by
  dsimp only [blakeT, mkT]
theorem memT_table (cnt : ℕ → K) : (memT cnt).table = List.ofFn (memRowArr cnt) := by
  dsimp only [memT, mkT]
theorem bcT_table :
    bcT.table = List.ofFn fun i ↦ (toElements (bytecodeRowOf walkProg i (bcCntFin i))).toArray := by
  dsimp only [bcT, mkT]
theorem memBlockRows_eq (c rA : K) (cnt : ℕ → K) :
    memBlockRows (walkW c rA cnt) = List.ofFn (memRowArr cnt) := by
  rw [memBlockRows, tableAt_six, memT_table]

/-! ## The image the data names -/

theorem walk_logSize : (imageOf walkData).1 = minLogMem := by
  show min (Nat.log 2 (memRows walkData).size) maxLogMem = minLogMem
  rw [memRows_walk, walkRows, Array.size_ofFn, Nat.log_pow (by norm_num)]
  rfl

theorem walk_wellShaped : WellShapedData walkData :=
  ⟨by rw [walk_logSize, memRows_walk, walkRows, Array.size_ofFn]⟩

theorem walk_pow_eq : 2 ^ (imageOf walkData).1 = 2 ^ minLogMem := by rw [walk_logSize]

/-- Row `k` of the table, through `getElem?`: a `getElem` with a bound on the `2^16`-row table
makes both the elaborator and the kernel unroll it. -/
theorem walkRows_get? (k : ℕ) (hk : k < 2 ^ minLogMem) :
    walkRows[k]? = some #v[(walkImage ⟨k, hk⟩).limb 0, (walkImage ⟨k, hk⟩).limb 1,
      (walkImage ⟨k, hk⟩).limb 2] := by
  rw [walkRows, Array.getElem?_ofFn, dite_eq_left hk]

theorem walk_image_apply' (k : ℕ) (hk : k < 2 ^ (imageOf walkData).1) :
    (imageOf walkData).2 ⟨k, hk⟩ = walkImage ⟨k, by rw [← walk_pow_eq]; exact hk⟩ := by
  conv_rhs => rw [← ofLimbs_limb (walkImage ⟨k, _⟩)]
  refine imageOf_apply walk_wellShaped ⟨k, hk⟩ (v := #v[(walkImage ⟨k, _⟩).limb 0,
    (walkImage ⟨k, _⟩).limb 1, (walkImage ⟨k, _⟩).limb 2]) ?_
  rw [Array.getElem_eq_iff, memRows_walk]
  exact walkRows_get? k _

/-- Every word the data names is the fixture's image. -/
theorem walk_image_apply (i : Fin (2 ^ (imageOf walkData).1)) :
    (imageOf walkData).2 i = walkImage (Fin.cast walk_pow_eq i) :=
  walk_image_apply' i i.isLt

/-- The image the data names, as one equality of dependent pairs: what every conjunct over
`imageOf w.data` is rewritten with, so that nothing compares the data's log-size against
`minLogMem` definitionally. -/
theorem walk_imageOf : imageOf walkData = ⟨minLogMem, walkImage⟩ := by
  have hκ : (imageOf walkData).1 = minLogMem := walk_logSize
  have hpow : 2 ^ (imageOf walkData).1 = 2 ^ minLogMem := walk_pow_eq
  have hf : ∀ i, (imageOf walkData).2 i = walkImage (Fin.cast hpow i) := walk_image_apply
  revert hκ hpow hf
  generalize imageOf walkData = s
  obtain ⟨κ, img⟩ := s
  intro hκ hpow hf
  dsimp only at hκ hpow hf
  subst hκ
  exact congrArg _ (funext fun i ↦ (hf i).trans (congrArg walkImage (Fin.ext rfl)))

theorem data_eq (c rA : K) (cnt : ℕ → K) : (walkW c rA cnt).data = walkData := rfl

/-! ## The run -/

/-- The instruction at `g^i`. -/
theorem fetch_at (i : ℕ) (ins : Instr) (hi : i < 2 ^ walkProg.logSize := by decide)
    (hd : walkProg.code ⟨i, hi⟩ = ins := by rfl) : walkProg.fetch (gpow i) = some ins := by
  rw [show gpow i = gpow ((⟨i, hi⟩ : Fin (2 ^ walkProg.logSize)) : ℕ) from rfl,
    Program.fetch_gpow, hd]

/-- The instruction at the counter `1 = g^0`. -/
theorem fetch_one : walkProg.fetch 1 = some (.setConstant (gpow 2) mulX) := by
  simpa using fetch_at 0 (.setConstant (gpow 2) mulX)

/-- The word at `g^k`. -/
theorem read_at (k : ℕ) (v : E) (hk : k < 2 ^ minLogMem := by decide)
    (hv : walkImage ⟨k, hk⟩ = v := by rfl) : walkImage.read (gpow k) = some v := by
  rw [show gpow k = gpow ((⟨k, hk⟩ : Fin (2 ^ minLogMem)) : ℕ) from rfl,
    MemImage.read_gpow (by decide), hv]

theorem walk_step0 : step walkProg walkImage ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨1, 1⟩) fetch_one]
  show execute walkImage ⟨1, 1⟩ (.setConstant (gpow 2) mulX) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX]
  decide +kernel

theorem walk_step1 : step walkProg walkImage ⟨gpow 1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 1, 1⟩) (fetch_at 1 (.setConstant (gpow 3) mulY))]
  show execute walkImage ⟨gpow 1, 1⟩ (.setConstant (gpow 3) mulY) = _
  simp only [execute, executeWith, one_mul, read_at 3 mulY]
  decide +kernel

theorem walk_step2 : step walkProg walkImage ⟨gpow 2, 1⟩ = some ⟨gpow 3, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 2, 1⟩) (fetch_at 2 (.mulNative (gpow 2) (gpow 3) (gpow 4)))]
  show execute walkImage ⟨gpow 2, 1⟩ (.mulNative (gpow 2) (gpow 3) (gpow 4)) = _
  simp only [execute, executeWith, one_mul, read_at 2 mulX, read_at 3 mulY, read_at 4 mulXY]
  decide +kernel

theorem walk_step3 : step walkProg walkImage ⟨gpow 3, 1⟩ = some ⟨gpow 31, 1⟩ := by
  rw [step_of_fetch_eq_some (r := ⟨gpow 3, 1⟩) (fetch_at 3 (.jump (gpow 26) (gpow 27) (gpow 28)))]
  show execute walkImage ⟨gpow 3, 1⟩ (.jump (gpow 26) (gpow 27) (gpow 28)) = _
  simp only [execute, executeWith, one_mul, read_at 26 (cellK 1), read_at 27 (cellK (gpow 31)),
    read_at 28 (cellK 1)]
  decide +kernel

theorem walk_run1 : run walkProg walkImage 1 ⟨1, 1⟩ = some ⟨gpow 1, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, Option.bind_eq_bind,
    Option.bind_some, run_zero]

theorem walk_run2 : run walkProg walkImage 2 ⟨1, 1⟩ = some ⟨gpow 2, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run3 : run walkProg walkImage 3 ⟨1, 1⟩ = some ⟨gpow 3, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    Option.bind_eq_bind, Option.bind_some, run_zero]

theorem walk_run4 : run walkProg walkImage 4 ⟨1, 1⟩ = some ⟨gpow 31, 1⟩ := by
  simp (disch := decide +kernel) only [run_succ_of_ne, walk_step0, walk_step1, walk_step2,
    walk_step3, Option.bind_eq_bind, Option.bind_some, run_zero]

/-- The run: four steps from `(1, 1)` to the final registers `(g^31, 1)`. -/
theorem walk_run : run walkProg walkImage 4 Regs.initial = some (Regs.final walkProg) :=
  walk_run4

/-- The public words are in place. -/
theorem walk_boundary : HasPublicBoundary mulInput walkTrace :=
  ⟨le_rfl, by decide, read_at 0 (cellK 1), read_at 1 (cellK (K.ofBits 2))⟩

/-- The extended program is a valid execution of the executor's on the same input. -/
example : ValidExecution walkProg mulInput walkTrace := ⟨walk_boundary, walk_run⟩

/-- Its register sequence. -/
theorem walk_regs :
    walkTrace.regs = [⟨1, 1⟩, ⟨gpow 1, 1⟩, ⟨gpow 2, 1⟩, ⟨gpow 3, 1⟩, ⟨gpow 31, 1⟩] := by
  show (List.range 5).filterMap (fun n ↦ run walkProg walkImage n ⟨1, 1⟩) = _
  simp only [List.range_succ, List.range_zero, List.nil_append, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, run_zero, walk_run1, walk_run2, walk_run3, walk_run4,
    List.singleton_append]
  rfl

/-! ## Proof helpers: the interactions the kernel evaluates -/

/-- The memory block sends nothing on a channel that is not its pair. -/
theorem memT_filter (cnt : ℕ → K) (c : RawChannel K) (hc : c.name ≠ MemPush.name)
    (hc' : c.name ≠ MemPull.name) :
    (memT cnt).interactions.filter (·.channel.name = c.name) = [] :=
  filter_eq_nil_of_rowOps _ c (by
    rw [show (memT cnt).component = ⟨memTable⟩ from rfl, memTable_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · exact fun h ↦ hc (h.symm.trans rfl)
    · exact fun h ↦ hc' (h.symm.trans rfl))

/-- The bytecode block sends nothing on a channel that is not its pair. -/
theorem bcT_filter (c : RawChannel K) (hc : c.name ≠ BytecodePush.name)
    (hc' : c.name ≠ BytecodePull.name) :
    bcT.interactions.filter (·.channel.name = c.name) = [] :=
  filter_eq_nil_of_rowOps _ c (by
    rw [show bcT.component = ⟨bytecodeTable⟩ from rfl, bytecodeTable_rowOps]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro i (rfl | rfl)
    · exact fun h ↦ hc (h.symm.trans rfl)
    · exact fun h ↦ hc' (h.symm.trans rfl))

/-- The cells the run and the loops touch are the first `touched`; the `untouched` rest
of the `2^16` are seeded and finalized with count `1` and cancel. -/
abbrev touched : ℕ := 29
abbrev untouched : ℕ := 65507
theorem touched_add_untouched : touched + untouched = 2 ^ minLogMem := by decide

/-- The seed message of cell `i`: `(g^i, 1, mem[i])`. -/
def seedMsg (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, 1, (walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2]

/-- The finalize message of cell `i`: `(g^i, cnt i, mem[i])`. -/
def finMsg (cnt : ℕ → K) (i : Fin (2 ^ minLogMem)) : Array K :=
  #[gpow i, cnt i, (walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2]

/-- A row of the memory block pushes its seed message … -/
theorem memRow_push (a : Array K) :
    (((⟨memTable⟩ : Component K).rowOperations.interactions.map
      (·.eval (Environment.fromArray a walkData))).filter
        (·.channel.name = MemPush.toRaw.name)).map (·.msg) =
      [#[a[0]?.getD 0, 1, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  rw [memTable_rowOps]
  -- The filter decides the two names by evaluation; the message is the row's variables
  -- evaluated (`Vector.map` is defined by well-founded recursion, so it is rewritten, not
  -- unfolded).
  show [((toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K))).map
    (Expression.eval (Environment.fromArray a walkData))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, 1, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ : MemMsg (Expression K)) =
    #v[var ⟨0⟩, 1, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- … and pulls its finalize message. -/
theorem memRow_pull (a : Array K) :
    (((⟨memTable⟩ : Component K).rowOperations.interactions.map
      (·.eval (Environment.fromArray a walkData))).filter
        (·.channel.name = MemPull.toRaw.name)).map (·.msg) =
      [#[a[0]?.getD 0, a[1]?.getD 0, a[2]?.getD 0, a[3]?.getD 0, a[4]?.getD 0]] := by
  rw [memTable_rowOps]
  show [((toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K))).map (Expression.eval (Environment.fromArray a walkData))).toArray] = _
  rw [show toElements (⟨var ⟨0⟩, var ⟨1⟩, #v[var ⟨2⟩, var ⟨3⟩, var ⟨4⟩]⟩ :
    MemMsg (Expression K)) = #v[var ⟨0⟩, var ⟨1⟩, var ⟨2⟩, var ⟨3⟩, var ⟨4⟩] from by with_unfolding_all rfl]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.toArray_mk]
  rfl

/-- The memory block's pushes are the seeds of every cell, in order. -/
theorem memT_pushes (cnt : ℕ → K) :
    ((memT cnt).interactions.filter (·.channel.name = MemPush.toRaw.name)).map (·.msg) =
      List.ofFn seedMsg := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memT, mkT, Air.Flat.Table.environment, memRow_push, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The memory block's pulls are the finalizes of every cell, in order. -/
theorem memT_pulls (cnt : ℕ → K) :
    ((memT cnt).interactions.filter (·.channel.name = MemPull.toRaw.name)).map (·.msg) =
      List.ofFn (finMsg cnt) := by
  rw [table_interactions_eq, List.filter_flatMap, List.map_flatMap]
  simp only [memT, mkT, Air.Flat.Table.environment, memRow_pull, ← List.map_eq_flatMap,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [memRowArr_eq]
  rfl

/-- The seeds, split at the touched cells. -/
theorem seeds_split : List.ofFn seedMsg =
    (List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)) ++
      List.ofFn fun j : Fin untouched ↦ seedMsg (Fin.natAdd touched j) := by
  rw [show List.ofFn seedMsg = List.ofFn fun i : Fin (touched + untouched) ↦ seedMsg i from rfl,
    List.ofFn_add]
  rfl

/-- The finalizes, split the same way: past the touched cells, with counts `1`, they are the
seeds. -/
theorem fins_split (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    List.ofFn (finMsg cnt) =
      (List.ofFn fun i : Fin touched ↦ finMsg cnt (Fin.castAdd untouched i)) ++
        List.ofFn fun j : Fin untouched ↦ seedMsg (Fin.natAdd touched j) := by
  rw [show List.ofFn (finMsg cnt) = List.ofFn fun i : Fin (touched + untouched) ↦ finMsg cnt i
    from rfl, List.ofFn_add]
  refine congrArg₂ _ rfl (congrArg _ (funext fun j ↦ ?_))
  show #[gpow (touched + j), cnt (touched + j), (walkImage (Fin.natAdd touched j)).limb 0,
    (walkImage (Fin.natAdd touched j)).limb 1, (walkImage (Fin.natAdd touched j)).limb 2] = _
  rw [h _ (Nat.le_add_right touched j)]
  rfl

/-! ## Proof helpers: constraints -/

/-- The `JUMP` table's two residuals hold on its four rows, with the witnesses `w = b = 1`. -/
theorem jumpT_constraints : jumpT.Constraints := by
  intro r hr
  simp only [jumpT, mkT, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
  · rw [Component.constraintsHold_iff]
    simp only [jumpT, mkT, circuit_norm, jumpTable, memRead, bytecodeRead, -BitVec.reduceNeg]
    rintro e (rfl | rfl) <;> decide +kernel

/-! ## The witness satisfies the statement -/

/-- Every component's constraints hold, for every count: the counts are never constrained,
only balanced (§6.2), so the rejections below fail on their conjunct alone. -/
theorem walk_constraints (c rA : K) (cnt : ℕ → K) : (walkW c rA cnt).Constraints := by
  intro t ht
  simp only [EnsembleWitness.allTables, walkW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ ↦ verifier_constraints _ _
  · exact fun _ _ ↦ xor_constraints _
  · exact fun _ _ ↦ mul_constraints _
  · exact fun _ _ ↦ set_constraints _
  · exact fun _ _ ↦ deref_constraints _
  · exact jumpT_constraints
  · exact fun _ _ ↦ blake2s_constraints _
  · exact fun _ _ ↦ mem_constraints _
  · exact fun _ _ ↦ bytecode_constraints _

/-- The state pair balances: the run's four steps against the boundary, and the three closed
walks of the loops. -/
theorem walk_state_balanced : BalancedPair (walkW 1 g memCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter memCnt StatePush.toRaw (by decide) (by decide),
    memT_filter memCnt StatePull.toRaw (by decide) (by decide),
    bcT_filter StatePush.toRaw (by decide) (by decide),
    bcT_filter StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The bytecode pair balances: every executed slot read once, the seeds and finalizes of all
thirty-two. -/
theorem walk_bytecode_balanced :
    BalancedPair (walkW 1 g memCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter memCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter memCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The memory pair, reduced to the touched cells: with the block's seeds and finalizes split
at cell `touched` and the untouched suffix cancelled, balance is a permutation the kernel
decides. -/
theorem mem_balanced_iff (c rA : K) (cnt : ℕ → K) (h : ∀ i, touched ≤ i → cnt i = 1) :
    BalancedPair (walkW c rA cnt) MemPull.toRaw MemPush.toRaw ↔
      (List.map (·.msg) (List.filter (·.channel.name = MemPush.toRaw.name)
        ((walkW c rA cnt).verifierTable.interactions ++ xorT.interactions ++
          (mulT rA).interactions ++ (setT c).interactions ++ derefT.interactions ++
          jumpT.interactions ++ blakeT.interactions)) ++
        List.ofFn fun i : Fin touched ↦ seedMsg (Fin.castAdd untouched i)).Perm
      (List.map (·.msg) (List.filter (·.channel.name = MemPull.toRaw.name)
        ((walkW c rA cnt).verifierTable.interactions ++ xorT.interactions ++
          (mulT rA).interactions ++ (setT c).interactions ++ derefT.interactions ++
          jumpT.interactions ++ blakeT.interactions)) ++
        List.ofFn fun i : Fin touched ↦ finMsg cnt (Fin.castAdd untouched i)) := by
  unfold BalancedPair messagesOn
  rw [EnsembleWitness.interactions]
  simp only [EnsembleWitness.allTables, walkW, mkW, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.filter_append, List.map_append,
    bcT_filter MemPush.toRaw (by decide) (by decide),
    bcT_filter MemPull.toRaw (by decide) (by decide), memT_pushes, memT_pulls,
    seeds_split, fins_split cnt h, ← List.append_assoc]
  exact List.perm_append_right_iff _

/-- The memory pair balances. -/
theorem walk_mem_balanced : BalancedPair (walkW 1 g memCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff 1 g memCnt fun _ ↦ memCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

/-- Every read count is nonzero. -/
theorem walk_countsNonzero : CountsNonzero (walkW 1 g memCnt) := by
  unfold CountsNonzero
  simp only [walkW, mkW, table_interactions_eq]
  decide +kernel

/-- The caps: `κ = 16`, heights `1, 1, 2, 1, 4, 8, 2^16, 2^5`; for every count. -/
theorem walk_caps (c rA : K) (cnt : ℕ → K) : Caps (walkW c rA cnt) where
  minLogMem_le := by rw [data_eq, walk_logSize]
  le_maxLogMem := by rw [data_eq, walk_logSize]; decide
  heights := by
    intro t ht
    simp only [walkW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · exact (show (mulT rA).table.length = 1 from rfl).trans_le (by decide)
    · exact (show (setT c).table.length = 2 from rfl).trans_le (by decide)
    · decide
    · decide
    · rw [blakeT_table, List.length_map, List.length_ofFn]; decide
    · rw [memT_table, List.length_ofFn]; decide
    · rw [bcT_table, List.length_ofFn]; decide
  well_shaped := walk_wellShaped

/-- The index column is the row index, for every count. -/
theorem walk_indexColumns (c rA : K) (cnt : ℕ → K) :
    IndexColumnsAreRowIndices (walkW c rA cnt) := by
  intro i hi
  simp only [memBlockRows_eq]
  rw [List.getElem_ofFn, memRowArr, memRowAt_toElements]

/-- The seed-rows conjunct over any image `s` equal to the fixture's: substituting the image
before anything is compared, since a rewrite under the conjunct's dependent binders unrolls
the data. -/
theorem seedRows_gen {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (cnt : ℕ → K) (hrows : memBlockRows (⟨tables, walkData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn (memRowArr cnt))
    (s : (κ : ℕ) × MemImage κ) (hs : s = ⟨minLogMem, walkImage⟩) :
    ∃ idx cntFin : Fin (2 ^ s.1) → K,
      memBlockRows (⟨tables, walkData, pi, h1, h2, h3⟩ :
        EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn fun i ↦
          (toElements (⟨idx i, cntFin i, #v[(s.2 i).limb 0, (s.2 i).limb 1, (s.2 i).limb 2]⟩ :
            MemRow K)).toArray := by
  subst hs
  exact ⟨fun i ↦ gpow i, fun i ↦ cnt i, hrows⟩

/-- A witness over the fixture's data whose memory block is the honest one, with any finalize
counts, has the image as its seed rows. Stated over a destructured witness, so that its
`data` is the constant `walkData`. -/
theorem seedRows_of {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (cnt : ℕ → K) (hrows : memBlockRows (⟨tables, walkData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) = List.ofFn (memRowArr cnt)) :
    SeedRowsAreTheImage (⟨tables, walkData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) := by
  unfold SeedRowsAreTheImage
  dsimp only
  exact seedRows_gen cnt hrows (imageOf walkData) walk_imageOf

/-- The memory block's rows are the image, for every count. -/
theorem walk_seedRows (c rA : K) (cnt : ℕ → K) : SeedRowsAreTheImage (walkW c rA cnt) :=
  seedRows_of cnt (memBlockRows_eq c rA cnt)

/-- The bytecode block's rows are the program's, with the honest counts. -/
theorem walk_bytecodeRows (c rA : K) (cnt : ℕ → K) :
    BytecodeRowsAreTheProgram walkProg (walkW c rA cnt) :=
  ⟨bcCntFin, by rw [bytecodeBlockRows, tableAt_seven, bcT_table]⟩

/-- The executor's nine cells compress, as the row carries them (the table tests'
`blake2s_relation` on the same cells): one kernel compression. -/
theorem blake_cells_compress :
    CompressCells ![E.ofCell (cell rustM0), E.ofCell (cell rustM1), E.ofCell (cell rustM2),
      E.ofCell (cell rustM3)] (E.ofCell (cell rustCv0)) (E.ofCell (cell rustCv1))
      (E.ofCell (cell rustOut0)) (E.ofCell (cell rustOut1)) (E.ofCell (cell rustMd)) := by
  decide +kernel

/-- Every `BLAKE2S` row of the fixture satisfies the relation: the eight rows share the cells
and differ in their read counts. -/
theorem blakeRow_relation (j : Fin 8) : Blake2sRelation (blakeRow j) := blake_cells_compress

/-- The `BLAKE2S` table is valid, for every count. -/
theorem walk_blake2sValid (c rA : K) (cnt : ℕ → K) : Blake2sRowsValid (walkW c rA cnt) := by
  intro r hr
  rw [blake2sRows, tableAt_five, blakeT_table, List.mem_map] at hr
  obtain ⟨rj, hrj, rfl⟩ := hr
  rw [List.mem_ofFn] at hrj
  obtain ⟨j, rfl⟩ := hrj
  rw [rawRow, blake2sRowAt_toElements]
  exact blakeRow_relation j

/-- The two public words sit at `g^0` and `g^1` of the image the data names. -/
theorem walk_word0 (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW c rA cnt).data).2.read (gpow 0) = some mulInput.word0 := by
  rw [data_eq, walk_imageOf]
  exact read_at 0 mulInput.word0

theorem walk_word1 (c rA : K) (cnt : ℕ → K) :
    (imageOf (walkW c rA cnt).data).2.read (gpow 1) = some mulInput.word1 := by
  rw [data_eq, walk_imageOf]
  exact read_at 1 mulInput.word1

/-- The honest witness satisfies the constraint statement. -/
theorem walk_satisfiedBy : SatisfiedBy walkProg mulInput (walkW 1 g memCnt) where
  public_input_eq := rfl
  constraints := walk_constraints 1 g memCnt
  state_balanced := walk_state_balanced
  mem_balanced := walk_mem_balanced
  bytecode_balanced := walk_bytecode_balanced
  counts_nonzero := walk_countsNonzero
  caps := walk_caps 1 g memCnt
  index_columns := walk_indexColumns 1 g memCnt
  seed_rows := walk_seedRows 1 g memCnt
  bytecode_rows := walk_bytecodeRows 1 g memCnt
  blake2s_valid := walk_blake2sValid 1 g memCnt
  word0_eq := walk_word0 1 g memCnt
  word1_eq := walk_word1 1 g memCnt

/-! ## The witness represents the trace -/

/-- Each of the run's four steps is one row's state pull and push. -/
theorem walk_regs_embed :
    ∀ k (hk : k + 1 < walkTrace.regs.length),
      RowSteps (walkW 1 g memCnt) walkTrace.regs[k] walkTrace.regs[k + 1] := by
  intro k hk
  have hk' : k < 4 := by rw [walk_regs] at hk; exact Nat.lt_of_succ_lt_succ hk
  simp only [walk_regs]
  interval_cases k
  · show RowSteps (walkW 1 g memCnt) ⟨1, 1⟩ ⟨gpow 1, 1⟩
    exact ⟨setT 1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      rawRow (setRow0 1), List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW 1 g memCnt) ⟨gpow 1, 1⟩ ⟨gpow 2, 1⟩
    exact ⟨setT 1, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      rawRow setRow1, List.mem_cons_of_mem _ List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW 1 g memCnt) ⟨gpow 2, 1⟩ ⟨gpow 3, 1⟩
    exact ⟨mulT g, List.mem_cons_of_mem _ List.mem_cons_self, rawRow (mulRow g),
      List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩
  · show RowSteps (walkW 1 g memCnt) ⟨gpow 3, 1⟩ ⟨gpow 31, 1⟩
    exact ⟨jumpT, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))), jumpRaw jumpRow3, List.mem_cons_self,
      by rw [rowMessagesOn_eq]; decide +kernel, by rw [rowMessagesOn_eq]; decide +kernel⟩

/-- A witness over the fixture's data whose rows step the trace represents it. Stated over a
destructured witness, so that its `data` is the constant `walkData` and no field is compared
against a projection of the witness. -/
theorem represents_of {tables : List (Air.Flat.Table K)} {pi : PublicIO K} {h1 h2 h3}
    (hregs : ∀ k (hk : k + 1 < walkTrace.regs.length),
      RowSteps (⟨tables, walkData, pi, h1, h2, h3⟩ : EnsembleWitness (leanIsaEnsemble walkProg))
        walkTrace.regs[k] walkTrace.regs[k + 1]) :
    AssignmentRepresents (⟨tables, walkData, pi, h1, h2, h3⟩ :
      EnsembleWitness (leanIsaEnsemble walkProg)) walkTrace where
  κ_eq := walk_logSize
  image_eq := fun i hi ↦ walk_image_apply' i (by rw [walk_logSize]; exact hi)
  regs_embed := hregs

/-- The honest witness represents the trace: the completeness instance for this program,
by hand. -/
theorem walk_represents : AssignmentRepresents (walkW 1 g memCnt) walkTrace :=
  represents_of walk_regs_embed

/-- The completeness instance for this program: the trace is a valid execution, the
witness satisfies the statement and represents the trace. -/
theorem walk_t1_instance : ValidExecution walkProg mulInput walkTrace ∧
    SatisfiedBy walkProg mulInput (walkW 1 g memCnt) ∧
      AssignmentRepresents (walkW 1 g memCnt) walkTrace :=
  ⟨⟨walk_boundary, walk_run⟩, walk_satisfiedBy, walk_represents⟩

/-- The image the witness names is the trace's, as one equality. -/
example : imageOf (walkW 1 g memCnt).data = ⟨minLogMem, walkImage⟩ :=
  assignmentRepresents_image walk_represents

/-! ## Rejections -/

/-- A wrong finalize count: cell `4` is read once, its finalize count `1` instead of `g`. -/
def wrongCnt (i : ℕ) : K := if i = 4 then 1 else memCnt i

theorem wrongCnt_of_ge {i : ℕ} (h : 29 ≤ i) : wrongCnt i = 1 := by
  unfold wrongCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- Nothing checks the finalize counts (§6.2): the block accepts the row, and the bus does not
balance. -/
example : ¬ BalancedPair (walkW 1 g wrongCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff 1 g wrongCnt fun _ ↦ wrongCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

/-- The finalize counts of a read count `0` at cell `2`: the first `SET_CONSTANT` row's read
pulls and pushes `(g^2, 0, x)`, the product row's read is then the first, and the cell is
finalized at `g`. -/
def zeroCnt (i : ℕ) : K := if i = 2 then g else memCnt i

theorem zeroCnt_of_ge {i : ℕ} (h : 29 ≤ i) : zeroCnt i = 1 := by
  unfold zeroCnt
  rw [ite_eq_right (by omega), memCnt_of_ge h]

/-- The zero-count witness balances the memory pair: a pull and a push of one tuple cancel,
which is what the count product exists to reject (§6.2 "The count product", Theorem 6.4). -/
theorem zero_mem_balanced : BalancedPair (walkW 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw := by
  rw [mem_balanced_iff 0 1 zeroCnt fun _ ↦ zeroCnt_of_ge]
  simp only [table_interactions_eq]
  decide +kernel

theorem zero_state_balanced :
    BalancedPair (walkW 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter zeroCnt StatePush.toRaw (by decide) (by decide),
    memT_filter zeroCnt StatePull.toRaw (by decide) (by decide),
    bcT_filter StatePush.toRaw (by decide) (by decide),
    bcT_filter StatePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

theorem zero_bytecode_balanced :
    BalancedPair (walkW 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw := by
  unfold BalancedPair messagesOn
  simp only [EnsembleWitness.interactions, EnsembleWitness.allTables, walkW, mkW,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append, List.map_append,
    memT_filter zeroCnt BytecodePush.toRaw (by decide) (by decide),
    memT_filter zeroCnt BytecodePull.toRaw (by decide) (by decide)]
  simp only [table_interactions_eq]
  decide +kernel

/-- The count product is load-bearing: the zero-count witness satisfies every other conjunct
of `SatisfiedBy` and fails `CountsNonzero` (§6.2 "The count product"). -/
theorem zero_count_witness :
    (walkW 0 1 zeroCnt).publicInput = PublicIO.ofInput mulInput ∧
    (walkW 0 1 zeroCnt).Constraints ∧
    BalancedPair (walkW 0 1 zeroCnt) StatePull.toRaw StatePush.toRaw ∧
    BalancedPair (walkW 0 1 zeroCnt) MemPull.toRaw MemPush.toRaw ∧
    BalancedPair (walkW 0 1 zeroCnt) BytecodePull.toRaw BytecodePush.toRaw ∧
    Caps (walkW 0 1 zeroCnt) ∧ IndexColumnsAreRowIndices (walkW 0 1 zeroCnt) ∧
    SeedRowsAreTheImage (walkW 0 1 zeroCnt) ∧
    BytecodeRowsAreTheProgram walkProg (walkW 0 1 zeroCnt) ∧
    Blake2sRowsValid (walkW 0 1 zeroCnt) ∧
    (imageOf (walkW 0 1 zeroCnt).data).2.read (gpow 0) = some mulInput.word0 ∧
    (imageOf (walkW 0 1 zeroCnt).data).2.read (gpow 1) = some mulInput.word1 ∧
    ¬ CountsNonzero (walkW 0 1 zeroCnt) :=
  ⟨rfl, walk_constraints 0 1 zeroCnt, zero_state_balanced, zero_mem_balanced,
    zero_bytecode_balanced, walk_caps 0 1 zeroCnt, walk_indexColumns 0 1 zeroCnt,
    walk_seedRows 0 1 zeroCnt, walk_bytecodeRows 0 1 zeroCnt, walk_blake2sValid 0 1 zeroCnt,
    walk_word0 0 1 zeroCnt, walk_word1 0 1 zeroCnt, by
      unfold CountsNonzero
      simp only [walkW, mkW, table_interactions_eq]
      decide +kernel⟩

/-- A wrong digest: the executor's row with the low bit of `out1` flipped. -/
def wrongOut1 : E := E.ofLimbs (K.ofBits 0xf1b0679a15df60ba) (K.ofBits 0x0228c8d4ed9b3a24) 0
def blakeRow' : Blake2sRow K := { blakeRow 0 with out1 := cell wrongOut1 }

theorem blakeRow'_no_relation : ¬ Blake2sRelation blakeRow' := by
  show ¬ CompressCells _ _ _ _ _ _
  decide +kernel

def blakeT' : Air.Flat.Table K :=
  mkT blake2sTable (size Blake2sRow) ([blakeRow'].map rawRow) (rawRows_size [blakeRow'])

/-- The witness with the wrong digest in its `BLAKE2S` table (one row; the caps are not the
point). -/
def digestW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT', memT memCnt, bcT]

/-- The compression is checked (§8.5): the wrong digest fails `Blake2sRowsValid`. It fails no
constraint: the table has none (`blake2s_constraints`). -/
example : ¬ Blake2sRowsValid digestW := fun h ↦
  blakeRow'_no_relation (by
    have hrel := h (rawRow blakeRow') (by
      show rawRow blakeRow' ∈ (tableAt digestW 5).table
      exact List.mem_cons_self)
    rwa [rawRow, blake2sRowAt_toElements] at hrel)

/-- The memory block with its index column shifted by one row. -/
def memRowArrShift (i : Fin (2 ^ minLogMem)) : Array K :=
  (toElements (⟨gpow (i + 1), memCnt i,
    #v[(walkImage i).limb 0, (walkImage i).limb 1, (walkImage i).limb 2]⟩ : MemRow K)).toArray

def memTShift : Air.Flat.Table K :=
  mkT memTable (size MemRow) (List.ofFn memRowArrShift) (by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact Vector.size_toArray _)

def idxW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT, memTShift, bcT]

theorem idxW_memBlockRows : memBlockRows idxW = List.ofFn memRowArrShift := by
  rw [memBlockRows, show tableAt idxW 6 = memTShift from rfl]
  dsimp only [memTShift, mkT]

/-- The index column is checked (§6.5): row `0` carrying `g^1` fails
`IndexColumnsAreRowIndices`. -/
example : ¬ IndexColumnsAreRowIndices idxW := fun h ↦ by
  have h0 := h 0 (by rw [idxW_memBlockRows, List.length_ofFn]; decide)
  simp only [idxW_memBlockRows, List.getElem_ofFn, memRowArrShift, memRowAt_toElements] at h0
  revert h0
  decide +kernel

/-- The public words are checked (§8.2): `input₀ = 3` in place of `1` fails `word0_eq`. -/
example : ¬ SatisfiedBy walkProg ⟨![K.ofBits 3, 0, K.ofBits 2, 0]⟩ (walkW 1 g memCnt) := fun h ↦ by
  have h0 := h.word0_eq
  rw [walk_word0] at h0
  have h1 := congrArg (fun o : Option E ↦ (o.getD 0).limb 0) h0
  revert h1
  decide +kernel

/-- A three-row `SET_CONSTANT` table, not a power of two. -/
def setT3 : Air.Flat.Table K :=
  mkT setTable (size SetRow) ([setRow0 1, setRow1, setRow1].map rawRow)
    (rawRows_size [setRow0 1, setRow1, setRow1])

def heightW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW [xorT, mulT g, setT3, derefT, jumpT, blakeT, memT memCnt, bcT]

/-- A row count that is not a power of two is within the caps (`crates/verifier/src/layout.rs`,
`build_layout`, at `3a37fb6e1`: a table's height is the least power of two holding its rows). -/
example : ∀ t ∈ heightW.tables, t.table.length ≤ 2 ^ maxLogRows := by
  intro t ht
  simp only [heightW, mkW, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [blakeT_table, List.length_map, List.length_ofFn]; decide
  · rw [memT_table, List.length_ofFn]; decide
  · rw [bcT_table, List.length_ofFn]; decide

/-- Four `BLAKE2S` rows. -/
def blakeT4 : Air.Flat.Table K :=
  mkT blake2sTable (size Blake2sRow)
    ((List.ofFn fun j : Fin 4 ↦ blakeRow (j.castAdd 4)).map rawRow)
    (rawRows_size (List.ofFn fun j : Fin 4 ↦ blakeRow (j.castAdd 4)))

theorem blakeT4_table :
    blakeT4.table = (List.ofFn fun j : Fin 4 ↦ blakeRow (j.castAdd 4)).map rawRow := by
  dsimp only [blakeT4, mkT]

def floorW : EnsembleWitness (leanIsaEnsemble walkProg) :=
  mkW [xorT, mulT g, setT 1, derefT, jumpT, blakeT4, memT memCnt, bcT]

/-- There is no `BLAKE2S` floor: four rows are within the caps. -/
example : (tableAt floorW 5).table.length ≤ 2 ^ maxLogRows := by
  rw [show tableAt floorW 5 = blakeT4 from rfl, blakeT4_table, List.length_map, List.length_ofFn]
  decide

end LeanVMTests.Arithmetization.Statement
