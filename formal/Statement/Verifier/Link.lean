module

public import Statement.Verifier.RingSwitch

/-!
# The link (`crates/verifier/src/link.rs`)

Hotwire: one-hot pointer links checked by two chained sum-checks. One sum-check runs over the index
`j` (the index side), the next over the rows `u`, then the pointer columns `q` (the row side). The
index side checks the memory and the program by agreement, and the state by one identity over the
cycles; the row side checks that the scattered arrays are the pointers the rows commit, and that
every executed pointer is one-hot (the mirror test).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-- `MAX_WIDTH`: the widest pointer one word holds (`link.rs`). -/
def maxPointerWidth : ℕ := 24

/-- `WINDOW_BITS`: the lowest chunk's bits, a pointer's window, the cells a shifted read reaches
(`link.rs`). -/
def windowBits : ℕ := 4

/-- How a `width`-bit pointer splits into chunks (`Chunks`, `link.rs`): the lowest
`min(WINDOW_BITS, width)` bits, then the fewest chunks whose one-hot blocks fit the rest of 64 bits,
widths differing by at most one, the wider first. Chunk `i` covers index bits from `indexShifts[i]`
and word bits from `wordShifts[i]`. -/
structure Chunks where
  /-- `width`: the pointer's bits. -/
  width : ℕ
  /-- `widths`: each chunk's bits. -/
  widths : List ℕ
  /-- `index_shifts`: each chunk's first index bit. -/
  indexShifts : List ℕ
  /-- `word_shifts`: each chunk's first word bit. -/
  wordShifts : List ℕ
  deriving Inhabited, DecidableEq

/-- The starts of consecutive runs of these sizes, from `0` (the `scan` of `Chunks::new`'s
`prefix`, `link.rs`). -/
def exclusivePrefix (sizes : List ℕ) : List ℕ :=
  (sizes.foldl (fun (acc : List ℕ × ℕ) size ↦ (acc.1 ++ [acc.2], acc.2 + size)) ([], 0)).1

/-- `Chunks::new(width)` (`link.rs`); `none` where the Rust returns `AnnouncedTableSizes`, a width
outside `1..=MAX_WIDTH`. The lowest chunk takes `min(WINDOW_BITS, width)` bits; the rest split
into the fewest `d` chunks, `rest / d` bits each and one more for the first `rest % d`, whose
one-hot blocks fit in `64 - 2^low` bits (one chunk per bit always fits, as the Rust's `expect`
says). -/
def Chunks.new (width : ℕ) : Option Chunks :=
  if 1 ≤ width ∧ width ≤ maxPointerWidth then
    let low := min width windowBits
    let rest := width - low
    let tail : List ℕ :=
      if 0 < rest then
        ((((List.range rest).map (· + 1)).map fun d ↦
            (List.range d).map fun i ↦ rest / d + if i < rest % d then 1 else 0).find?
          fun widths ↦ decide ((widths.map (2 ^ ·)).sum ≤ 64 - 2 ^ low)).getD []
      else []
    let widths := low :: tail
    some ⟨width, widths, exclusivePrefix widths, exclusivePrefix (widths.map (2 ^ ·))⟩
  else none

/-- `Chunks::d()`: the chunk count (`link.rs`). -/
def Chunks.d (chunks : Chunks) : ℕ := chunks.widths.length

/-- `Chunks::part(point, i)`: chunk `i`'s coordinates of an index point (`link.rs`). -/
def Chunks.part (chunks : Chunks) (point : List E) (i : ℕ) : List E :=
  (point.drop (chunks.indexShifts.getD i 0)).take (chunks.widths.getD i 0)

/-- `window_shift(e, s)` (`link.rs`): `T_s(v) = e(v + s)` where `v + s < n`, zero elsewhere, chunk
`0` read `s` cells further inside its window from its eq table `e` over `n` values. -/
def linkWindowShift (e : List E) (s : ℕ) : List E :=
  (List.range e.length).map fun v ↦ e.getD (v + s) 0

/-- The functionals a pointer word is read with (`Functionals`, `link.rs`), as tables over each
chunk's values: `D_i` at the index point `r` and at `1 + r`, then chunk `0`'s `T_s` per shift `s`
from `1` to `max_shift`. A one-hot pointer `σ` read `s` cells further is
`T_s(e_0)·Π_{i ≥ 1} D_i(e_i) = eq(r, σ + s)·[σ_0 + s < 2^{w_0}]`: a read past its window is zero. -/
structure Functionals where
  /-- `tables`: `(chunk, table)` per value, in order. -/
  tables : List (ℕ × List E)
  /-- `d`: the chunk count. -/
  d : ℕ
  /-- `mirrors`: `π_{w_i}(r_i) = Π_h r_h·(1 + r_h)` over chunk `i`'s coordinates of `r`. -/
  mirrors : List E
  deriving Inhabited

/-- `Functionals::new(chunks, r, max_shift)` (`link.rs`). The table at `1 + r_i` is the one at
`r_i` reversed: `eq(1 + r_i, v) = eq(r_i, v')` for `v'` the value `v` with its bits flipped. -/
def Functionals.new (chunks : Chunks) (r : List E) (maxShift : ℕ) : Functionals :=
  let d := chunks.d
  let eq := (List.range d).map fun i ↦ eqKernel (chunks.part r i)
  let atR := (List.range d).zip eq
  let tables := atR ++ atR.map (fun (i, e) ↦ (i, e.reverse)) ++
    (List.range maxShift).map fun s ↦ (0, linkWindowShift (eq.headD []) (s + 1))
  let mirrors := (List.range d).map fun i ↦ prodE ((chunks.part r i).map fun x ↦ x * (1 + x))
  ⟨tables, d, mirrors⟩

/-- `Functionals::values(chunks, slices)` (`link.rs`): the values of a word whose `64` bit-slices
are `slices`, each functional linear in the bits. -/
def Functionals.values (f : Functionals) (chunks : Chunks) (slices : List E) : List E :=
  f.tables.map fun (i, table) ↦
    sumE (List.zipWith (· * ·) table (slices.drop (chunks.wordShifts.getD i 0)))

/-- `Functionals::summand(coef, shifts, values, certs)` (`link.rs`):
`(c·D_0 + Σ_s c_s·T_s)·Π_{i ≥ 1} D_i + Σ_i e_i·(D_i(r_i)·D_i(1 + r_i) + π_i)` from a word's
values: the pointer at `r`, the pointer read `s` further, and the mirror certificate. `shifts[s − 1]`
is `c_s`. -/
def Functionals.summand (f : Functionals) (coef : E) (shifts values certs : List E) : E :=
  let d := f.d
  let rest := prodE ((values.drop 1).take (d - 1))
  let low := coef * values.getD 0 0 + sumE (List.zipWith (· * ·) shifts (values.drop (2 * d)))
  let cert := sumE ((List.range d).map fun i ↦
    certs.getD i 0 * (values.getD i 0 * values.getD (d + i) 0 + f.mirrors.getD i 0))
  low * rest + cert

/-- `less_than(point, n)` (`link.rs`): `LT_n(point)`, the multilinear extension of `[j < n]`, for
`n ≤ 2^|point|`. -/
def lessThan (point : List E) (n : ℕ) : E := 1 + paddingWeight point n

/-- `shift_eq(zeta, r)` (`link.rs`): `Σ_{j + 1 < 2^n} eq(r, j)·eq(ζ, j + 1)`, the shift of
`eq(ζ, ·)` by one at `r`, as a sum over the lowest zero bit `k` of `j`, below which `j` is all ones
and `j + 1` all zeros; the loop over `zeta.iter().zip(r)` from `(shift, carry) = (0, 1)`. -/
def linkShiftEq (zeta r : List E) : E :=
  ((zeta.zip r).foldl (fun acc zx ↦ (acc.1 * (1 + zx.1 + zx.2) + acc.2 * (1 + zx.2) * zx.1,
    acc.2 * (zx.2 * (1 + zx.1)))) ((0 : E), (1 : E))).1

/-- `eq_at(point, j)` (`link.rs`): `eq(point, j)` at the integer `j`, LSB-first. -/
def linkEqAt (point : List E) (j : ℕ) : E :=
  point.zipIdx.foldl (fun acc p ↦ acc * if j >>> p.2 % 2 = 1 then p.1 else 1 + p.1) 1

/-- `prefix_sum(low, high, n)` (`link.rs`): `Σ_{g < n} Π_h e_h(g_h)` with `e_h(0) = low[h]` and
`e_h(1) = high[h]`, for `n ≤ 2^len`: a walk over the binary digits of `n`, from the top. -/
def prefixSum (low high : List E) (n : ℕ) : E :=
  let len := low.length
  let full := (List.range len).foldl
    (fun acc h ↦ acc ++ [acc.getD h 0 * (low.getD h 0 + high.getD h 0)]) [(1 : E)]
  if 2 ^ len ≤ n then full.getD len 0
  else ((List.range len).reverse.foldl (fun (acc : E × E) h ↦
      if n >>> h % 2 = 1 then (acc.1 + acc.2 * low.getD h 0 * full.getD h 0, acc.2 * high.getD h 0)
      else (acc.1, acc.2 * low.getD h 0)) (0, 1)).1

/-- `omega_at(theta, tau, chi, n)` (`link.rs`): `ω_F(χ) = θ_F·Σ_{u < n} eq(τ, u)·eq(χ, u)`, the row
weight at the table's row point. -/
def omegaAt (theta : E) (tau chi : List E) (n : ℕ) : E :=
  theta * prefixSum (List.zipWith (fun t x ↦ (1 + t) * (1 + x)) tau chi)
    (List.zipWith (fun t x ↦ t * x) tau chi) n

/-- `round_coefficients(d)` (`link.rs`): the coefficients of a row round and of a pointer-column
round. -/
def roundCoefficients (d : ℕ) : ℕ × ℕ := (max (d + 2) 4 + 1, max (d + 1) 3 + 1)

/-- What the program side weighs each opcode's slots by, per table `F` and slot `s` (`SlotWeights`,
`link.rs`): on the rows' weight `ω` (`omega`, and `pc` for a slot read times `pc`), and on `ω·fp`
(`frame`); `2^BYTECODE_SLOT_BITS` entries a table. -/
structure SlotWeights where
  /-- `omega`: on `ω`. -/
  omega : List (List E)
  /-- `pc`: on `ω`, for a slot read times `pc`. -/
  pc : List (List E)
  /-- `frame`: on `ω·fp`. -/
  frame : List (List E)
  deriving Inhabited

/-- `weights[s] += value`. -/
def addAtSlot (weights : List E) (s : ℕ) (value : E) : List E :=
  weights.set s (weights.getD s 0 + value)

/-- One table's `omega`, `pc` and `frame` rows of `slot_weights` (`link.rs`). -/
def tableSlotWeights (table : Table) (slot : List E) (gamma : E × E) (mu : List E)
    (etaMem etaBc : E) : List E × List E × List E :=
  let zero := List.replicate (2 ^ bytecodeSlotBits) (0 : E)
  let links := table.links
  let omega := zero.set 3 (etaBc * slot.getD 3 0)
  let omega := links.bytecodeLink.operands.foldl (fun omega (slots, _) ↦
    slots.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (slots.headD 0) 0)) omega) omega
  (links.memory.zip mu).foldl (fun (acc : List E × List E × List E) (access, m) ↦
    let m := etaMem * m
    let frame := match access.frame with
      | some (s, e) => addAtSlot acc.2.2 s (m * gamma.1 * gpow e)
      | none => acc.2.2
    access.reads.foldl (fun (acc : List E × List E × List E) read ↦
      match read with
      | .word _ _ => acc
      | .slot s scale => (addAtSlot acc.1 s (m * gamma.2 * scale), acc.2.1, acc.2.2)
      | .frame s scale => (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * gamma.2 * scale))
      | .pc s scale => (acc.1, addAtSlot acc.2.1 s (m * gamma.2 * scale), acc.2.2))
      (acc.1, acc.2.1, frame)) (omega, zero, zero)

/-- `slot_weights(tables, slot, gamma, mu, eta_mem, eta_bc)` (`link.rs`): the program side's
weights: the opcode on every row; each operand equation's slots under its first slot's challenge;
and each access's reads of its instruction, under `η_mm·μ` and the address or word challenge.
`gamma` is `(γ_addr, γ_word)`. -/
def slotWeights (tables : List Table) (slot : List E) (gamma : E × E) (mu : List (List E))
    (etaMem etaBc : E) : SlotWeights :=
  let rows := tables.zipIdx.map fun (table, t) ↦
    tableSlotWeights table slot gamma (mu.getD t []) etaMem etaBc
  ⟨rows.map (·.1), rows.map (·.2.1), rows.map (·.2.2)⟩

/-- What the link leaves on the commitment, and where it read the program (`LinkEnd`, `link.rs`):
the memory term at `r` (the memory's low point, each limb's scale, the value), each table's row
point and its non-pointer columns' values there (`TableValues`: local column and value), the
pointer columns' bit-slices as one ring-switch claim, and the point the link reads the stacked
program at. The Rust's `values_at_r` and `bit_slices`, stream positions the `Summary` reports to a
prover, are not part of the verifier's walk. -/
structure LinkEnd where
  /-- `memory.0`: the memory's low point. -/
  memoryPoint : List E
  /-- `memory.1`: each memory limb's scale. -/
  memoryScales : E × E
  /-- `memory.2`: the memory term's value at `r`. -/
  memoryValue : E
  /-- `columns`: per table, its row point and its non-pointer columns' values there. -/
  columns : List (List E × List (ℕ × E))
  /-- `ring`: the pointer columns' 64 bit-slices, one piece per pointer column. -/
  ring : RingClaim
  /-- `bytecode_point`: where the link splits the program, the index point's program coordinates. -/
  bytecodePoint : List E
  deriving Inhabited

/-- `pointer_width(log_memory, log_bytecode, cycles)` (`link.rs`): the pointer width every
execution of these sizes takes, the cycle count's bits, the memory's and the program's, at least
one. -/
def pointerWidth (logMemory logBytecode cycles : ℕ) : ℕ :=
  max (max (max (bitLength cycles) logMemory) logBytecode) 1

/-- `packed_challenges(tables, n_rows, width)` (`link.rs`): how many challenges the link draws
eight to a permutation, after `θ_0`: `θ`'s rest, `γ`, `μ`, `α`, `η` and `ε`, then `τ` over the
tallest table's `n_rows` row variables, `ζ` over the pointer width and `ν` over its chunks (none
for a width `Chunks::new` refuses). -/
def packedChallenges (tables : List Table) (nRows width : ℕ) : ℕ :=
  let nAccesses := (tables.map (·.links.memory.length)).sum
  let nPointers := (tables.map (·.links.pointers.length)).sum
  let d := ((Chunks.new width).map Chunks.d).getD 0
  (nTables - 1) + 5 + nAccesses + bytecodeSlotBits + 2 + nPointers + nRows + width + d

/-- What the row side's values make of the summand at the row point, accumulated table by table
in `verify_link`'s loop (`link.rs`): the pointer's coefficient `coef`, the shifted reads'
`shifts`, the certificate's weight, the base terms, the ring pieces, the pointer column count `q`
so far, each table's point and sent values, and the values not yet read. -/
structure LinkRowSide where
  /-- `coef`. -/
  coef : E
  /-- `shifts`: `c_s` at `s - 1`. -/
  shifts : List E
  /-- `cert_weight`. -/
  certWeight : E
  /-- `base`. -/
  base : E
  /-- `pieces`. -/
  pieces : List RingPiece
  /-- `q`: the pointer columns so far. -/
  q : ℕ
  /-- `columns`: each table's row point and sent values. -/
  columns : List (List E × List (ℕ × E))
  /-- `sent_values`: the values not yet read. -/
  sent : List E
  deriving Inhabited

/-- `verify_link(layout, transcript)` (`link.rs`): the links of the execution `layout` announces,
from right after the commitment's out-of-domain sample. **Where the verifier meets the program**:
`bytecodeSplit layout.bytecode point pc` gives the program's split at the link's point over the
instructions, at the pairs `pc_slots(tables)` reads times `pc`, as the Rust calls
`layout.bytecode.split`; the deployed verifier computes it (`computedSplit`, `Bytecode::split`), an
aggregate's verifier holds it to a child's fresh claim (`freshSplit`).

In order: a grind for the challenges' error (a degree-`m + 3 + BYTECODE_SLOT_BITS` polynomial on the row
side, `m` the tallest table's row variables, and the `width + 1` of the index side), `θ_0` from the
grind's permutation, the rest eight to a permutation (`packedChallenges`); the index side's
sum-check over the pointer width at three coefficients a round, from
`eq(ζ, 0)·ŝ_init + eq(ζ, T)·ŝ_fin`; the memory term at `r`, `m1`; five fresh coefficients (the
certificate's and `JUMP`'s identities'); the row side's sum-check over the rows and over the pointer
columns; one packed message of the non-pointer values at the row point and the pointer words' `64`
bit-slices; the terminal check. The Rust computes the split and the terminal check only in its
checked mode; the program is the checked one. A pointer column always has a placement, as the
Rust's `expect` says. -/
def verifyLink (bytecodeSplit : List K → List E → List (ℕ × ℕ) → VerifierProgram Split)
    (layout : Layout) :
    VerifierProgram LinkEnd := do
  let tables := layout.tables
  let heights := layout.tableLogHeights
  let rows := layout.tableRows
  let cycles := rows.foldl (· + ·) 0
  let chunks ← liftOption (Chunks.new (pointerWidth layout.logMemory layout.logBytecode cycles))
  let width := chunks.width
  let d := chunks.d
  let pointers := tables.map (·.links.pointers)
  let nPointers := (pointers.map List.length).sum
  let maxShift := tables.foldl (fun m t ↦ max m t.links.maxShift) 0
  -- The challenges, after the grind their error asks for.
  let nRows := heights.foldl max 0
  VerifierProgram.grindProofOfWork (grindingBits (max (nRows + 3 + bytecodeSlotBits) (width + 1)))
  let theta0 ← VerifierProgram.sampleChallenge
  let drawn ← VerifierProgram.sampleChallengesPacked (packedChallenges tables nRows width)
  let theta := theta0 :: drawn.take (nTables - 1)
  let drawn := drawn.drop (nTables - 1)
  let gammaState := drawn.take 2
  let drawn := drawn.drop 2
  -- On the address, the word and the presence coordinate; a word `lo + y·hi` takes `γ_word·y` on
  -- its high limb.
  let g := drawn.take 3
  let drawn := drawn.drop 3
  let gammaMem : List E := [g.getD 0 0, g.getD 1 0, g.getD 1 0 * eY, g.getD 2 0]
  let (mu, drawn) := tables.foldl (fun (acc : List (List E) × List E) t ↦
    (acc.1 ++ [acc.2.take t.links.memory.length], acc.2.drop t.links.memory.length)) ([], drawn)
  let alpha := drawn.take bytecodeSlotBits
  let drawn := drawn.drop bytecodeSlotBits
  let etaMem := drawn.getD 0 0
  let etaBc := drawn.getD 1 0
  let drawn := drawn.drop 2
  -- The mirror certificates' coefficients: pointer column `q`'s chunk `c` takes `ε_q·ν_c`.
  let eps := drawn.take nPointers
  let drawn := drawn.drop nPointers
  let tau := drawn.take nRows
  let drawn := drawn.drop nRows
  let zeta := drawn.take width
  let nu := (drawn.drop width).take d
  let slot := eqKernel alpha
  -- `ŝ_γ = 1 + γ_pc·pc + γ_fp·fp`: the constant component counts the rows on each cycle.
  let stateGamma := fun (pc fp : E) ↦ 1 + gammaState.getD 0 0 * pc + gammaState.getD 1 0 * fp
  let sInit := stateGamma 1 1
  let sFin := stateGamma (gpow (2 ^ layout.logBytecode - 1)) 1
  -- The index side, then the memory term at `r` and the fresh coefficients.
  let claim := linkEqAt zeta 0 * sInit + linkEqAt zeta cycles * sFin
  let (r, claim) ← sumcheck claim 3 (List.replicate width none)
  let m1 ← VerifierProgram.readScalar
  let fresh ← VerifierProgram.sampleChallengesPacked 5
  let cert := fresh.getD 0 0
  let jump := fresh.drop 1
  let below := fun (k : ℕ) ↦ prodE ((r.drop (min k width)).map (1 + ·))
  let yMem := gammaMem.getD 0 0 * indexMle r + gammaMem.getD 3 0 * below layout.logMemory +
    gammaMem.getD 1 0 * m1
  let bytecodePoint := r.take layout.logBytecode
  -- The program side's targets at `r`: `X_ω` on the rows' weight, `P_fp` on `ω·fp`. Both weigh an
  -- instruction's slots by its opcode.
  let weights := slotWeights tables slot (gammaMem.getD 0 0, gammaMem.getD 1 0) mu etaMem etaBc
  let split ← bytecodeSplit layout.bytecode (r.take layout.logBytecode) (pcSlots tables)
  let (program, frameProgram) := (List.range nTables).foldl (fun (acc : E × E) t ↦
    let omega := weights.omega.getD t []
    let pc := weights.pc.getD t []
    let frame := weights.frame.getD t []
    let slots := split.slots.getD t []
    let pcs := split.pc.getD t []
    let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
    ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
      (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
        acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0)
  let belowBc := below layout.logBytecode
  let xBc := etaBc * slot.getD 1 0 * indexMle r + belowBc * (etaBc * slot.getD 2 0 + program)
  let pFp := belowBc * frameProgram
  let eq0R := below 0
  -- The state identity's weights at `r`: on `A` and on `B`.
  let eqZetaR := eqEval zeta r
  let shiftZetaR := linkShiftEq zeta r
  -- The row side.
  let (rowCount, columnCount) := roundCoefficients d
  let (chi, claim) ← sumcheck claim rowCount (List.replicate nRows none)
  let qVars := log2Ceil nPointers
  let (qPoint, claim) ← sumcheck claim columnCount (List.replicate qVars none)
  let eqQ := eqKernel qPoint
  -- The values at the row point, then the pointer words' bit-slices, one message read eight
  -- scalars a permutation.
  let nonPointer := fun (t : ℕ) (table : Table) ↦
    (List.range table.width).filter fun c ↦ !(pointers.getD t []).contains c
  let nValues := (tables.zipIdx.map fun (table, t) ↦ (nonPointer t table).length).sum
  let message ← VerifierProgram.readScalarsPacked (nValues + kBits)
  let slices := message.drop nValues
  -- What the values make of the summand at the row point.
  let rowSide := tables.zipIdx.foldl (fun (acc : LinkRowSide) (table, t) ↦
    let height := heights.getD t 0
    let tableRows := rows.getD t 0
    let point := chi.take height
    let corner := prodE ((chi.drop height).map (1 + ·))
    let columns := nonPointer t table
    let sent := columns.zip (acc.sent.take columns.length)
    let values := (List.range table.width).map fun c ↦ (sent.lookup c).getD 0
    let col := fun (c : ℕ) ↦ values.getD c 0
    let links := table.links
    let muT := mu.getD t []
    let omega := omegaAt (theta.getD t 0) (tau.take height) point tableRows
    let act := lessThan point tableRows
    let state := links.stateLink
    let sHat := stateGamma (col state.pc) (col state.fp)
    let sNext := stateGamma (state.next.1.evaluate col) (state.next.2.evaluate col)
    -- The base terms: the payload under ω, and `JUMP`'s identities on every row. An access's
    -- committed part: its reads are the pointers' coefficients.
    let accessValue := fun (a : Access) ↦
      gammaMem.getD 0 0 * a.address.evaluate col + gammaMem.getD 3 0 +
        gammaMem.getD 1 0 * a.value.evaluate col
    let bc := links.bytecodeLink
    let rBc := slot.getD 1 0 * col bc.pc + slot.getD 2 0 + slot.getD 3 0 * gpow bc.opcode +
      sumE (bc.operands.map fun (slots, f) ↦ slot.getD (slots.headD 0) 0 * f.evaluate col)
    let gateOf := fun (a : Access) ↦ (a.gate.map col).getD 1
    let memory := sumE ((links.memory.zip muT).map fun (a, m) ↦ m * gateOf a * accessValue a)
    let tableBase := omega * eq0R * (etaMem * memory + etaBc * rBc)
    let tableBase :=
      if 0 < table.nConstraints then
        let identities := table.constraints values
        let eqTau := eqEval (tau.take height) point
        tableBase + eqTau * sumE (List.zipWith (· * ·) jump identities)
      else tableBase
    -- The pointer columns' coefficients.
    let acc := (pointers.getD t []).zipIdx.foldl (fun (acc : LinkRowSide) (pointer, k) ↦
      let e := eqQ.getD acc.q 0 * corner
      let (coef, shifts) :=
        match k with
        | 0 => (acc.coef + e * act * (eqZetaR * sHat + shiftZetaR * sNext), acc.shifts)
        | 1 => (acc.coef + e * omega * (xBc + col state.fp * pFp), acc.shifts)
        | _ =>
          -- The word reads at this pointer weigh `word(r)`, the memory term.
          let coef := (links.memory.zip muT).foldl (fun coef (access, m) ↦
            access.reads.foldl (fun coef read ↦
              match read with
              | .word p scale =>
                if p = pointer then
                  coef + e * omega * etaMem * m * gammaMem.getD 1 0 * m1 * scale.evaluate col
                else coef
              | _ => coef) coef) acc.coef
          ((links.memory.zip muT).filter (·.1.pointer = pointer)).foldl
            (fun (cs : E × List E) (access, m) ↦
              let c := e * omega * gateOf access * etaMem * m * yMem
              match access.shift with
              | 0 => (cs.1 + c, cs.2)
              | s + 1 => (cs.1, addAtSlot cs.2 s c)) (coef, acc.shifts)
      let piece : RingPiece :=
        { placement :=
            some ((layout.placements.getD (globalColumnBases.getD t 0 + pointer) none).getD default)
          point := point
          scale := eqQ.getD acc.q 0 }
      { acc with
        coef := coef
        shifts := shifts
        certWeight := acc.certWeight + e * omega * eps.getD acc.q 0
        pieces := acc.pieces ++ [piece]
        q := acc.q + 1 })
      { acc with base := acc.base + corner * tableBase, sent := acc.sent.drop columns.length }
    { acc with columns := acc.columns ++ [(point, sent)] })
    ⟨0, List.replicate maxShift 0, 0, 0, [], 0, [], message.take nValues⟩
  let functionals := Functionals.new chunks r maxShift
  let values := functionals.values chunks slices
  let eq0Q := prodE (qPoint.map (1 + ·))
  let certs := nu.map fun n ↦ cert * rowSide.certWeight * n
  let last := functionals.summand rowSide.coef rowSide.shifts values certs + eq0Q * rowSide.base
  VerifierProgram.require (last = claim)
  let belowMem := below layout.logMemory
  return {
    memoryPoint := r.take layout.logMemory
    memoryScales := (belowMem, eY * belowMem)
    memoryValue := m1
    columns := rowSide.columns
    ring := ⟨rowSide.pieces, slices⟩
    bytecodePoint := bytecodePoint }

end LeanVM.Protocol.Verifier

end
