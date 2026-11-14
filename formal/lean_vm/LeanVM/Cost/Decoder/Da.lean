module

public import LeanVM.Cost.Decoder.Hints
public import LeanVM.Guest.Fast.Da
import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# The guest decoder's compiled chain: the DA matrix

`da_verify`'s witness off its callees' frames, keyed by the functions' indices
(`Guest.Fast.dvWitN`, equal to `Da.dvWit` at the frame map re-keyed by `decoderFunctionName`,
`Guest.Fast.dvWitN_eq`): the rows of the cells' symbols, compiled part by part. Staged, each frame
looked up once:

* the number of rows (a logarithm, `gLogD D`, the logarithm's tables `D` given, at most `DA_MAX_ROWS`,
  `daRowCount`, as `Da.dvRows`) computed once by `dvWitND` and passed to `dvWitNAt`;
* each column's frame (`dvColVN`) looked up once, its two words the rows read (`dvColWords`)
  kept in an array of the `128` columns (`dvCols`), built once by `dvWitNAt` and passed to
  `dvWitNCols`;
* each cell's blob-loop frame (`dvRowVW`, `da_verify_loop0`) looked up once, passed as a value to
  `cellSymsAt`;
* the powers of `g` taken in `K` (`ofK (g^i)`, `mulK`), not in `E`.

`dvWitNAt_eq : dvWitNCols r σ Vn (dvCols σ Vn) = …` is the unstaged witness (`dvSymsPNAt`), and
`dvWitND_tables : dvWitND discreteLogTables = dvWitN`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Extraction.Fast LeanVM.Protocol.Verifier

@[expose] public section

/-- The symbols, padded outside the matrix of `r` rows (`dvSymsPN`, `r` its logarithm). -/
def dvSymsPNAt (r : ℕ) (σ : Val) (Vn : NFrames) (i h : ℕ) : List E :=
  if i < r ∧ h < 128 then
    cellSymsOf (Vn (fn_idx% da_verify_cell) [dvColVN σ Vn h (.n 14)]
      [dvRowVN σ Vn i h (.n 6), dvRowVN σ Vn i h (.n 7), dvRowVN σ Vn i h (.n 8)])
  else List.replicate 128 0

/-! ## Each frame once -/

/-- A column's two words its blob loop reads (`14`, `15`), off its valuation. -/
def colWordsOf (v : Val) : E × E := (v (.n 14), v (.n 15))

/-- Column `h`'s two words, its frame looked up once. -/
def dvColWords (σ : Val) (Vn : NFrames) (h : ℕ) : E × E := colWordsOf (dvColVN σ Vn h)

/-- The `128` columns' words. -/
def dvCols (σ : Val) (Vn : NFrames) : Array (E × E) := ((List.range 128).map (dvColWords σ Vn)).toArray

/-- Blob `i`'s iteration of column `h`'s blob loop (`dvRowVN`), the column's words `cw` given. -/
def dvRowVW (σ : Val) (Vn : NFrames) (cw : E × E) (i h : ℕ) : Val :=
  Vn (fn_idx% da_verify_column_loop0) [ofK (Parameters.g ^ i), σ (.n 1), cw.1, σ (.n 22), ofK (Parameters.g ^ h), cw.2] []

/-- A cell's symbols off `da_verify_cell`'s frame, the blob loop's valuation given. -/
def cellSymsAt (Vn : NFrames) (c14 : E) (row : Val) : List E :=
  cellSymsOf (Vn (fn_idx% da_verify_cell) [c14] [row (.n 6), row (.n 7), row (.n 8)])

/-- Cell `(i, h)`'s symbols, the column's words given: its blob loop's frame looked up once. -/
def dvSymsCell (σ : Val) (Vn : NFrames) (cw : E × E) (i h : ℕ) : List E :=
  cellSymsAt Vn cw.1 (dvRowVW σ Vn cw i h)

/-- The symbols, padded outside the matrix of `r` rows, the columns' words given. -/
def dvSymsCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) (i h : ℕ) : List E :=
  if i < r ∧ h < 128 then dvSymsCell σ Vn (cols.getD h (0, 0)) i h else List.replicate 128 0

/-- `da_verify`'s witness, its `r` rows and its columns' words given. -/
def dvWitNCols (r : ℕ) (σ : Val) (Vn : NFrames) (cols : Array (E × E)) : LeanVM.Da.MatrixWitness :=
  ⟨daRows r (dvSymsCols r σ Vn cols)⟩

/-- `da_verify`'s witness, its `r` rows given (`dvWitN`): the columns' words built once. -/
def dvWitNAt (r : ℕ) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNCols r σ Vn (dvCols σ Vn)

theorem dvCols_getD (σ : Val) (Vn : NFrames) {h : ℕ} (hh : h < 128) :
    (dvCols σ Vn).getD h (0, 0) = (dvColVN σ Vn h (.n 14), dvColVN σ Vn h (.n 15)) := by
  simp [dvCols, dvColWords, colWordsOf, Array.getD_eq_getD_getElem?, hh]

theorem dvSymsCols_eq (r : ℕ) (σ : Val) (Vn : NFrames) (i h : ℕ) :
    dvSymsCols r σ Vn (dvCols σ Vn) i h = dvSymsPNAt r σ Vn i h := by
  unfold dvSymsCols dvSymsPNAt
  split
  · rename_i hc
    rw [dvCols_getD σ Vn hc.2]
    simp only [dvSymsCell, cellSymsAt, dvRowVW, dvRowVN, LeanVM.Guest.Value.gen_pow_eq_ofK]
  · rfl

/-- **The staged witness is the unstaged one.** -/
theorem dvWitNAt_eq (r : ℕ) (σ : Val) (Vn : NFrames) :
    dvWitNAt r σ Vn = ⟨daRows r (dvSymsPNAt r σ Vn)⟩ := by
  unfold dvWitNAt dvWitNCols
  have h1 : dvSymsCols r σ Vn (dvCols σ Vn) = dvSymsPNAt r σ Vn :=
    funext fun i ↦ funext fun h ↦ dvSymsCols_eq r σ Vn i h
  rw [h1]

/-- A count of rows, at most `DA_MAX_ROWS` (`dvRows`'s clamp). -/
def daRowCount (r : ℕ) : ℕ := if r ≤ guest_const% DA_MAX_ROWS then r else guest_const% DA_MAX_ROWS

theorem daRowCount_eq (r : ℕ) : daRowCount r = min r (guest_const% DA_MAX_ROWS) := by
  unfold daRowCount
  split <;> omega

theorem daRowCount_le (r : ℕ) : daRowCount r ≤ guest_const% DA_MAX_ROWS := by
  unfold daRowCount
  split <;> omega

/-- **`da_verify`'s witness** (`dvWitN`), the logarithm's tables `D` given: its rows counted
once, at most `DA_MAX_ROWS` (`daRowCount`). -/
def dvWitND (D : DiscreteLogTables) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  dvWitNAt (daRowCount (gLogD D (σ (.n 1)))) σ Vn

theorem dvWitND_tables : dvWitND discreteLogTables = dvWitN := by
  funext σ Vn
  unfold dvWitND
  rw [dvWitNAt_eq]
  unfold dvWitN dvSymsPNAt dvSymsPN dvRows
  rw [gLogD_tables, daRowCount_eq]

cost_compile dvColArgsC := LeanVM.Guest.B1.Da.dvColArgs
cost_compile cellSymsOfC := LeanVM.Guest.B1.Da.cellSymsOf
cost_compile daRowsC := LeanVM.Guest.B1.Da.daRows
cost_compile dvColVNC := dvColVN
cost_compile colWordsOfC := colWordsOf
cost_compile dvColWordsC := dvColWords
cost_compile dvColsC := dvCols
cost_compile dvRowVWC := dvRowVW
cost_compile cellSymsAtC := cellSymsAt
cost_compile dvSymsCellC := dvSymsCell
cost_compile dvSymsColsC := dvSymsCols
cost_compile dvWitNColsC := dvWitNCols
cost_compile dvWitNAtC := dvWitNAt
cost_compile daRowCountC := daRowCount
cost_compile dvWitNC := dvWitND

end

end LeanVM.Cost.Decoder
