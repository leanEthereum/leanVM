module

public import LeanVM.Cost.Decoder.Hints
public import LeanVM.Guest.Fast.Da
import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

/-!
# The guest decoder's compiled chain: the DA matrix

`da_verify`'s witness off its callees' frames, keyed by the functions' indices
(`Guest.Fast.dvWitN`, equal to `Da.dvWit` at the frame map re-keyed by `decoderFunctionName`,
`Guest.Fast.dvWitN_eq`): the blobs' rows of the cells' symbols, staged, each frame looked up once:

* the number of blobs (a logarithm, `gLogD D`, the logarithm's tables `D` given, at most `DA_MAX_ROWS`,
  `daRowCount`, as `Da.dvRows`) computed once by `dvWitND` and passed to `dvWitNAt`;
* each blob's region base (`dvBlobBase`: its blob-loop iteration's two words, then
  `da_verify_blob`'s frame) computed once and passed as a value to its row (`dvRowOf`);
* each cell's loop frame (`dvCellVW`, `da_verify_blob_loop0`) passed as a closure to
  `cellSymsAt`, which reads its four words once;
* the powers of `g` taken in `K` (`ofK (g^i)`), not in `E`.

`dvWitNAt_eq : dvWitNAt r σ Vn = …` is the unstaged witness (`dvSymsPNAt`), and
`dvWitND_tables : dvWitND discreteLogTables = dvWitN`.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Cost LeanVM.Parameters LeanVM.Guest.Fast LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Guest.B1.Da LeanVM.Extraction.Fast LeanVM.Protocol.Verifier

@[expose] public section

/-- The symbols, padded outside the matrix of `r` blobs (`dvSymsPN`, `r` its logarithm). -/
def dvSymsPNAt (r : ℕ) (σ : Val) (Vn : NFrames) (i h : ℕ) : List E :=
  if i < r ∧ h < 128 then
    cellSymsOf (Vn (fn_idx% da_verify_cell) [dvCellVN σ Vn i h (.n 4)]
      [dvCellVN σ Vn i h (.n 5), dvCellVN σ Vn i h (.n 6), dvCellVN σ Vn i h (.n 7)])
  else List.replicate 128 0

/-! ## Each frame once -/

/-- Blob `i`'s iteration of the blob loop (`dvBlobLVN`), the power of `g` in `K`. -/
def dvBlobLW (σ : Val) (Vn : NFrames) (i : ℕ) : Val :=
  Vn (fn_idx% da_verify_loop0) [ofK (Parameters.g ^ i), σ (.n (val% «da_verify» "n_blob_g")), σ (.n (val% «da_verify» "weights")), σ (.n (val% «da_verify» "roots"))] []

/-- Blob `i`'s region base (`dvBlobVN σ Vn i (.n 1)`). -/
def dvBlobBase (σ : Val) (Vn : NFrames) (i : ℕ) : E :=
  Vn (fn_idx% da_verify_blob) [σ (.n 8)] [dvBlobLW σ Vn i (.n 4), dvBlobLW σ Vn i (.n 5)] (.n 1)

/-- Cell `h`'s iteration of a blob's cell loop (`dvCellVN`), the blob's base given. -/
def dvCellVW (σ : Val) (Vn : NFrames) (base : E) (h : ℕ) : Val :=
  Vn (fn_idx% da_verify_blob_loop0) [ofK (Parameters.g ^ h), σ (.n (val% «da_verify» "weights")), base] []

/-- A cell's symbols off `da_verify_cell`'s frame, the cell loop's valuation given. -/
def cellSymsAt (Vn : NFrames) (cell : Val) : List E :=
  cellSymsOf (Vn (fn_idx% da_verify_cell) [cell (.n 4)] [cell (.n 5), cell (.n 6), cell (.n 7)])

/-- Cell `h`'s symbols, its blob's base given. -/
def dvSymsCell (σ : Val) (Vn : NFrames) (base : E) (h : ℕ) : List E :=
  cellSymsAt Vn (dvCellVW σ Vn base h)

/-- A blob's row, its base given. -/
def dvRowOf (σ : Val) (Vn : NFrames) (base : E) : List E :=
  (List.range 128).flatMap fun h => dvSymsCell σ Vn base h

/-- Blob `i`'s row, its base computed once. -/
def dvRowAt (σ : Val) (Vn : NFrames) (i : ℕ) : List E := dvRowOf σ Vn (dvBlobBase σ Vn i)

/-- `da_verify`'s witness, its `r` blobs given (`dvWitN`). -/
def dvWitNAt (r : ℕ) (σ : Val) (Vn : NFrames) : LeanVM.Da.MatrixWitness :=
  ⟨(List.range r).map fun i => dvRowAt σ Vn i⟩

theorem dvSymsCell_eq (r : ℕ) (σ : Val) (Vn : NFrames) {i h : ℕ} (hi : i < r) (hh : h < 128) :
    dvSymsCell σ Vn (dvBlobBase σ Vn i) h = dvSymsPNAt r σ Vn i h := by
  unfold dvSymsPNAt
  simp only [hi, hh, and_self, ↓reduceIte]
  simp only [dvSymsCell, cellSymsAt, dvCellVW, dvBlobBase, dvBlobLW, dvCellVN, dvBlobVN, dvBlobLVN,
    LeanVM.Guest.Value.gen_pow_eq_ofK]

/-- **The staged witness is the unstaged one.** -/
theorem dvWitNAt_eq (r : ℕ) (σ : Val) (Vn : NFrames) :
    dvWitNAt r σ Vn = ⟨daRows r (dvSymsPNAt r σ Vn)⟩ := by
  unfold dvWitNAt daRows
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  rw [List.mem_range] at hi
  unfold dvRowAt dvRowOf
  refine List.flatMap_congr fun h hh ↦ ?_
  rw [List.mem_range] at hh
  exact dvSymsCell_eq r σ Vn hi hh

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
  dvWitNAt (daRowCount (gLogD D (σ (.n (val% «da_verify» "n_blob_g"))))) σ Vn

theorem dvWitND_tables : dvWitND discreteLogTables = dvWitN := by
  funext σ Vn
  unfold dvWitND
  rw [dvWitNAt_eq]
  unfold dvWitN dvSymsPNAt dvSymsPN dvRows
  rw [gLogD_tables, daRowCount_eq]

cost_compile cellSymsOfC := LeanVM.Guest.B1.Da.cellSymsOf
cost_compile dvBlobLWC := dvBlobLW
cost_compile dvBlobBaseC := dvBlobBase
cost_compile dvCellVWC := dvCellVW
cost_compile cellSymsAtC := cellSymsAt
cost_compile dvSymsCellC := dvSymsCell
cost_compile dvRowOfC := dvRowOf
cost_compile dvRowAtC := dvRowAt
cost_compile dvWitNAtC := dvWitNAt
cost_compile daRowCountC := daRowCount
cost_compile dvWitNC := dvWitND

end

end LeanVM.Cost.Decoder
