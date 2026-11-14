/-
  LeanVM.Guest.B1.Da.Interface

  The interface of B1's LeanDA functions: what `da_verify` and its helpers compute, and the
  statements that their core IR computes it.
-/

module

public import LeanVM.Guest.B1.Digest.Interface
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# LeanDA: meanings (TRIAGE G #90-93)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py`, G
below) its meaning on its argument and return words, and `…_sound_Spec`: its core
IR relation (`coreProgram.Rel`) gives the meaning. A `…_Spec` is a definition (a `Prop`); its
proof is the theorem `…_holds` of the family's modules. The functions building the dual codeword
(`da_vector` and its callees) have their meanings in `VectorDefs`.

| function | G | meaning |
| --- | --- | --- |
| `da_verify` | 4509-4547 | `Da.MatrixWitness.Opens` (`Statement/LeanVmGuest.lean`): a matrix of `1..LeanDa.maxRows` codewords committed to the returned root (`LeanDa.commitCells` of the matrix, `LeanDa.commitCodewords` level by level), orthogonal to the dual codeword of the returned challenge |
| `da_row_shape` | 4550-4559 | `n_blob = g^r`, `1 ≤ r ≤ LeanDa.maxRows`, the padded count `2^L = LeanDa.nPad r` |
| `da_verify_cell` | 4579-4591 | one cell's digest (`LeanDa.listCellDigestWithHash`) and its dot product with the column's weights |
| `da_levels__L{n}_L{k}` | 4594-4602 | the Merkle root over `n = 2^k` leaves of two cells (`LeanDa.treeRootWithHash`) |

`da_verify` reads the padded row count's power off the exponent table `g_squares`
(`exponent_tables`, `SquaresAt`).

The trees: a node is two cells; an internal node's cells are the digest of its children's four
(`nodeCells`); `cellRoot k leaves` is the root over `2^k` leaves, level by level as `da_levels`
builds it (`LeanDa.treeLevelWithHash`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## Shared vocabulary -/

/-- The table of `g^(2^j)` at `q`, `j < 34` (`exponent_tables`' second table, `g_squares`). -/
def SquaresAt (rd : Reader) (q : E) : Prop := ∀ j < 34, LoadHolds rd q j (gen ^ 2 ^ j)

/-- The two cells of a tree node from its children's: their digest. -/
def nodeCells (l r : E × E) : E × E := digestHalves (keccak256 (cellsBytes [l.1, l.2, r.1, r.2]))

/-- One level of a tree of cell pairs. -/
def cellLevel (nodes : List (E × E)) : List (E × E) :=
  (List.range (nodes.length / 2)).map fun i ↦ nodeCells (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0)

/-- The root over `2^k` leaves, `k` levels up. -/
def cellRoot : ℕ → List (E × E) → E × E
  | 0, nodes => nodes.headD 0
  | k + 1, nodes => cellRoot k (cellLevel nodes)

/-- The cells of a list of nodes, two a node. -/
def pairCells (nodes : List (E × E)) : List E := nodes.flatMap fun p ↦ [p.1, p.2]

/-! ## `da_verify` (G:4509-4547, TRIAGE #90) -/

/-- **`da_verify(g_squares)`**: with the exponent table at `g_squares`, a witness opens the claim
of the returned root and challenge `z` (`Da.MatrixWitness.Opens`), the three returned words the
root's cells and `z`. -/
def MeaningDaVerify (rd : Reader) : List E → List E → Prop
  | [gsq], rets => SquaresAt rd gsq →
      ∃ (w : LeanVM.Da.MatrixWitness) (root : Digest) (z : E), w.Opens root z ∧
        rets = digestCells root ++ [z]
  | _, _ => False

/-- `da_verify`'s core IR gives its meaning, on a memory image. -/
def da_verify_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "da_verify" args rets → MeaningDaVerify rd args rets

/-! ## `da_row_shape` (G:4550-4559, TRIAGE #91) -/

/-- **`da_row_shape(n_blob_g, g_log_pad, g_squares)`**: with the exponent table at `g_squares`,
`n_blob = g^r` for `1 ≤ r ≤ LeanDa.maxRows`, `g_log_pad = g^L` with `2^L` the padded count
`LeanDa.nPad r`, and the function returns `g^(2^L)` and `g^(2^L - r)`. -/
def MeaningDaRowShape (rd : Reader) : List E → List E → Prop
  | [nb, glp, gsq], rets => SquaresAt rd gsq →
      ∃ r L, 1 ≤ r ∧ r ≤ LeanDa.maxRows ∧ L ≤ guest_const% DA_LOG_MAX_ROWS ∧ nb = gen ^ r ∧ glp = gen ^ L ∧
        2 ^ L = LeanDa.paddedRowCount r ∧ rets = [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]
  | _, _ => False

/-- `da_row_shape`'s core IR gives its meaning, on a memory image. -/
def da_row_shape_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "da_row_shape" args rets → MeaningDaRowShape rd args rets

/-! ## `da_verify_cell` (G:4579-4591, TRIAGE #92) -/

/-- **`da_verify_cell(lvals)`**: some `128` symbols of `E` (the hint), their digest's two cells
(LeanDA's cell digest, sixteen bytes a symbol) and their dot product with the `128` weights at
`lvals`. -/
def MeaningDaVerifyCell (rd : Reader) : List E → List E → Prop
  | [lv], rets => ∃ (syms ws : List E), syms.length = LeanDa.cellSymbols ∧
      ReadsAt rd lv ws ∧ ws.length = LeanDa.cellSymbols ∧
      rets = digestCells (keccak256 (syms.flatMap E.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * syms.getD e 0).sum]
  | _, _ => False

/-- `da_verify_cell`'s core IR gives its meaning. -/
def da_verify_cell_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_verify_cell" args rets → MeaningDaVerifyCell rd args rets

/-! ## `da_levels` (G:4594-4602, TRIAGE #92) -/

/-- The name of `da_levels`' specialization at `2^k` leaves, `da_levels__L{2^k}_L{k}`, for `k` up to
a row's own tree (`DlDepth`). -/
def daLevelsName (k : ℕ) : String :=
  ["da_levels__L1_L0", "da_levels__L2_L1", "da_levels__L4_L2", "da_levels__L8_L3",
    "da_levels__L16_L4", "da_levels__L32_L5", "da_levels__L64_L6", "da_levels__L128_L7"].getD k ""

/-- **The depths `da_levels` is specialized at**: the matrix's trees, `k ≤ DA_LOG_MAX_ROWS`
(`da_verify`'s dispatch), and a row's own tree over its cells, `k = DA_BLOCK_BITS`. -/
def DlDepth (k : ℕ) : Prop := k ≤ guest_const% DA_LOG_MAX_ROWS ∨ k = guest_const% DA_BLOCK_BITS

instance (k : ℕ) : Decidable (DlDepth k) := inferInstanceAs (Decidable (_ ∨ _))

/-- **The Statement's row cap is the guest's**: `LeanDa.maxRows` is `DA_MAX_ROWS`. -/
theorem maxRows_eq : LeanDa.maxRows = guest_const% DA_MAX_ROWS := by decide

/-- Its log is `DA_LOG_MAX_ROWS`. -/
theorem logMaxRows_eq : LeanDa.logMaxRows = guest_const% DA_LOG_MAX_ROWS := rfl

/-- **`da_levels(tree, 2^k, k)`**: the `2^k` leaves at `tree` (two cells each), and the function
returns the root's cells (`cellRoot`). -/
def MeaningDaLevels (k : ℕ) (rd : Reader) : List E → List E → Prop
  | [tree], rets => ∃ leaves : List (E × E), leaves.length = 2 ^ k ∧
      ReadsAt rd tree (pairCells leaves) ∧
      rets = [(cellRoot k leaves).1, (cellRoot k leaves).2]
  | _, _ => False

/-- `da_levels`' specializations (`DlDepth`) compute their meanings. -/
def da_levels_sound_Spec : Prop :=
  ∀ k, DlDepth k → ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd (daLevelsName k) args rets → MeaningDaLevels k rd args rets

/-! ## The functions, found -/

theorem find_da_verify :
    coreProgram.find? name% «da_verify» = some fn% «da_verify» :=
  coreProgram_find?_at (j := idx% «da_verify») rfl

theorem find_da_row_shape :
    coreProgram.find? name% «da_row_shape» = some fn% «da_row_shape» :=
  coreProgram_find?_at (j := idx% «da_row_shape») rfl

theorem find_da_verify_column :
    coreProgram.find? name% «da_verify_column» = some fn% «da_verify_column» :=
  coreProgram_find?_at (j := idx% «da_verify_column») rfl

theorem find_da_verify_cell :
    coreProgram.find? name% «da_verify_cell» = some fn% «da_verify_cell» :=
  coreProgram_find?_at (j := idx% «da_verify_cell») rfl

theorem find_da_vector :
    coreProgram.find? name% «da_vector» = some fn% «da_vector» :=
  coreProgram_find?_at (j := idx% «da_vector») rfl

theorem find_da_column_offsets :
    coreProgram.find? name% «da_column_offsets» = some fn% «da_column_offsets» :=
  coreProgram_find?_at (j := idx% «da_column_offsets») rfl

set_option maxRecDepth 100000 in
theorem find_da_expand_L6_L7 :
    coreProgram.find? name% «da_expand__L6_L7» = some fn% «da_expand__L6_L7» :=
  coreProgram_find?_at (j := idx% «da_expand__L6_L7») rfl

set_option maxRecDepth 100000 in
theorem find_da_factors_L13_L7_L0 :
    coreProgram.find? name% «da_factors__L13_L7_L0» = some fn% «da_factors__L13_L7_L0» :=
  coreProgram_find?_at (j := idx% «da_factors__L13_L7_L0») rfl

set_option maxRecDepth 100000 in
theorem find_da_expand_L13_L7 :
    coreProgram.find? name% «da_expand__L13_L7» = some fn% «da_expand__L13_L7» :=
  coreProgram_find?_at (j := idx% «da_expand__L13_L7») rfl

set_option maxRecDepth 100000 in
theorem find_da_factors_L6_L7_L128 :
    coreProgram.find? name% «da_factors__L6_L7_L128» = some fn% «da_factors__L6_L7_L128» :=
  coreProgram_find?_at (j := idx% «da_factors__L6_L7_L128») rfl

end
end LeanVM.Guest.B1.Da
