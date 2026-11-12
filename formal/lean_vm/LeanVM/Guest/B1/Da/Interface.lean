/-
  LeanVM.Guest.B1.Da.Interface

  The interface of B1's LeanDA functions: what `da_verify` and its helpers compute, and the
  statements that their core IR computes it.
-/

module

public import LeanVM.Guest.B1.Digest.Interface

/-!
# LeanDA: meanings (TRIAGE G #90-93)

For each function of the guest (`crates/rec_aggregation/guests/lean_ethereum.py`, G
below) its meaning on its argument and return words, and `…_sound_Spec`: its core
IR relation (`coreProgram.Rel`) gives the meaning. A `…_Spec` is a definition (a `Prop`); its
proof is the theorem `…_holds` of the family's modules. The functions building the dual codeword
(`da_vector` and its callees) have their meanings in `VectorDefs`.

| function | G | core | meaning |
| --- | --- | --- | --- |
| `da_verify` | 4509-4547 | `core27` | `Da.MatrixWitness.Opens` (`Statement/LeanVmGuest.lean`): a matrix of `1..1024` codewords committed to the returned root (`LeanDa.commitCells` of the matrix, `LeanDa.commitCodewords` level by level), orthogonal to the dual codeword of the returned challenge |
| `da_row_shape` | 4550-4559 | `core28` | `n_blob = g^r`, `1 ≤ r ≤ 1024`, the padded count `2^L = LeanDa.nPad r` |
| `da_verify_cell` | 4579-4591 | `core30` | one cell's digest (`LeanDa.listCellDigestWithHash`) and its dot product with the column's weights |
| `da_levels__L{n}_L{k}` | 4594-4602 | `core420-430` | the Merkle root over `n = 2^k` leaves of two cells (`LeanDa.treeRootWithHash`) |

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
`n_blob = g^r` for `1 ≤ r ≤ 1024`, `g_log_pad = g^L` with `2^L` the padded count
`LeanDa.nPad r`, and the function returns `g^(2^L)` and `g^(2^L - r)`. -/
def MeaningDaRowShape (rd : Reader) : List E → List E → Prop
  | [nb, glp, gsq], rets => SquaresAt rd gsq →
      ∃ r L, 1 ≤ r ∧ r ≤ LeanDa.maxRows ∧ L ≤ 10 ∧ nb = gen ^ r ∧ glp = gen ^ L ∧
        2 ^ L = LeanDa.paddedRowCount r ∧ rets = [gen ^ 2 ^ L, gen ^ (2 ^ L - r)]
  | _, _ => False

/-- `da_row_shape`'s core IR gives its meaning, on a memory image. -/
def da_row_shape_sound_Spec : Prop :=
  ∀ (rd : Reader), MemOk rd → ∀ (args rets : List E),
    coreProgram.Rel rd "da_row_shape" args rets → MeaningDaRowShape rd args rets

/-! ## `da_verify_cell` (G:4579-4591, TRIAGE #92) -/

/-- **`da_verify_cell(lvals)`**: some `256` symbols of `K` (the hint), their digest's two cells
(LeanDA's cell digest, eight bytes a symbol) and their dot product with the `256` weights at
`lvals`. -/
def MeaningDaVerifyCell (rd : Reader) : List E → List E → Prop
  | [lv], rets => ∃ (syms : List K) (ws : List E), syms.length = LeanDa.cellSymbols ∧
      ReadsAt rd lv ws ∧ ws.length = LeanDa.cellSymbols ∧
      rets = digestCells (keccak256 (syms.flatMap K.toBytes)) ++
        [((List.range LeanDa.cellSymbols).map fun e ↦ ws.getD e 0 * ofK (syms.getD e 0)).sum]
  | _, _ => False

/-- `da_verify_cell`'s core IR gives its meaning. -/
def da_verify_cell_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_verify_cell" args rets → MeaningDaVerifyCell rd args rets

/-! ## `da_levels` (G:4594-4602, TRIAGE #92) -/

/-- The name of `da_levels`' specialization at `2^k` leaves, `da_levels__L{2^k}_L{k}`. -/
def daLevelsName (k : ℕ) : String :=
  ["da_levels__L1_L0", "da_levels__L2_L1", "da_levels__L4_L2", "da_levels__L8_L3",
    "da_levels__L16_L4", "da_levels__L32_L5", "da_levels__L64_L6", "da_levels__L128_L7",
    "da_levels__L256_L8", "da_levels__L512_L9", "da_levels__L1024_L10"].getD k ""

/-- **`da_levels(tree, 2^k, k)`**: the `2^k` leaves at `tree` (two cells each), and the function
returns the root's cells (`cellRoot`). -/
def MeaningDaLevels (k : ℕ) (rd : Reader) : List E → List E → Prop
  | [tree], rets => ∃ leaves : List (E × E), leaves.length = 2 ^ k ∧
      ReadsAt rd tree (pairCells leaves) ∧
      rets = [(cellRoot k leaves).1, (cellRoot k leaves).2]
  | _, _ => False

/-- `da_levels`' specializations, `k ≤ 10`, compute their meanings. -/
def da_levels_sound_Spec : Prop :=
  ∀ k ≤ 10, ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd (daLevelsName k) args rets → MeaningDaLevels k rd args rets

/-! ## The functions, found -/

theorem find_da_verify : coreProgram.find? "da_verify" = some Data.core27 :=
  Program.find?_of_indexOf? (j := 27) (by decide +kernel) rfl

theorem find_da_row_shape : coreProgram.find? "da_row_shape" = some Data.core28 :=
  Program.find?_of_indexOf? (j := 28) (by decide +kernel) rfl

theorem find_da_verify_column : coreProgram.find? "da_verify_column" = some Data.core29 :=
  Program.find?_of_indexOf? (j := 29) (by decide +kernel) rfl

theorem find_da_verify_cell : coreProgram.find? "da_verify_cell" = some Data.core30 :=
  Program.find?_of_indexOf? (j := 30) (by decide +kernel) rfl

theorem find_da_vector : coreProgram.find? "da_vector" = some Data.core31 :=
  Program.find?_of_indexOf? (j := 31) (by decide +kernel) rfl

theorem find_da_column_offsets : coreProgram.find? "da_column_offsets" = some Data.core32 :=
  Program.find?_of_indexOf? (j := 32) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_da_expand_L7_L8 : coreProgram.find? "da_expand__L7_L8" = some Data.core418 :=
  Program.find?_of_indexOf? (j := 418) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_da_factors_L14_L7_L0 :
    coreProgram.find? "da_factors__L14_L7_L0" = some Data.core420 :=
  Program.find?_of_indexOf? (j := 420) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_da_expand_L14_L7 : coreProgram.find? "da_expand__L14_L7" = some Data.core421 :=
  Program.find?_of_indexOf? (j := 421) (by decide +kernel) rfl

set_option maxRecDepth 100000 in
theorem find_da_factors_L7_L8_L128 :
    coreProgram.find? "da_factors__L7_L8_L128" = some Data.core422 :=
  Program.find?_of_indexOf? (j := 422) (by decide +kernel) rfl

end
end LeanVM.Guest.B1.Da
