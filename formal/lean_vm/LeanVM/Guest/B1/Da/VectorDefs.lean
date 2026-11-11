/-
  LeanVM.Guest.B1.Da.VectorDefs

  The meanings of the functions that build the dual codeword (`da_vector`, `da_factors`,
  `da_expand`, `da_column_offsets`) and the values they compute.
-/

module

public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Da.DualMath

/-!
# The dual codeword's builders: meanings (G:4396-4460)

`da_vector(z)` (G:4396-4415, `core31`) returns four pointers: the powers `z_j = z^(2^j)`, `j < 14`,
and `0` at `14` (`zs`, `ZsAt`); the leaves of the product tree over the cell index (`top_leaves`,
`da_expand__L14_L7`: `topLeaf z h`, the factors `j = 8 … 13` of the dual codeword at the cell
`h`'s first point); the factors of the tree inside a cell (`cell_factors`,
`da_factors__L7_L8_L128`); each column's shifts of them (`offsets`, `da_column_offsets`:
`z_j Ŵ_j(256 h)`). `da_verify_column` expands each column's tree from its top leaf with them
(`da_expand__L7_L8`), whose leaves are the dual codeword's entries `256 h + e` (`VectorMath`).

A product tree over the bits `top, top - 1, …` of depth `D`, in heap order: node `n = 2^d + y` at
depth `d` splits the bit `j = top - d`, `y` the bits above it. `da_factors(zs, top, D, at)`
(G:4416-4424) writes node `n`'s factor `1 + z_j Ŵ_j(y · 2^(j + 1))` (`DA_VHAT[at + n]`, the bits
above `j` of the point, `factorAt`); `da_expand(root, factors, zs, shifts, top, D)` (G:4427-4439)
multiplies down the tree: a node's children are it times its factor plus the shift of its bit and,
for the child of bit one, `z_j` (`expandLeaf`). `da_column_offsets(zs)` (G:4442-4460) writes
`offsets[8h + j] = z_j · Ŵ_j(256 h)`, one doubling per bit of `h` (`DA_VHAT_COLUMN`, `Ŵ_j` at the
basis elements `e_(8 + b)`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The values -/

/-- `zs[j]`: `z^(2^j)` for `j < 14`, `0` at `14` (G:4402-4407). -/
def zsVal (z : E) (j : ℕ) : E := if j < 14 then z ^ 2 ^ j else 0

/-- The factor at node `n` of a product tree over the bits `top, top - 1, …`, with the bit powers
`Z`: `Z_j · Ŵ_j(y · 2^(j + 1)) + 1`, `n = 2^d + y`, `j = top - d` (`da_factors`). -/
def factorAt (Z : ℕ → E) (top n : ℕ) : E :=
  Z (top - Nat.log 2 n) * ofK (wK (top - Nat.log 2 n) ((n - 2 ^ Nat.log 2 n) * 2 ^ (top - Nat.log 2 n + 1))) + 1

/-- **Leaf `y` of `da_expand`'s tree**: `root` times, at each depth `k < D`, the factor of the
node on `y`'s path, its bit's shift and, if the bit is one, `Z_(top - k)`. -/
def expandLeaf (root : E) (F Z S : ℕ → E) (top D y : ℕ) : E :=
  root * ((List.range D).map fun k ↦ F (2 ^ k + y >>> (D - k)) + S (top - k) +
    if y.testBit (D - 1 - k) then Z (top - k) else 0).prod

/-- The dual codeword's factors `j = 8 … 13` at the cell `h`'s first point: leaf `h` of the tree
over the cell index. -/
def topLeaf (z : E) (h : ℕ) : E :=
  ((List.range 6).map fun i ↦ 1 + z ^ 2 ^ (8 + i) * ofK (wK (8 + i) (256 * h))).prod

/-! ## The meanings -/

/-- The powers at `zs`. -/
def ZsAt (rd : Reader) (zs z : E) : Prop := ∀ j < 15, LoadHolds rd zs j (zsVal z j)

/-- A frame run at `p`: every word readable at `p · g^k`, `k < n`, is `f k`. -/
def RunAt (rd : Reader) (p : E) (n : ℕ) (f : ℕ → E) : Prop :=
  IsInK p ∧ ∀ k < n, ∀ w, rd (p.limb 0 * addressOfIndex k) = some w → w = f k

/-- **`da_factors(zs, top, D, at)`** (`D ≤ 8`): some powers `Z` at `zs` (the bits `top - d`,
`d < D`), and node `n`'s factor `factorAt Z top n` at `p · g^n`, `1 ≤ n < 2^D`. -/
def MeaningDaFactors (top D : ℕ) (rd : Reader) : List E → List E → Prop
  | [zs], [p] => ∃ Z : ℕ → E, (∀ d < D, LoadHolds rd zs (top - d) (Z (top - d))) ∧
      ∀ n, 1 ≤ n → n < 2 ^ D → LoadHolds rd p n (factorAt Z top n)
  | _, _ => False

/-- **`da_expand(root, factors, zs, shifts, top, D)`**: some factors `F`, powers `Z` and shifts
`S` read, and the returned frame run holds the leaves (`expandLeaf`). -/
def MeaningDaExpand (top D : ℕ) (rd : Reader) : List E → List E → Prop
  | [root, fs, zs, sh], [p] => ∃ F Z S : ℕ → E,
      (∀ n, 1 ≤ n → n < 2 ^ D → LoadHolds rd fs n (F n)) ∧
      (∀ d < D, LoadHolds rd zs (top - d) (Z (top - d))) ∧
      (∀ d < D, LoadHolds rd sh (top - d) (S (top - d))) ∧
      RunAt rd p (2 ^ D) (expandLeaf root F Z S top D)
  | _, _ => False

/-- **`da_column_offsets(zs)`**: some powers `Z` at `zs` (`j < 8`), and
`offsets[8h + j] = Z_j · Ŵ_j(256 h)`, `h < 128`. -/
def MeaningDaColumnOffsets (rd : Reader) : List E → List E → Prop
  | [zs], [off] => ∃ Z : ℕ → E, (∀ j < 8, LoadHolds rd zs j (Z j)) ∧
      ∀ h < 128, ∀ j < 8, LoadHolds rd off (8 * h + j) (Z j * ofK (wK j (256 * h)))
  | _, _ => False

/-- **`da_vector(z)`**: the powers, the top leaves (a frame run), the cell tree's factors and the
column offsets, of `z`. -/
def MeaningDaVector (rd : Reader) : List E → List E → Prop
  | [z], [zs, tl, cf, off] => ZsAt rd zs z ∧ RunAt rd tl 128 (topLeaf z) ∧
      (∀ n, 1 ≤ n → n < 256 → LoadHolds rd cf n (factorAt (zsVal z) 7 n)) ∧
      ∀ h < 128, ∀ j < 8, LoadHolds rd off (8 * h + j) (zsVal z j * ofK (wK j (256 * h)))
  | _, _ => False

def da_factors_sound_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_factors__L14_L7_L0" args rets → MeaningDaFactors 14 7 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_factors__L7_L8_L128" args rets → MeaningDaFactors 7 8 rd args rets

def da_expand_sound_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_expand__L14_L7" args rets → MeaningDaExpand 14 7 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_expand__L7_L8" args rets → MeaningDaExpand 7 8 rd args rets

def da_column_offsets_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_column_offsets" args rets → MeaningDaColumnOffsets rd args rets

def da_vector_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_vector" args rets → MeaningDaVector rd args rets

end
end LeanVM.Guest.B1.Da
