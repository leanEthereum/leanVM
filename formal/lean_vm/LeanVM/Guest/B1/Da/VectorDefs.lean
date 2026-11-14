/-
  LeanVM.Guest.B1.Da.VectorDefs

  The meanings of the functions that build the dual codeword (`da_vector`, `da_factors`,
  `da_expand`, `da_column_offsets`) and the values they compute.
-/

module

public import LeanVM.Guest.B1.Da.Interface
public import LeanVM.Guest.B1.Da.DualMath

/-!
# The dual codeword's builders: meanings

`da_vector(z)` returns four pointers: the powers `z_j = z^(2^j)`, `j < 13`, and `0` at `13`
(`zs`, `ZsAt`); the leaves of the product tree over the cell index (`top_leaves`,
`da_expand__L13_L7`: `topLeaf z h`, the factors `j = 7 … 12` of the dual codeword at the cell
`h`'s first point); the factors of the tree inside a cell (`cell_factors`,
`da_factors__L6_L7_L128`); each column's shifts of them (`offsets`, `da_column_offsets`:
`z_j Ŵ_j(128 h)`). `da_verify_column` expands each column's tree from its top leaf with them
(`da_expand__L6_L7`), whose leaves are the dual codeword's entries `128 h + e` (`VectorMath`).

A product tree over the bits `top, top - 1, …` of depth `D`, in heap order: node `n = 2^d + y` at
depth `d` splits the bit `j = top - d`, `y` the bits above it. `da_factors(zs, top, D, at)`
writes node `n`'s factor `1 + z_j Ŵ_j(y · 2^(j + 1))` (`DA_VHAT[at + n]`, the bits
above `j` of the point, `factorAt`); `da_expand(root, factors, zs, shifts, top, D)`
multiplies down the tree: a node's children are it times its factor plus the shift of its bit and,
for the child of bit one, `z_j` (`expandLeaf`). `da_column_offsets(zs)` writes
`offsets[7h + j] = z_j · Ŵ_j(128 h)`, one doubling per bit of `h` (`DA_VHAT_COLUMN`, `Ŵ_j` at the
basis elements `e_(7 + b)`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-! ## The values -/

/-- `zs[j]`: `z^(2^j)` for `j < 13`, `0` at `13` (`da_vector`). -/
def zsVal (z : E) (j : ℕ) : E := if j < 13 then z ^ 2 ^ j else 0

/-- The factor at node `n` of a product tree over the bits `top, top - 1, …`, with the bit powers
`Z`: `Z_j · Ŵ_j(y · 2^(j + 1)) + 1`, `n = 2^d + y`, `j = top - d` (`da_factors`). -/
def factorAt (Z : ℕ → E) (top n : ℕ) : E :=
  Z (top - Nat.log 2 n) * ofK (wK (top - Nat.log 2 n) ((n - 2 ^ Nat.log 2 n) * 2 ^ (top - Nat.log 2 n + 1))) + 1

/-- **Leaf `y` of `da_expand`'s tree**: `root` times, at each depth `k < D`, the factor of the
node on `y`'s path, its bit's shift and, if the bit is one, `Z_(top - k)`. -/
def expandLeaf (root : E) (F Z S : ℕ → E) (top D y : ℕ) : E :=
  root * ((List.range D).map fun k ↦ F (2 ^ k + y >>> (D - k)) + S (top - k) +
    if y.testBit (D - 1 - k) then Z (top - k) else 0).prod

/-- The dual codeword's factors `j = 7 … 12` at the cell `h`'s first point: leaf `h` of the tree
over the cell index. -/
def topLeaf (z : E) (h : ℕ) : E :=
  ((List.range 6).map fun i ↦ 1 + z ^ 2 ^ (7 + i) * ofK (wK (7 + i) (128 * h))).prod

/-! ## The meanings -/

/-- The powers at `zs`. -/
def ZsAt (rd : Reader) (zs z : E) : Prop := ∀ j < 14, LoadHolds rd zs j (zsVal z j)

/-- A frame run at `p`: every word readable at `p · g^k`, `k < n`, is `f k`. -/
def RunAt (rd : Reader) (p : E) (n : ℕ) (f : ℕ → E) : Prop :=
  IsInK p ∧ ∀ k < n, ∀ w, rd (p.limb 0 * addressOfIndex k) = some w → w = f k

/-- **`da_factors(zs, top, D, at)`** (`D ≤ 7`): some powers `Z` at `zs` (the bits `top - d`,
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

/-- **`da_column_offsets(zs)`**: some powers `Z` at `zs` (`j < 7`), and
`offsets[7h + j] = Z_j · Ŵ_j(128 h)`, `h < 128`. -/
def MeaningDaColumnOffsets (rd : Reader) : List E → List E → Prop
  | [zs], [off] => ∃ Z : ℕ → E, (∀ j < 7, LoadHolds rd zs j (Z j)) ∧
      ∀ h < 128, ∀ j < 7, LoadHolds rd off (7 * h + j) (Z j * ofK (wK j (128 * h)))
  | _, _ => False

/-- **`da_vector(z)`**: the powers, the top leaves (a frame run), the cell tree's factors and the
column offsets, of `z`. -/
def MeaningDaVector (rd : Reader) : List E → List E → Prop
  | [z], [zs, tl, cf, off] => ZsAt rd zs z ∧ RunAt rd tl 128 (topLeaf z) ∧
      (∀ n, 1 ≤ n → n < 128 → LoadHolds rd cf n (factorAt (zsVal z) 6 n)) ∧
      ∀ h < 128, ∀ j < 7, LoadHolds rd off (7 * h + j) (zsVal z j * ofK (wK j (128 * h)))
  | _, _ => False

def da_factors_sound_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_factors__L13_L7_L0" args rets → MeaningDaFactors 13 7 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_factors__L6_L7_L128" args rets → MeaningDaFactors 6 7 rd args rets

def da_expand_sound_Spec : Prop :=
  (∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_expand__L13_L7" args rets → MeaningDaExpand 13 7 rd args rets) ∧
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_expand__L6_L7" args rets → MeaningDaExpand 6 7 rd args rets

def da_column_offsets_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_column_offsets" args rets → MeaningDaColumnOffsets rd args rets

def da_vector_sound_Spec : Prop :=
  ∀ (rd : Reader) (args rets : List E),
    coreProgram.Rel rd "da_vector" args rets → MeaningDaVector rd args rets

end
end LeanVM.Guest.B1.Da
