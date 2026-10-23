/-
  LeanVM.Protocol.Stack

  Aligned stacking on leanVM's columns: `K`-columns stacked into one committed column, read back
  block by block, and evaluated at points of `E`.
-/

module

public import LeanVM.Protocol.Spine.Instance
public import LeanVM.Protocol.ToCompPoly.AmbientStacking

/-!
# The stack of columns

The generic stacking of `ToCompPoly/Stacking.lean`, specialised to the two fields of leanVM: the
blocks are columns over `K`, the stack is the one committed column, and every evaluation is at a
point of `E` (specification §4.1).

* `Blocks.stackColumn` is the witness stack: block `b` at its window, zero past the last block.
* `Blocks.readColumn` reads block `b` off *any* column of the stack's height, honest or not.
  `Blocks.readColumn_eval` is the stacking identity `q̃(z, sel_b) = P̃_b(z)`, for every `q`.
* `Blocks.layout` packages the lift of a point and that identity as a `Layout`, the reading law
  an `M3Instance` carries; the reader is derived from the lift. A layout is sizes only, so it
  names no table.
  `Layout.comap` renames its columns, which is how a layout indexed by blocks becomes one
  indexed by the columns of an instance.
* `Blocks.stridedLayout` reads the strided slots of one block: the low `k` coordinates of the
  block are frozen to the bits of a column's slot, and a point `z` of the column lifts to
  `(slot bits, z, sel_b)`. `Layout.piecewise` joins two layouts on the sum of their column
  types, which is how the aligned columns and the strided slots become one layout.
* `Blocks.stack_eval_ambient_one` is the one-padded stack over `E` at an arbitrary point, with
  the padding term written as the specification writes it in characteristic two,
  `1 + Σ_b eq(sel_b, ζ_hi)` (§5.4, equation (2)).

Written from the specification, except the strided slots, whose shape is the
Rust's (`crates/pcs/src/stack_open.rs:74-87`, `crates/leanvm_core/src/cpu/mod.rs:718-724` at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`). Which columns the blocks are, and in which order
equal sizes come, is the instance's to say, not this module's.

## Wrong readings excluded

* The reading law quantifies over every column `q`, not only over honest stacks: a knowledge
  extractor reads the blocks off whatever the prover committed.
* The padding term of the one-padded stack is the weight of the *uncovered* part of the cube,
  not the constant `1`; it vanishes when the blocks fill the stack.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Renaming the columns of a layout -/

/-- Reading through a renamed lift is reading the renamed column, cast to its height. -/
private theorem Layout.readWith_comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ}
    (extend : (c : ι) → Vector E (κ c) → Vector E μ) (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c)
    (q : Column μ) (c : ι') :
    Layout.readWith (fun c z ↦ extend (f c) (Vector.cast (h c).symm z)) q c =
      ⟨Vector.cast (congrArg (2 ^ ·) (h c)) (Layout.readWith extend q (f c)).values⟩ := by
  unfold Layout.readWith
  congr 1
  apply Vector.ext
  intro x hx
  simp only [Vector.getElem_cast, Vector.getElem_ofFn, boolVec_cast]
  rfl

/-- A layout read through a renaming of its columns that keeps their heights. -/
def Layout.comap {μ : ℕ} {ι ι' : Type} {κ : ι → ℕ} {κ' : ι' → ℕ} (L : Layout μ ι κ)
    (f : ι' → ι) (h : ∀ c, κ (f c) = κ' c) : Layout μ ι' κ' where
  extend := fun c z ↦ L.extend (f c) (Vector.cast (h c).symm z)
  read_eval := fun q c z ↦ by
    rw [Layout.readWith_comap L.extend f h]
    have hz : z = Vector.cast (h c) (Vector.cast (h c).symm z) := by simp
    conv_lhs => rw [hz]
    rw [eval₂Mle_cast, L.read_eval]

/-- The union of two layouts: a left column is read through `L₁`, a right column through
`L₂`. -/
def Layout.piecewise {μ : ℕ} {ι₁ ι₂ : Type} {κ₁ : ι₁ → ℕ} {κ₂ : ι₂ → ℕ} (L₁ : Layout μ ι₁ κ₁)
    (L₂ : Layout μ ι₂ κ₂) : Layout μ (ι₁ ⊕ ι₂) (Sum.elim κ₁ κ₂) where
  extend
    | .inl c => L₁.extend c
    | .inr c => L₂.extend c
  read_eval q
    | .inl c => L₁.read_eval q c
    | .inr c => L₂.read_eval q c

namespace Blocks

/-! ## Stacking and reading columns -/

section Columns

variable (B : Blocks) {μ : ℕ}

/-- The columns stacked on `μ` variables, zero past the last block: the witness stack (§4.1). -/
def stackColumn (t : B.Tables K) (μ : ℕ) : Column μ := ⟨B.stackAt t μ 0⟩

/-- Read block `b` off a column of height `2 ^ μ`: the cells of the block's window. -/
def readColumn (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) : Column (B.size b) :=
  ⟨B.unstack hμ q.values b⟩

/-- The stacking identity, for every column `q`: the block read off `q`, evaluated at `z`, is
`q` evaluated at `(z, sel_b)`. -/
theorem readColumn_eval (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (z : Vector E (B.size b)) :
    eval₂Mle (B.readColumn hμ q b).values (algebraMap K E) z =
      eval₂Mle q.values (algebraMap K E) (B.extendPoint hμ b z) :=
  (B.unstack_eval₂ (algebraMap K E) hμ q.values b z).symm

/-- The cell a cube point of block `b` lifts to: the point's index plus the block's offset. -/
theorem get_extendPoint (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n)
    (y : Fin (2 ^ B.size b)) :
    q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
      q.values[y.val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have := y.isLt
        omega) := by
  simp only [extendPoint, boolVec_append, boolIndex_cast, boolIndex_boolVec,
    Vector.get_eq_getElem, Fin.val_cast, cubeIndex_val, selector_val]
  congr 1
  exact congrArg (y.val + ·) (Nat.mul_div_cancel' (B.pow_size_dvd_offset b))

/-- Reading through the lift of the aligned blocks is reading the block: the cube point
`(x, sel_b)` is the cell `x + offset_b`. -/
private theorem readWith_extendPoint (hμ : B.total ≤ 2 ^ μ) (q : Column μ) (b : Fin B.n) :
    Layout.readWith (B.extendPoint hμ) q b = B.readColumn hμ q b := by
  unfold Layout.readWith readColumn
  congr 1
  apply Vector.ext
  intro x hx
  rw [B.unstack_getElem hμ q.values b hx]
  simp only [Vector.getElem_ofFn, extendPoint, boolVec_append, boolIndex_cast, boolIndex_boolVec,
    Vector.get_eq_getElem, Fin.val_cast, cubeIndex_val, selector_val]
  congr 1
  exact congrArg (x + ·) (Nat.mul_div_cancel' (B.pow_size_dvd_offset b))

/-- The aligned blocks as a reading law on the committed column. -/
def layout (hμ : B.total ≤ 2 ^ μ) : Layout μ (Fin B.n) B.size where
  extend := B.extendPoint hμ
  read_eval := fun q b z ↦ by rw [readWith_extendPoint]; exact B.readColumn_eval hμ q b z

/-! ## Strided slots of a block -/

/-- Reading through a strided lift: the column at slot `slot c` of block `b` is the low slice
at that slot of the block read off the stack. -/
private theorem readWith_strided (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) (q : Column μ)
    (c : ι) :
    (Layout.readWith (fun c (z : Vector E (κ c)) ↦
        B.extendPoint hμ b (Vector.cast (h c).symm ((boolVec (slot c) : Vector E k) ++ z)))
        q c).values =
      sliceLow (Vector.cast (congrArg (2 ^ ·) (h c)) (B.readColumn hμ q b).values) (slot c) := by
  have key : ∀ y : Fin (2 ^ B.size b),
      q.values.get (boolIndex (B.extendPoint hμ b (boolVec y : Vector E (B.size b)))) =
        (B.readColumn hμ q b).values[y] := by
    intro y
    rw [← B.readWith_extendPoint hμ q b]
    simp [Layout.readWith]
  apply Vector.ext
  intro x hx
  simp only [Layout.readWith, Vector.getElem_ofFn, boolVec_append, boolVec_cast, key, sliceLow,
    Fin.getElem_fin, Vector.getElem_cast, Fin.val_cast]

/-- The strided slots of block `b`, one column per slot: the low `k` coordinates of the block
are frozen to the bits of the column's slot, and a point `z` of the column lifts to the stack's
point `(slot bits, z, selector bits of b)`. The weight of such a claim is nonzero only at the
cells `offset_b + slot + j · 2 ^ k`. -/
def stridedLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type} {κ : ι → ℕ}
    (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) : Layout μ ι κ where
  extend := fun c z ↦
    B.extendPoint hμ b (Vector.cast (h c).symm ((boolVec (slot c) : Vector E k) ++ z))
  read_eval := fun q c z ↦ by
    rw [B.readWith_strided hμ b k slot h q c, ← B.readColumn_eval hμ q b,
      ← eval₂Mle_cast (algebraMap K E) (h c)]
    simp only [Vector.cast_cast, Vector.cast_rfl]
    rw [eval₂Mle, eval₂Mle, sliceLow_map, evalMle_boolVec_append]

/-- A strided slot's cell `x` is the block's cell `slot + x · 2 ^ k`, at the block's offset. -/
theorem get_stridedLayout (hμ : B.total ≤ 2 ^ μ) (b : Fin B.n) (k : ℕ) {ι : Type}
    {κ : ι → ℕ} (slot : ι → Fin (2 ^ k)) (h : ∀ c, B.size b = k + κ c) (q : Column μ) (c : ι)
    (x : Fin (2 ^ κ c)) :
    q.values.get (boolIndex ((B.stridedLayout hμ b k slot h).extend c (boolVec x))) =
      q.values[(cubeIndex (slot c) x).val + B.offset b]'(by
        have := B.offset_add_pow_le_total b
        have h1 := (cubeIndex (slot c) x).isLt
        have h2 : 2 ^ (k + κ c) = 2 ^ B.size b := by rw [h c]
        omega) := by
  simp only [stridedLayout, boolVec_append, boolVec_cast, get_extendPoint, Fin.val_cast]

end Columns

/-! ## The one-padded stack in characteristic two -/

/-- The one-padded stack of `E`-tables at an arbitrary point (§5.4, equation (2)): the blocks'
weighted evaluations, plus the weight `1 + Σ_b eq(sel_b, ζ_hi)` of the uncovered cells. -/
theorem stack_eval_ambient_one (B : Blocks) (t : B.Tables E) {μ : ℕ} (hμ : B.total ≤ 2 ^ μ)
    (ζ : Vector E μ) :
    evalMle (B.stackAt t μ 1) ζ =
      (∑ b : Fin B.n, B.selectorWeight hμ b ζ * evalMle (t b) (B.lowPoint hμ b ζ)) +
        (1 + ∑ b : Fin B.n, B.selectorWeight hμ b ζ) := by
  rw [B.stack_eval_ambient t hμ 1 ζ, one_mul, CharTwo.sub_eq_add]

end Blocks

end
end LeanVM.Protocol
