/-
  LeanVM.Protocol.Relation.Link.Summand

  The link's summands on a stack: the row side's summand is the terminal check's `last` on the
  stack's own values, the index side's is its sum over the rows at zero fresh coefficients, and each
  fresh coefficient's weight is what that coefficient adds.
-/

module

public import LeanVM.Protocol.Relation.Link.Spec
public import LeanVM.Protocol.Relation.Link.Fold
public import LeanVM.Protocol.Relation.Link.Cube

/-!
# The link's summands

At a stack `q` and the link's chunks, the summands `LinkCore` (`Link/Spec.lean`) asks for:

* **the row summand** (`rowSummand`): `last`, the summand at the final point `x = (χ, q_point)` as
  `verify_link` computes it (`tailValuesF`, `Link/Fold.lean`), from the stack's own values instead of
  the prover's message: each table's non-pointer columns' extensions at its row point
  (`honestValues`), the pointer columns' bit-slices the ring claim names (`honestSlices`) and the
  memory term at `r` (`honestM1`), with the program's split `splitAt`. Under `LinkEndHolds` the
  message and `m1` are these, so the terminal check compares the claim with `rowSummand` (`tail`);
* **the row side's table** (`linkRow`): `rowSummand`'s partial sums over the cube of the row and
  pointer-column variables (`cube`, `Link/Cube.lean`);
* **the index summand** (`linkIdxAt`): the row side's full sum at zero fresh coefficients, a function
  of the index point `r`; **the index side's table** (`linkIdx`) its partial sums over the cube of the
  pointer width;
* **the weights** (`linkB`): fresh coefficient `i`'s, the row side's full sum at the unit vector `i`
  less the index summand. `rowSummand` is affine in the fresh coefficients (`cert` and `JUMP`'s
  `jump` enter linearly), so the row side's full sum is `linkIdxAt + Σ_i fresh_i·B_i` (`row_total`);
* `Good` is `True`: the index summand is the row side's sum, a polynomial of degree at most `2` in
  each index variable whether or not the pointers are one-hot.

What is left of `LinkCore` at these summands is `LinkSummandFacts`, field by field.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

open Classical

/-! ## The stack's values -/

/-- The memory term at `r` the stack gives: each limb's extension at the memory point, scaled as
`verify_link`'s end scales it. -/
def honestM1 (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (r : List E) : E :=
  belowAt chunks r layout.logMemory * rowMle (r.take layout.logMemory) (columnValue layout q memory0) +
    eY * belowAt chunks r layout.logMemory *
      rowMle (r.take layout.logMemory) (columnValue layout q memory1)

/-- The values the packed message holds on the stack: table by table, its non-pointer columns'
extensions at its row point. -/
def honestValues (layout : Layout) {μ : ℕ} (q : Column μ) (chi : List E) : List E :=
  (layout.tables.zipIdx.map fun (table, t) ↦ (nonPointerOf layout t table).map fun c ↦
    rowMle (chi.take (layout.tableLogHeights.getD t 0))
      (columnValue layout q (globalColumnBases.getD t 0 + c))).flatten

/-- The ring pieces the row side builds: they depend on the points alone. -/
def piecesOf (layout : Layout) (chi qPoint : List E) : List RingPiece :=
  (rowSideOf layout ⟨[], [], [], [], [], 0, 0, [], [], [], []⟩ ⟨0, 0, 0, 0, 0, 0, 0⟩ []
    (eqKernel qPoint) chi []).pieces

/-- The bit-slices the ring claim names on the stack. -/
def honestSlices (layout : Layout) {μ : ℕ} (q : Column μ) (chi qPoint : List E) : List E :=
  (List.range kBits).map fun b ↦ sumE ((piecesOf layout chi qPoint).map fun piece ↦
    piece.scale * rowMle piece.point fun j ↦ bitOf (pieceRow q piece.placement j) b)

/-- The packed message on the stack. -/
def honestMessage (layout : Layout) {μ : ℕ} (q : Column μ) (chi qPoint : List E) : List E :=
  honestValues layout q chi ++ honestSlices layout q chi qPoint

/-! ## The summands -/

/-- The program's split at the link's point. -/
def linkSplit (layout : Layout) (r : List E) : Split :=
  splitAt layout.bytecode (r.take layout.logBytecode) (pcSlots layout.tables)

/-- **The row summand** at `x = χ ++ q_point`: `last` on the stack's values. -/
def rowSummand (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r fresh : List E) (x : List E) : E :=
  let chi := x.take (linkRows layout)
  let qPoint := x.drop (linkRows layout)
  (tailValuesF layout chunks theta0 drawn r (honestM1 layout chunks q r) fresh (linkSplit layout r)
    chi qPoint (honestMessage layout q chi qPoint)).1

/-- **The row side's table**: the row summand's partial sums over the row and pointer-column
variables. -/
def linkRow (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r fresh : List E) : List E → E :=
  cube (rowSummand layout chunks q theta0 drawn r fresh) (linkRowVars layout)

/-- **The index summand** at `r`: the row side's sum at zero fresh coefficients. -/
def linkIdxAt (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) : E :=
  linkRow layout chunks q theta0 drawn r [] []

/-- **The index side's table**: the index summand's partial sums over the pointer width. -/
def linkIdx (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn : List E) : List E → E :=
  cube (linkIdxAt layout chunks q theta0 drawn) chunks.width

/-- The unit vector of fresh coefficient `i`. -/
def unitFresh (i : Fin 5) : List E := List.ofFn fun j : Fin 5 ↦ if j = i then 1 else 0

/-- **Fresh coefficient `i`'s weight** at `r`: what it adds to the row side's sum. -/
def linkB (layout : Layout) (chunks : Chunks) {μ : ℕ} (q : Column μ) (theta0 : E)
    (drawn r : List E) (i : Fin 5) : E :=
  linkRow layout chunks q theta0 drawn r (unitFresh i) [] - linkIdxAt layout chunks q theta0 drawn r

/-! ## What is left -/

/-- **What is left of `LinkCore`** at these summands, one field per obligation. -/
structure LinkSummandFacts (layout : Layout) {μ : ℕ} (q : Column μ) (chunks : Chunks) : Prop where
  /-- The index summand is of degree at most `2` in each index variable. -/
  idx_deg : ∀ theta0 drawn, PerVarDegAt (linkIdxAt layout chunks q theta0 drawn) chunks.width
    fun _ ↦ 2
  /-- Each weight is of degree at most `2` in each index variable. -/
  B_deg : ∀ theta0 drawn i, PerVarDeg (fun r ↦ linkB layout chunks q theta0 drawn r i) chunks.width 2
  /-- The row summand is of the row side's round degrees in each variable. -/
  row_deg : ∀ theta0 drawn r fresh, PerVarDegAt (rowSummand layout chunks q theta0 drawn r fresh)
    (linkRowVars layout)
    (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2)
  /-- The row side's full sum is the index summand plus the fresh coefficients' weights. -/
  row_total : ∀ theta0 drawn r fresh,
    linkRow layout chunks q theta0 drawn r fresh [] =
      linkIdxAt layout chunks q theta0 drawn r +
        ∑ i : Fin 5, fresh.getD i 0 * linkB layout chunks q theta0 drawn r i
  /-- The drawn group's count. -/
  group : (¬ LinkRel layout q ∨ ¬ KeccakRel layout q) →
    (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
      ¬ RoundDoom True (linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail)
        (IndexCarry layout q chunks (linkB layout chunks q) ((List.ofFn v).headD 0)
          (List.ofFn v).tail)
        (indexClaim layout chunks (List.ofFn v).tail) []).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks
  /-- The terminal check. -/
  tail : ∀ theta0 drawn r m1 fresh chi qPoint message, message.length = tailLen layout →
    chi.length = linkRows layout → qPoint.length = linkQVars layout →
    (tailValues layout chunks theta0 drawn r m1 fresh (linkSplit layout r) chi qPoint message).1 ≠
      linkRow layout chunks q theta0 drawn r fresh (chi ++ qPoint) →
    ¬ LinkEndHolds layout q
      (tailValues layout chunks theta0 drawn r m1 fresh (linkSplit layout r) chi qPoint message).2

/-- **The link's arithmetization from the summands' facts.** -/
def linkCoreOf {layout : Layout} {μ : ℕ} {q : Column μ} {chunks : Chunks}
    (h : LinkSummandFacts layout q chunks) : LinkCore layout q chunks where
  Good := True
  idx := linkIdx layout chunks q
  B := linkB layout chunks q
  row := linkRow layout chunks q
  idx_rounds _ theta0 drawn := roundPolys_cube (h.idx_deg theta0 drawn)
  B_deg := h.B_deg
  row_rounds theta0 drawn r fresh := roundPolys_cube (h.row_deg theta0 drawn r fresh)
  row_total theta0 drawn r fresh hr := by
    rw [h.row_total, linkIdx, cube_full hr.ge]
  group := h.group
  tail := h.tail

end

end LeanVM.Protocol.Relation
