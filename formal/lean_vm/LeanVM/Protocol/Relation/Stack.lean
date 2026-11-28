/-
  LeanVM.Protocol.Relation.Stack

  What a committed stack says: its columns read off by the layout's placements, the claims the
  verifier's phases leave on it and when they hold, the Keccak and public-input parts of the
  relation, and the execution the knowledge extractor reads off it.
-/

module

public import LeanVM.Protocol.Field
public import Statement.Verifier.Lib
public import LeanVM.Protocol.Tables

/-!
# The stack and its claims

The shared vocabulary of the knowledge-soundness proof (`notes/hotwire-port.md`, M2-KS). A stack is
a `Column μ` (`Protocol/Field.lean`), `2^μ` words of `K`.

* **Columns.** Row `i` of the global column `c` is the stack's cell at its placement's offset plus
  `i` (`columnRow`, as `buildLayout` places it); the `KECCAK` output lanes, which nothing commits,
  read the last Keccak segment run on the committed state (`keccakOutput`); `columnValue` is every
  column's rows in `E`.
* **Claims.** A column claim holds when its value is its column's multilinear extension at its
  point (`ColumnClaimHolds`), a stack claim when the weight's inner product with the stack is the
  value (`StackClaimHolds`, `Σ_x w(x)·q(x)` over the cube), a ring claim when its `64` slices are
  its pieces' bit slices at their points (`RingClaimHolds`), the link's end when its memory term,
  its column claims and its ring claim hold (`LinkEndHolds`).
* **The relation's Keccak and public-input parts.** `q_keccak` holds, per `KECCAK` row, the
  permutation's input in slots `0..25` (the table's input lanes) and the state after the first
  segment's `12` rounds in slots `25..50`; `KeccakRel` says that state is the first segment of the
  input on every row of the table's height, and then `keccakOutput` is Keccak-f[1600] of the input
  (`keccakOutput_of_keccakRel`). `PubRel` says the memory's words `0` and `1` hold the public input.
  The link's part (`LinkRel`, the AIR's meaning) is `Protocol/Relation/Link.lean`'s.
* The extracted execution (`candidate`) is `Link/Rel.lean`'s: it reads the cycle the run halts at
  off the tables' rows.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Columns -/

/-- Cell `i` of a stack, `0` past its end. -/
def cell {μ : ℕ} (q : Column μ) (i : ℕ) : K := q.values.getD i 0

/-- Row `i` of the global column `c`: the stack's cell at the column's placement's offset plus `i`,
`0` for a column without a placement. -/
def columnRow (layout : Layout) {μ : ℕ} (q : Column μ) (c i : ℕ) : K :=
  match layout.placements.getD c none with
  | some placement => cell q (placement.index + i)
  | none => 0

/-- The `KECCAK` table's log-height. -/
def keccakHeight (layout : Layout) : ℕ := layout.tableLogHeights.getD opKeccak 0

/-- Lane `slot` of `q_keccak` at row `row`: its rows are slot-major, slot `s` the rows at offset
`s · 2^h` of the column, `h` the `KECCAK` table's log-height (`buildLayout`'s `slot <<< kappa`). -/
def qkeccakLane (layout : Layout) {μ : ℕ} (q : Column μ) (slot row : ℕ) : UInt64 :=
  (columnRow layout q qkeccak (slot * 2 ^ keccakHeight layout + row)).lane

/-- The permutation's input at a `KECCAK` row: `q_keccak`'s slots `0..25`, the table's input
lanes. -/
def keccakInput (layout : Layout) {μ : ℕ} (q : Column μ) (row : ℕ) : KeccakState :=
  Vector.ofFn fun l ↦ qkeccakLane layout q l.val row

/-- The committed state after the first segment at a `KECCAK` row: `q_keccak`'s slots `25..50`. -/
def keccakMid (layout : Layout) {μ : ℕ} (q : Column μ) (row : ℕ) : KeccakState :=
  Vector.ofFn fun l ↦ qkeccakLane layout q (keccakStateLanes + l.val) row

/-- `count` rounds of Keccak-f[1600] from round `start`. -/
def keccakRounds (a : KeccakState) (start count : ℕ) : KeccakState :=
  ((keccakRC.drop start).take count).foldl Keccak.round a

/-- The permutation's output the relation reads at a `KECCAK` row: the last segment's rounds on the
committed state. -/
def keccakOutput (layout : Layout) {μ : ℕ} (q : Column μ) (row : ℕ) : KeccakState :=
  keccakRounds (keccakMid layout q row) keccakDepth keccakDepth

/-- The `KECCAK` output lane a global column is, if any. -/
def keccakOutputLane (c : ℕ) : Option ℕ :=
  let base := globalColumnBases.getD opKeccak 0 + keccakOut
  if base ≤ c ∧ c < base + keccakStateLanes then some (c - base) else none

/-- Row `i` of the global column `c` in `E`: the `KECCAK` output lanes the permutation's output
(`keccakOutput`), every other column its committed rows. -/
def columnValue (layout : Layout) {μ : ℕ} (q : Column μ) (c i : ℕ) : E :=
  match keccakOutputLane c with
  | some l => ofK (K.ofLane (Keccak.lane (keccakOutput layout q i) l))
  | none => ofK (columnRow layout q c i)

/-! ## Claims -/

/-- The multilinear extension at `point` of the rows `f`, row `0` first, the first coordinate the
lowest bit (`multilinearEval`). -/
def rowMle (point : List E) (f : ℕ → E) : E :=
  multilinearEval ((List.range (2 ^ point.length)).map f) point

/-- **A stack claim holds** of the stack: the weight's values on the cube, paired with the stack,
give the value. -/
def StackClaimHolds {μ : ℕ} (c : StackClaim) (q : Column μ) : Prop :=
  ∑ x : Fin (2 ^ μ), c.1 (Tables.boolPoint μ x) * ofK (cell q x) = c.2

/-- **A column claim holds** of the stack: its value is its column's multilinear extension at its
point. -/
def ColumnClaimHolds (layout : Layout) {μ : ℕ} (q : Column μ) (c : ColumnClaim) : Prop :=
  c.value = rowMle c.point (columnValue layout q c.column)

/-- Bit `b` of a word, in `E`. -/
def bitOf (a : K) (b : ℕ) : E := if a.toBitVec.getLsbD b then 1 else 0

/-- The rows of a ring piece's column: its placement's (the whole stack for `none`). -/
def pieceRow {μ : ℕ} (q : Column μ) : Option Placement → ℕ → K
  | some placement, j => cell q (placement.index + j)
  | none, j => cell q j

/-- **A ring claim holds** of the stack: it has `64` slices, slice `b` the pieces' bit-`b` slices at
their points, scaled (`RingClaim`, `ring_switch.rs`). -/
def RingClaimHolds {μ : ℕ} (q : Column μ) (c : RingClaim) : Prop :=
  c.slices.length = kBits ∧ ∀ b < kBits,
    c.slices.getD b 0 =
      sumE (c.pieces.map fun piece ↦
        piece.scale * rowMle piece.point fun j ↦ bitOf (pieceRow q piece.placement j) b)

/-- **What the link leaves holds** of the stack (`LinkEnd`, `link.rs`): the memory term (each
limb's multilinear extension at the memory point, scaled), every column claim it sends (the
`KECCAK` output lanes against `keccakOutput`), and its ring claim. -/
def LinkEndHolds (layout : Layout) {μ : ℕ} (q : Column μ) (e : LinkEnd) : Prop :=
  e.memoryValue =
      e.memoryScales.1 * rowMle e.memoryPoint (columnValue layout q memory0) +
        e.memoryScales.2 * rowMle e.memoryPoint (columnValue layout q memory1) ∧
    (∀ c ∈ linkColumnClaims e, ColumnClaimHolds layout q c) ∧ RingClaimHolds q e.ring

/-! ## The relation's Keccak and public-input parts -/

/-- **`q_keccak` holds the first segment** on every row of the `KECCAK` table's height: the
committed state is the input's first `12` rounds. -/
def KeccakRel (layout : Layout) {μ : ℕ} (q : Column μ) : Prop :=
  ∀ row < 2 ^ keccakHeight layout,
    keccakMid layout q row = keccakRounds (keccakInput layout q row) 0 keccakDepth

/-- Lane `l` of the defect of a `KECCAK` row: the committed state minus the input's first segment
(`0` where they agree). -/
def keccakDefect (layout : Layout) {μ : ℕ} (q : Column μ) (l row : ℕ) : E :=
  ofK (K.ofLane (Keccak.lane (keccakMid layout q row) l)) -
    ofK (K.ofLane (Keccak.lane (keccakRounds (keccakInput layout q row) 0 keccakDepth) l))

/-- **The Keccak defect survives at the `KECCAK` table's row point** the link leaves: some lane's
defect has a nonzero multilinear extension there. -/
def KeccakDefectAt (layout : Layout) {μ : ℕ} (q : Column μ) (e : LinkEnd) : Prop :=
  ∃ l < keccakStateLanes, rowMle (e.columns.getD opKeccak ([], [])).1 (keccakDefect layout q l) ≠ 0

/-- The memory word at index `i` of a stack: its two limbs, the memory columns' rows. -/
def memoryImage (layout : Layout) {μ : ℕ} (q : Column μ) : MemoryImage layout.logMemory :=
  fun i ↦ E.ofLimbs (columnRow layout q memory0 i) (columnRow layout q memory1 i)

/-- **The memory holds the public input** in words `0` and `1`. -/
def PubRel (layout : Layout) {μ : ℕ} (input : PublicInput) (q : Column μ) : Prop :=
  columnRow layout q memory0 0 = input.lanes 0 ∧ columnRow layout q memory1 0 = input.lanes 1 ∧
    columnRow layout q memory0 1 = input.lanes 2 ∧ columnRow layout q memory1 1 = input.lanes 3

end

end LeanVM.Protocol.Relation

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier

@[expose] public section

/-- The two segments' rounds are the permutation. -/
theorem keccakRounds_segments (a : KeccakState) :
    keccakRounds (keccakRounds a 0 keccakDepth) keccakDepth keccakDepth = keccakF1600 a := by
  unfold keccakRounds keccakF1600
  rw [← List.foldl_append]
  rfl

/-- **With `KeccakRel`, the output the relation reads is Keccak-f[1600] of the input.** -/
theorem keccakOutput_of_keccakRel {layout : Layout} {μ : ℕ} {q : Column μ}
    (h : KeccakRel layout q) {row : ℕ} (hrow : row < 2 ^ keccakHeight layout) :
    keccakOutput layout q row = keccakF1600 (keccakInput layout q row) := by
  rw [keccakOutput, h row hrow, keccakRounds_segments]

end

end LeanVM.Protocol.Relation
