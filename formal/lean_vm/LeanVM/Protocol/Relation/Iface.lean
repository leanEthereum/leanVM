/-
  LeanVM.Protocol.Relation.Iface

  What the assembly of leanVM's knowledge soundness takes of the link and of the Keccak
  reduction: their round-by-round specifications on a committed stack, and the link's relation
  with its meaning.
-/

module

public import LeanVM.Protocol.Relation.Link.Rel
public import LeanVM.Protocol.Compile.Spec
public import LeanVM.Protocol.Compile.SpecRules.Grind
public import LeanVM.Protocol.Verifier.Deferred

/-!
# The phases' interfaces

The assembly (the walk's specification, `notes/hotwire-port.md`, M2-KS) composes the phases'
specifications on the stack candidates the commitment's out-of-domain sample leaves, a set `S` of
at most one stack (`Set.Subsingleton`), fixed before the phases run. Each phase turns "the stack
fails the relation" into "a claim the phase leaves is false of the stack", every group of challenges
within `εmsg` after its grind, and leads with at most `εmsg`, as the bus era's `FrontIface` did
(tag `formal-bus-archive`, `EndToEnd/Sound/Assemble.lean`).

* `LinkIface`: the link's relation `LinkRel` (one-hot pointers, the state, memory and program
  links, `JUMP`'s identities), the link's specification (`linkSpec`: the relation or `KeccakRel`
  failing becomes the link's end failing on the stack or the Keccak defect surviving at the
  `KECCAK` row point, which the link carries through its row rounds), and its meaning (`valid`:
  the relation, the public input and `KeccakRel` give a valid execution, the one the extractor
  reads off the stack).
* `KeccakIface`: the Keccak reduction's specification (`keccakSpec`: the link's `KECCAK` output
  lanes false, or the defect at the row point, becomes the reduction's `q_keccak` claims or its
  input slices failing).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-- The layout and rate a run's first step announces and accepts (`readAnnouncedSizes`). -/
def Announced (bytecode : List K) (layout : Layout) (ρ : ℕ) : Prop :=
  VerifierProgram.Returns (readAnnouncedSizes bytecode) (layout, ρ)

/-- The claims of the link's end on the `KECCAK` output lanes, which nothing commits: the Keccak
reduction's claim on the permutation's output. -/
def keccakOutputClaims (e : LinkEnd) : List ColumnClaim :=
  (linkColumnClaims e).filter fun c ↦ (keccakOutputLane c.column).isSome

/-- **The shape of the link's end**: the memory point over the memory's variables, one row point
per table over its height with its sent columns distinct and below the table's width (as
`verify_link`'s non-pointer columns are), and every ring piece at a placement of the layout, at a
point over its variables, and `64` ring slices. -/
def LinkShape (layout : Layout) (e : LinkEnd) : Prop :=
  e.memoryPoint.length = layout.logMemory ∧ e.columns.length = nTables ∧
    (∀ t < nTables, (e.columns.getD t ([], [])).1.length = layout.tableLogHeights.getD t 0) ∧
    (∀ t < nTables, ((e.columns.getD t ([], [])).2.map Prod.fst).Nodup ∧
      ∀ x ∈ (e.columns.getD t ([], [])).2, x.1 < tableWidths.getD t 0) ∧
    (∀ piece ∈ e.ring.pieces, ∃ c p, layout.placements.getD c none = some p ∧
      piece.placement = some p ∧ piece.point.length = p.variableCount) ∧
    e.ring.slices.length = kBits

/-- **The shape of the Keccak reduction's result**: its column claims on `q_keccak` at points over
`q_keccak`'s variables, its ring point over them too, `64` slices, and at most one claim. -/
def KeccakShape (layout : Layout) (r : List ColumnClaim × List E × List E) : Prop :=
  (∀ c ∈ r.1, c.column = qkeccak ∧ c.point.length = keccakHeight layout + qkeccakSlotBits) ∧
    r.2.1.length = keccakHeight layout + qkeccakSlotBits ∧ r.2.2.length = kBits ∧ r.1.length ≤ 1

/-- **What the assembly takes of the link.** -/
structure LinkIface : Type 1 where
  /-- The link's part of the relation on a stack. -/
  LinkRel : (layout : Layout) → Column layout.stackLog → Prop
  /-- **The link, round by round**: from the relation failing (the link's part, or `q_keccak`'s
  first segment) on every candidate, its end fails on the candidate or the Keccak defect survives
  at the `KECCAK` row point; every group within `εmsg` after its grind. -/
  linkSpec : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
    ∀ (S : Set (Column layout.stackLog)), S.Subsingleton → ∀ T : ENNReal, T ≤ εmsg →
    Spec (verifyLink computedSplit layout)
      (fun _ ↦ ∀ q ∈ S, ¬ LinkRel layout q ∨ ¬ KeccakRel layout q)
      (fun e _ ↦ ∀ q ∈ S, ¬ LinkEndHolds layout q e ∨ KeccakDefectAt layout q e) εmsg εmsg T
  /-- What the link returns has its shape. -/
  linkShape : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
    ∀ e, VerifierProgram.Returns (verifyLink computedSplit layout) e → LinkShape layout e
  /-- **The relation's meaning**: a stack satisfying it, whose memory holds the public input and
  whose `q_keccak` holds the first segments, gives a valid execution, the one read off it. -/
  valid : ∀ (program : LeanIsaProgram) (input : PublicInput) (layout : Layout) (ρ : ℕ)
    (q : Column layout.stackLog), Announced (bytecodeWords program) layout ρ →
    LinkRel layout q → PubRel layout input q → KeccakRel layout q →
    ValidExecution program input (candidate program layout q)

/-- **What the assembly takes of the Keccak reduction.** -/
structure KeccakIface : Type where
  /-- **The Keccak reduction, round by round**: from the link's `KECCAK` output-lane claims failing,
  or the Keccak defect surviving at their point, on every candidate, its `q_keccak` claims or its
  ring claim (the input slices on `q_keccak`) fail on the candidate; every group within `εmsg`
  after its grind. Its first group (the segment and lane challenges, whose grind is zero bits)
  joins the public input's challenge and the link's last boundary, so its lead is its own error
  `(keccakSegmentBits + keccakLaneBits)/|E|` and the follower's. -/
  keccakSpec : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
    ∀ (link : LinkEnd), LinkShape layout link →
    ∀ (qk : Placement), layout.placements.getD qkeccak none = some qk →
    ∀ (S : Set (Column layout.stackLog)), S.Subsingleton → ∀ T : ENNReal, T ≤ εmsg →
    Spec (keccakValidity layout link)
      (fun _ ↦ ∀ q ∈ S,
        ¬ (∀ c ∈ keccakOutputClaims link, ColumnClaimHolds layout q c) ∨
          KeccakDefectAt layout q link)
      (fun r _ ↦ ∀ q ∈ S,
        ¬ (∀ c ∈ r.1, ColumnClaimHolds layout q c) ∨
          ¬ RingClaimHolds q (keccakRingClaim qk r.2.1 r.2.2)) εmsg
      (((keccakSegmentBits + keccakLaneBits : ℕ) : ENNReal) / Fintype.card E + T) T
  /-- What the reduction returns has its shape. -/
  keccakShape : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
    ∀ (link : LinkEnd), LinkShape layout link →
    ∀ r, VerifierProgram.Returns (keccakValidity layout link) r → KeccakShape layout r

end

end LeanVM.Protocol.Relation
