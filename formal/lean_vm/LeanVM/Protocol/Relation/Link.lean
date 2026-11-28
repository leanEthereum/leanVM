/-
  LeanVM.Protocol.Relation.Link

  The link's interface for the knowledge-soundness assembly, from the link's arithmetization, its
  end's shape and each executed row's leanISA step; and the axioms of what is proved.
-/

module

public import LeanVM.Protocol.Relation.Link.Rel
public import LeanVM.Protocol.Relation.Link.Rounds
public import LeanVM.Protocol.Relation.Link.Tail
public import LeanVM.Protocol.Relation.Link.Spec
public import LeanVM.Protocol.Relation.Link.Chain
public import LeanVM.Protocol.Relation.Link.Valid
public import LeanVM.Protocol.Relation.Link.Shape
public import LeanVM.Protocol.Relation.Link.Steps
public import LeanVM.Protocol.Relation.Link.KeccakStep
public import LeanVM.Protocol.Relation.Link.Facts
public import LeanVM.Protocol.Relation.Link.Summand
public import LeanVM.Protocol.Relation.Link.TailEq
public import LeanVM.Protocol.Relation.Link.Affine
public import LeanVM.Protocol.Relation.Link.Group
public import LeanVM.Protocol.Relation.Link.IdxDeg
public import LeanVM.Protocol.Relation.Link.GroupJump
public import LeanVM.Protocol.Relation.Link.RowDeg

/-!
# The link, for the assembly

`LinkIface` (`Iface.lean`) asks of the link its relation, its round-by-round specification, the
shape of its end and the relation's meaning. `linkIfaceOf` gives it from one fact still
to discharge for leanVM's tables (`notes/hotwire-port.md`, M2-A):

* `harith`: the link's arithmetization proper at every candidate and the link's chunks
  (`LinkCore`, `Link/Spec.lean`), from which, with the layout's facts (`linkArith_of_core`,
  `Link/Facts.lean`), `linkSpecSet` is the specification.

Each executed row takes one leanISA step under the relation (`rowStep_of_rel`, `Link/Steps.lean`;
`KECCAK`'s under `KeccakRel` too, `keccakRowSteps_of_rel`, `Link/KeccakStep.lean`), and
`valid_of_rowSteps` is the meaning.

The modules:

* `Link/Rel.lean`: `LinkRel` (one-hot pointers, the state link's identity, the memory and program
  lookups, `JUMP`'s constraints) and the extracted execution, `candidate`, which runs to the first
  cycle in the final state (`firstFinal`);
* `Link/Rounds.lean`: the plain sum-check round by round with a carried fact (`roundsSpec`);
* `Link/Tail.lean`: `linkTail` as a packed read, a check and a return (`linkTail_eq`);
* `Link/Spec.lean`: the arithmetization package and `verifyLink` round by round (`linkSpecOf`,
  `linkSpecSet`);
* `Link/Facts.lean`: the package's facts of the layout alone (`linkArith_of_core`);
* `Link/Shape.lean`: the shape of what `verifyLink` returns (`linkShape_holds`);
* `Link/Chain.lean`, `Link/Valid.lean`: a chain of steps runs; the relation with the rows' steps
  gives a valid execution (`valid_of_rowSteps`);
* `Link/Steps.lean`, `Link/KeccakStep.lean`: each executed row's leanISA step.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Link

@[expose] public section

/-- **The link's interface**, from its arithmetization; the end's shape is `linkShape_holds`, the
rows' steps `rowStep_of_rel` and `keccakRowSteps_of_rel`. -/
noncomputable def linkIfaceOf
    (harith : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
      ∀ (q : Column layout.stackLog) (chunks : Chunks),
        Chunks.new (linkWidth layout) = some chunks → LinkCore layout q chunks) :
    LinkIface where
  LinkRel layout q := Relation.LinkRel layout q
  linkSpec bytecode layout ρ hA S hS _ hT := linkSpecSet layout
    (fun q chunks hch ↦ linkArith_of_core hA hch (harith bytecode layout ρ hA q chunks hch)) S hS hT
  linkShape := linkShape_holds
  valid program input layout ρ q hA hrel hpub hk := by
    have hst := rowStep_of_rel hA hrel (keccakRowSteps_of_rel hA hrel hk)
    obtain ⟨chunks, hch, -, hs, -⟩ := hrel
    exact valid_of_rowSteps program input layout ρ q hA hch hs hpub hst

open Classical in
/-- **The summands' facts at an announced layout** from the three degree bounds and the drawn
group's count: the terminal check is `tail_of_summand`, the row side's total
`row_total_of_summand`. -/
theorem linkSummandFacts_of {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) (chunks : Chunks)
    (hidx : ∀ theta0 drawn, PerVarDegAt (linkIdxAt layout chunks q theta0 drawn) chunks.width
      fun _ ↦ 2)
    (hB : ∀ theta0 drawn i,
      PerVarDeg (fun r ↦ linkB layout chunks q theta0 drawn r i) chunks.width 2)
    (hrow : ∀ theta0 drawn r fresh, PerVarDegAt (rowSummand layout chunks q theta0 drawn r fresh)
      (linkRowVars layout)
      (rowDegrees (linkRows layout) (roundCoefficients chunks.d).1 (roundCoefficients chunks.d).2))
    (hgroup : (¬ LinkRel layout q ∨ ¬ KeccakRel layout q) →
      (Finset.univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
        ¬ RoundDoom True (linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail)
          (IndexCarry layout q chunks (linkB layout chunks q) ((List.ofFn v).headD 0)
            (List.ofFn v).tail)
          (indexClaim layout chunks (List.ofFn v).tail) []).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks) :
    LinkSummandFacts layout q chunks := by
  have hT := (announced_facts hA).2.1
  exact { idx_deg := hidx, B_deg := hB, row_deg := hrow
          row_total := row_total_of_summand layout hT chunks q
          group := hgroup
          tail := tail_of_summand layout q chunks (by rw [hT, tables_length]; decide) }

/-- **The link's interface from its summands' facts** (`LinkSummandFacts`, `Link/Summand.lean`). -/
noncomputable def linkIfaceOfFacts
    (hfacts : ∀ (bytecode : List K) (layout : Layout) (ρ : ℕ), Announced bytecode layout ρ →
      ∀ (q : Column layout.stackLog) (chunks : Chunks),
        Chunks.new (linkWidth layout) = some chunks → LinkSummandFacts layout q chunks) :
    LinkIface :=
  linkIfaceOf fun bytecode layout ρ hA q chunks hch ↦ linkCoreOf (hfacts bytecode layout ρ hA q chunks hch)

open Classical in
/-- **The link's interface from the failing links' count** (`card_notDoom_of_links`'s statement):
the degrees are `linkSummand_degs` and `row_deg_of_summand`, the drawn group's count
`linkGroup_of_jump_links` with `card_notDoom_of_not_constraints`. -/
noncomputable def linkIfaceOfLinks
    (hLinks : ∀ {bytecode : List K} {layout : Layout} {ρ : ℕ}, Announced bytecode layout ρ →
      ∀ {μ : ℕ} (q : Column μ) {chunks : Chunks}, Chunks.new (linkWidth layout) = some chunks →
      PointersOneHot layout q chunks → ConstraintsHold layout q → KeccakRel layout q →
      ¬ (StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks) →
      (Finset.univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks) :
    LinkIface :=
  linkIfaceOfFacts fun _ _ _ hA q chunks hch ↦
    linkSummandFacts_of hA q chunks (linkSummand_degs q hch).1 (linkSummand_degs q hch).2
      (fun theta0 drawn r fresh ↦
        row_deg_of_summand (announced_facts hA).2.1 chunks q theta0 drawn r fresh)
      (linkGroup_of_jump_links hA q hch (card_notDoom_of_not_constraints hA q hch)
        (hLinks hA q hch))

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.linkSummandFacts_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkSummandFacts_of

/-- info: 'LeanVM.Protocol.Relation.tail_of_summand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.tail_of_summand

/-- info: 'LeanVM.Protocol.Relation.row_total_of_summand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.row_total_of_summand

/-- info: 'LeanVM.Protocol.Relation.linkIfaceOfFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkIfaceOfFacts

/-- info: 'LeanVM.Protocol.Relation.linkIfaceOfLinks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkIfaceOfLinks

/-- info: 'LeanVM.Protocol.Relation.linkSpecOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkSpecOf

/-- info: 'LeanVM.Protocol.Relation.linkSpecSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkSpecSet

/-- info: 'LeanVM.Protocol.Relation.roundsSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.roundsSpec

/-- info: 'LeanVM.Protocol.Relation.valid_of_rowSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.valid_of_rowSteps

/-- info: 'LeanVM.Protocol.Relation.linkIfaceOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkIfaceOf

/-- info: 'LeanVM.Protocol.Link.linkTail_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Link.linkTail_eq

/-- info: 'LeanVM.Protocol.Relation.linkShape_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkShape_holds

/-- info: 'LeanVM.Protocol.Relation.linkArith_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkArith_of_core

/-- info: 'LeanVM.Protocol.Relation.keccakRowSteps_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.keccakRowSteps_of_rel

/-- info: 'LeanVM.Protocol.Relation.rowStep_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.rowStep_of_rel

/-- info: 'LeanVM.Protocol.Relation.linkGroup_of_jump_links' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkGroup_of_jump_links

/-- info: 'LeanVM.Protocol.Relation.linkB_zero_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkB_zero_closed
