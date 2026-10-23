import SphincsFors.SecurityHiddenRows
import SphincsFors.SecurityPrefixOracle
import SphincsFors.SecurityPosition
import SphincsFors.SecurityPrunedGraph

/-! A concrete programmed graph for the candidate's one-digest hash inputs. Canonical
chain and FORS-leaf answers are programmed from independent digest coordinates. Ordinary
queries are monitored before a hidden input can expose its successor. -/

open OracleComp OracleSpec ENNReal
namespace SphincsFors.Security.HiddenGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable

inductive Coordinate where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
      (position : Digit)
  | ftsSecret (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsValue (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  deriving DecidableEq, Fintype

noncomputable local instance : DecidableEq Coordinate := Classical.decEq _

inductive Address where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  deriving DecidableEq, Fintype

def Address.position : Address → Position
  | .chain lay tree leaf chainIdx step => .chain lay tree leaf chainIdx step
  | .ftsLeaf index tree leaf => .ftsLeaf index tree leaf

def Address.inputCoordinate : Address → Coordinate
  | .chain lay tree leaf chainIdx step =>
      .chain lay tree leaf chainIdx ⟨step.val, by have := step.isLt; omega⟩
  | .ftsLeaf index tree leaf => .ftsSecret index tree leaf

def Address.outputCoordinate : Address → Coordinate
  | .chain lay tree leaf chainIdx step =>
      .chain lay tree leaf chainIdx ⟨step.val + 1, by have := step.isLt; omega⟩
  | .ftsLeaf index tree leaf => .ftsValue index tree leaf

/-- Only the retained WOTS chains and the FORS rows are programmed for a pruned key. -/
def candidateActive [Params] (parameter : PublicParameter) (address : Address) : Prop :=
  PrunedGraph.active parameter address.position

def input (parameter : PublicParameter) (query : Address × Digest) : HashInput :=
  tweakableHashInput parameter query.1.position.domain (bytesLE 16 query.2)

theorem input_injective (parameter : PublicParameter) : Function.Injective (input parameter) := by
  intro left right heq
  have hfields := (tweakableInput_injective heq).1
  have hpayload := (tweakableInput_injective heq).2.2
  have hposition := Position.domain_injective
    (hashFields_injective left.1.position.domain_inRange right.1.position.domain_inRange hfields)
  have haddress : left.1 = right.1 := by
    cases hleft : left.1 <;> cases hright : right.1 <;>
      simp only [hleft, hright, Address.position, Position.chain.injEq,
        Position.ftsLeaf.injEq, reduceCtorEq] at hposition <;> simp_all
  exact Prod.ext haddress (bytesLE_injective hpayload)

noncomputable def parse (parameter : PublicParameter) (active : Address → Prop) (bytes : HashInput) :
    Option (Address × Digest) :=
  if h : ∃ query, input parameter query = bytes ∧ active query.1 then some h.choose else none

theorem parse_some_iff (parameter : PublicParameter) (active : Address → Prop) (bytes : HashInput) (query : Address × Digest) :
    parse parameter active bytes = some query ↔ bytes = input parameter query ∧ active query.1 := by
  unfold parse
  split
  · rename_i hex
    rw [Option.some.injEq]
    constructor
    · intro heq; rw [← heq]; exact ⟨hex.choose_spec.1.symm, hex.choose_spec.2⟩
    · intro heq; exact input_injective parameter (hex.choose_spec.1.trans heq.1)
  · rename_i hnone
    constructor
    · intro h; cases h
    · intro heq; exact False.elim (hnone ⟨query, heq.1.symm, heq.2⟩)

theorem parse_input (parameter : PublicParameter) (active : Address → Prop) (query : Address × Digest) (hactive : active query.1) :
    parse parameter active (input parameter query) = some query :=
  (parse_some_iff parameter active _ query).mpr ⟨rfl, hactive⟩

attribute [local irreducible] parse input Prefix.combine

abbrev Table := Coordinate → Digest
abbrev Knowledge := HiddenReveal.Knowledge Coordinate

/-- The high half of every canonical answer remains explicit and adversary visible. -/
noncomputable def answer (parameter : PublicParameter) (active : Address → Prop) (table : Table)
    (high : Address → Prefix.High) (outside : HashInput → HashOutput) : HashInput → HashOutput :=
  fun bytes => (parse parameter active bytes).elim (outside bytes) fun query =>
    if query.2 = table query.1.inputCoordinate then
      Prefix.combine (table query.1.outputCoordinate) (high query.1)
    else outside bytes

theorem answer_canonical (parameter : PublicParameter) (active : Address → Prop) (table : Table)
    (high : Address → Prefix.High) (outside : HashInput → HashOutput) (address : Address) (hactive : active address) :
    answer parameter active table high outside (input parameter (address, table address.inputCoordinate)) =
      Prefix.combine (table address.outputCoordinate) (high address) := by
  rw [answer, parse_input _ _ _ hactive]
  exact ite_eq_left rfl

/-- The parser enforces the candidate's complete byte layout and retained-row selection.
The generic compiler therefore has only one possible input coordinate for each raw query. -/
noncomputable def rowModel (parameter : PublicParameter) (active : Address → Prop)
    (high : Address → Prefix.High) : HiddenRows.Model HashInput HashOutput Address Coordinate where
  parse := parse parameter active
  incoming := Address.inputCoordinate
  outgoing := Address.outputCoordinate
  combine := fun address value => Prefix.combine value (high address)

theorem rowModel_answer (parameter : PublicParameter) (active : Address → Prop)
    (table : Table) (high : Address → Prefix.High) (outside : HashInput → HashOutput) :
    HiddenRows.answer (rowModel parameter active high) table outside =
      answer parameter active table high outside := rfl

abbrev SourceSpec := HiddenRows.SourceSpec HashInput HashOutput Coordinate
abbrev KnownAgrees := @HiddenRows.KnownAgrees Coordinate

noncomputable abbrev stopped {α : Type} (parameter : PublicParameter) (active : Address → Prop)
    (table : Table) (high : Address → Prefix.High) (outside : HashInput → HashOutput)
    (computation : OracleComp SourceSpec α) (known : Knowledge) :=
  HiddenRows.stopped (rowModel parameter active high) table outside computation known

noncomputable abbrev stoppedExperiment {α : Type} (parameter : PublicParameter)
    (active : Address → Prop) (high : Address → Prefix.High) (outside : HashInput → HashOutput)
    (computation : OracleComp SourceSpec α) (known : Knowledge) :=
  HiddenRows.stoppedExperiment (rowModel parameter active high) outside computation known

end SphincsFors.Security.HiddenGraph
