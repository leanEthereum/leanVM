import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CanonicalHiddenCoordinates
import SphincsSecurity.Proof.Ots.EncodingSelectionCache
import SphincsSecurity.Proof.Scheme.FirstBad
import SphincsSecurity.Proof.Fts.HiddenLabelObservation
import SphincsSecurity.Proof.Fts.FtsProbeSimulation
import SphincsSecurity.Proof.Ots.OtsProbeSimulation
namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp OracleSpec HiddenLabelObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev Labels := CanonicalCoordinate → Digest

def inputOf (parameter : PublicParameter) (values : Labels) (position : Position) : HashInput :=
  tweakableHashInput parameter position.domain
    (((CanonicalCoordinate.slots position).map values).flatMap digestBytes)

theorem inputOf_canonical (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (position : Position) :
    inputOf parameter (CanonicalCoordinate.value otsSecret ftsSecret labels) position =
      canonicalGraphInput parameter otsSecret ftsSecret position labels := by
  rw [inputOf, CanonicalCoordinate.values_slots, canonicalGraphInput]

theorem inputOf_unary (parameter : PublicParameter) (values : Labels) (position : Position)
    (coordinate : CanonicalCoordinate) (hslot : CanonicalCoordinate.slots position = [coordinate]) :
    inputOf parameter values position = tweakableHashInput parameter position.domain (digestBytes (values coordinate)) := by
  simp only [inputOf, hslot, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem unary_eq_inputOf_iff (parameter : PublicParameter) (values : Labels) (position : Position)
    (coordinate : CanonicalCoordinate) (hslot : CanonicalCoordinate.slots position = [coordinate]) (candidate : Digest) :
    tweakableHashInput parameter position.domain (digestBytes candidate) = inputOf parameter values position ↔
      candidate = values coordinate := by
  rw [inputOf_unary parameter values position coordinate hslot]
  constructor
  · intro h
    exact digestBytes_injective (tweakableHashInput_injective parameter position.domain_inRange position.domain_inRange h).2
  · rintro rfl
    rfl

noncomputable def decodePosition (parameter : PublicParameter) (input : HashInput) : Option Position :=
  letI : Decidable (∃ position, AtPosition parameter input position) := Classical.propDecidable _
  if h : ∃ position, AtPosition parameter input position then some h.choose else none

theorem decodePosition_some_iff (parameter : PublicParameter) (input : HashInput) (position : Position) :
    decodePosition parameter input = some position ↔ AtPosition parameter input position := by
  unfold decodePosition
  split
  · rename_i h
    constructor
    · intro heq
      have heq := Option.some.inj heq
      exact heq ▸ h.choose_spec
    · intro hat
      exact congrArg some (atPosition_unique parameter h.choose_spec hat)
  · rename_i h
    constructor
    · simp
    · intro hat
      exact (h ⟨position, hat⟩).elim

theorem decodePosition_none_iff (parameter : PublicParameter) (input : HashInput) :
    decodePosition parameter input = none ↔ ∀ position, ¬AtPosition parameter input position := by
  constructor
  · intro hnone position hat
    have hsome := (decodePosition_some_iff parameter input position).mpr hat
    rw [hnone] at hsome
    cases hsome
  · intro hnone
    cases hdecode : decodePosition parameter input with
    | none => rfl
    | some position => exact (hnone position ((decodePosition_some_iff parameter input position).mp hdecode)).elim

noncomputable def decodeUnary (parameter : PublicParameter) (position : Position) (input : HashInput) : Option Digest :=
  letI : Decidable (∃ value, input = tweakableHashInput parameter position.domain (digestBytes value)) := Classical.propDecidable _
  if h : ∃ value, input = tweakableHashInput parameter position.domain (digestBytes value) then some h.choose else none

theorem decodeUnary_some_iff (parameter : PublicParameter) (position : Position) (input : HashInput) (candidate : Digest) :
    decodeUnary parameter position input = some candidate ↔
      input = tweakableHashInput parameter position.domain (digestBytes candidate) := by
  unfold decodeUnary
  split
  · rename_i h
    constructor
    · intro heq
      have heq := Option.some.inj heq
      exact heq ▸ h.choose_spec
    · intro hinput
      apply congrArg some
      exact digestBytes_injective
        (tweakableHashInput_injective parameter position.domain_inRange position.domain_inRange
          (h.choose_spec.symm.trans hinput)).2
  · rename_i h
    constructor
    · simp
    · intro hinput
      exact (h ⟨candidate, hinput⟩).elim

theorem decodeUnary_none_ne (parameter : PublicParameter) (position : Position) (input : HashInput)
    (hnone : decodeUnary parameter position input = none) (candidate : Digest) :
    input ≠ tweakableHashInput parameter position.domain (digestBytes candidate) := by
  intro hinput
  have hsome := (decodeUnary_some_iff parameter position input candidate).mpr hinput
  rw [hnone] at hsome
  cases hsome

def HasHiddenChild (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (position : Position) : Prop :=
  ∃ coordinate ∈ CanonicalCoordinate.slots position, CanonicalCoordinate.Hidden words disclosed coordinate

def PublicAgreement (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (known actual : Labels) : Prop :=
  ∀ coordinate, ¬CanonicalCoordinate.Hidden words disclosed coordinate → known coordinate = actual coordinate

theorem inputOf_public (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (position : Position)
    (hpublic : ¬HasHiddenChild words disclosed position) :
    inputOf parameter known position = inputOf parameter actual position := by
  have hvalues : (CanonicalCoordinate.slots position).map known = (CanonicalCoordinate.slots position).map actual := by
    apply List.map_congr_left
    intro coordinate hcoordinate
    exact hagrees coordinate (fun hhidden => hpublic ⟨coordinate, hcoordinate, hhidden⟩)
  rw [inputOf, inputOf, hvalues]

theorem parent_public_of_no_hidden_child (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (position : Position)
    (hpublic : ¬HasHiddenChild words disclosed position) :
    ¬CanonicalCoordinate.Hidden words disclosed (.graph position) := by
  intro hhidden
  cases position
  case chain lay tree leaf chain step =>
    apply hpublic
    refine ⟨CanonicalCoordinate.chainChild lay tree leaf chain step, ?_, ?_⟩
    · rw [CanonicalCoordinate.slots_chain]
      exact List.mem_singleton_self _
    · apply (CanonicalCoordinate.hidden_chain_child_iff words disclosed lay tree leaf chain step).mpr
      change step.val + 1 < (words lay tree leaf chain).val at hhidden
      omega
  all_goals exact hhidden

inductive Route where
  | outside
  | canonical (position : Position)
  | probe (request : Probe CanonicalCoordinate)

noncomputable def routeAt (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (position : Position) (input : HashInput) : Route :=
  if h : HasHiddenChild words disclosed position then
    match decodeUnary parameter position input with
    | some candidate => .probe (.pair h.choose (.graph position)
        (CanonicalCoordinate.slots_ne_parent position h.choose h.choose_spec.1) candidate)
    | none => .probe (.output (.graph position))
  else if input = inputOf parameter known position then .canonical position else .probe (.output (.graph position))

noncomputable def route (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput) : Route :=
  (decodePosition parameter input).elim .outside (fun position => routeAt parameter words disclosed known position input)

def RouteSpec (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (input : HashInput) : Route → Prop
  | .outside => ∀ position, ¬AtPosition parameter input position
  | .canonical position => AtPosition parameter input position ∧ input = inputOf parameter actual position ∧
      ¬HasHiddenChild words disclosed position
  | .probe (.pair child parent _ candidate) => ∃ position, AtPosition parameter input position ∧ parent = .graph position ∧
      CanonicalCoordinate.slots position = [child] ∧ CanonicalCoordinate.Hidden words disclosed child ∧
      input = tweakableHashInput parameter position.domain (digestBytes candidate)
  | .probe (.output parent) => ∃ position, AtPosition parameter input position ∧ parent = .graph position ∧
      input ≠ inputOf parameter actual position

theorem routeAt_spec (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (position : Position) (input : HashInput)
    (hat : AtPosition parameter input position) :
    RouteSpec parameter words disclosed actual input (routeAt parameter words disclosed known position input) := by
  unfold routeAt
  split
  · rename_i hhidden
    have hslot := CanonicalCoordinate.hidden_slot_unary words disclosed position hhidden.choose
      hhidden.choose_spec.1 hhidden.choose_spec.2
    cases hdecode : decodeUnary parameter position input with
    | none =>
        refine ⟨position, hat, rfl, ?_⟩
        rw [inputOf_unary parameter actual position hhidden.choose hslot]
        exact decodeUnary_none_ne parameter position input hdecode _
    | some candidate =>
        exact ⟨position, hat, rfl, hslot, hhidden.choose_spec.2,
          (decodeUnary_some_iff parameter position input candidate).mp hdecode⟩
  · rename_i hpublic
    have heq := inputOf_public parameter words disclosed known actual hagrees position hpublic
    split
    · rename_i hinput
      exact ⟨hat, hinput.trans heq, hpublic⟩
    · rename_i hinput
      exact ⟨position, hat, rfl, fun h => hinput (h.trans heq.symm)⟩

theorem route_spec (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (input : HashInput) :
    RouteSpec parameter words disclosed actual input (route parameter words disclosed known input) := by
  rw [route]
  cases hdecode : decodePosition parameter input with
  | none => exact (decodePosition_none_iff parameter input).mp hdecode
  | some position =>
      exact routeAt_spec parameter words disclosed known actual hagrees position input
        ((decodePosition_some_iff parameter input position).mp hdecode)

def BadAt (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (position : Position) (input : HashInput) (answer : HashOutput) : Prop :=
  (HasHiddenChild words disclosed position ∧ input = inputOf parameter actual position) ∨
    (input ≠ inputOf parameter actual position ∧ truncateHash answer = actual (.graph position))

def Bad (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ position, AtPosition parameter input position ∧ BadAt parameter words disclosed actual position input answer

theorem bad_iff_at (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (position : Position)
    (input : HashInput) (hat : AtPosition parameter input position) (answer : HashOutput) :
    Bad parameter words disclosed actual input answer ↔ BadAt parameter words disclosed actual position input answer := by
  constructor
  · rintro ⟨other, hother, hbad⟩
    have heq := atPosition_unique parameter hother hat
    exact heq ▸ hbad
  · intro hbad
    exact ⟨position, hat, hbad⟩

def Safe (actual : Labels) (answer : HashOutput) : Route → Prop
  | .probe request => request.keep actual answer
  | _ => True

theorem safe_iff_not_bad (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (input : HashInput)
    (routing : Route) (hspec : RouteSpec parameter words disclosed actual input routing) (answer : HashOutput) :
    Safe actual answer routing ↔ ¬Bad parameter words disclosed actual input answer := by
  cases routing with
  | outside =>
      constructor
      · intro _ hbad
        obtain ⟨position, hat, _⟩ := hbad
        exact hspec position hat
      · intro _
        trivial
  | canonical position =>
      obtain ⟨hat, hinput, hpublic⟩ := hspec
      rw [bad_iff_at parameter words disclosed actual position input hat answer]
      simp only [Safe, BadAt, hinput, hpublic, false_and, ne_eq, not_true_eq_false, or_self, not_false_eq_true]
  | probe request =>
      cases request with
      | pair child parent hne candidate =>
          obtain ⟨position, hat, rfl, hslot, hhidden, hinput⟩ := hspec
          have hhas : HasHiddenChild words disclosed position := ⟨child, by rw [hslot]; exact List.mem_singleton_self _, hhidden⟩
          have heq : input = inputOf parameter actual position ↔ candidate = actual child := by
            rw [hinput, unary_eq_inputOf_iff parameter actual position child hslot candidate]
          rw [bad_iff_at parameter words disclosed actual position input hat answer]
          simp only [Safe, Probe.keep, BadAt, hhas, true_and, heq]
          tauto
      | output parent =>
          obtain ⟨position, hat, rfl, hinput⟩ := hspec
          rw [bad_iff_at parameter words disclosed actual position input hat answer]
          simp only [Safe, Probe.keep, BadAt, hinput, and_false, not_false_eq_true, true_and, false_or, ne_eq, eq_comm]

end SphincsSecurity.Concrete.CanonicalProbeRouting
