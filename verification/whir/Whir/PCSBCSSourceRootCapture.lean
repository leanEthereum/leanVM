import Whir.PCSBCSFirstRootDisclosure
import Whir.PCSBCSChallengeOracleEnteredErasure
import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSSourceRootReferences

/-! In the grouped mixed game, root images are reconstructed from actual
ordinary primitive records preceding the first shape-address mention. Source
packet answers are not invented Merkle preimages. Identifying this prefix with
the physical compression trace is a separate coupling/refinement obligation. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceRootCapture
open Concrete Protocol CausalGame CausalProbability PCSBCSRounds
open FiatShamirGame TypedOracleCompiler TypedFiatShamirGame
open PCSBCSChallengeOracle PCSBCSMerkleRootCache PCSBCSSourceRootReferences
open Classical PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}

abbrev Key := (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Key
abbrev Answer := (EnteredPacket.partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).Answer
  (D := Digest32)
local notation "Keys" => Key (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Only the primitive-query summand contains public compression records.
Other construction queries cannot supply a made-up hash preimage. -/
def ordinaryRecord (event : Sigma (Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary))) :
    DuplexPublicSimulator.PublicLog :=
  match event with
  | ⟨.inl _,_⟩ => []
  | ⟨.inr other,answer⟩ =>
    match other.val with
    | .inl input => [(input,answer)]
    | .inr _ => []

def ordinaryPrefix (events : List (Sigma
    (Answer (p := p) (Q := Q) (iv := iv) (boundary := boundary)))) :
    DuplexPublicSimulator.PublicLog :=
  events.foldl (fun log event => ordinaryRecord event ++ log) []

/-- A missing first mention returns no captured root, not an authenticated
zero table. Genuine absent leaf images retain the cache's explicit status. -/
noncomputable def capture {R : Type} {n : Nat}
    (address : Key (p := p) (Q := Q) (iv := iv) (boundary := boundary) → List Reference)
    (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) : Option Frozen :=
  (PCSBCSFirstRootDisclosure.firstMention address ref program table).map fun events =>
    freeze (ordinaryPrefix events) ref.root ref.shape

/-- This reconstructs the complete image and compact suffix from a prefix of
actual records, while erasing the whole current packet before metadata lookup. -/
theorem capture_answer_independent {R : Type} {n : Nat}
    (address : Key (p := p) (Q := Q) (iv := iv) (boundary := boundary) → List Reference)
    (current : EnteredPacket p Q iv boundary) (ref : Reference)
    (mentioned : ref ∈ address (.inl current))
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (full : Fin (blocks (rawWidth current.2.coord)) → Digest32) :
    capture address ref program (Function.update table (.inl current) full) =
      capture address ref program table := by
  unfold capture
  rw [PCSBCSFirstRootDisclosure.first_mention_answer_independent address
    (.inl current) ref mentioned program table full]

/-- A ghost completion only: the selected packet is never read before its
address mention. The following theorem removes the inert completion exactly. -/
noncomputable def otherTable (current : EnteredPacket p Q iv boundary)
    (other : current.OtherValues) : Table Keys Answers :=
  fun key => if same : key = .inl current then by
    subst key
    exact fun _ _ => 0
  else other ⟨key,same⟩

noncomputable def captureOther {R : Type} {n : Nat}
    (address : Key (p := p) (Q := Q) (iv := iv) (boundary := boundary) → List Reference)
    (current : EnteredPacket p Q iv boundary) (ref : Reference)
    (program : Sampling Keys Answers R n) (other : current.OtherValues) : Option Frozen :=
  capture address ref program (otherTable current other)

theorem captureOther_table {R : Type} {n : Nat}
    (address : Key (p := p) (Q := Q) (iv := iv) (boundary := boundary) → List Reference)
    (current : EnteredPacket p Q iv boundary) (ref : Reference)
    (mentioned : ref ∈ address (.inl current))
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) :
    captureOther address current ref program (fun key => table key.val) =
      capture address ref program table := by
  have same : otherTable current (fun key => table key.val) =
      Function.update table (.inl current) (fun _ _ => 0) := by
    funext key
    by_cases equal : key = .inl current
    · subst key
      simp [otherTable]
    · simp [otherTable,equal]
  unfold captureOther
  rw [same]
  exact capture_answer_independent address current ref mentioned program table (fun _ _ => 0)


/-- An actually queried shape reference has a genuine earlier capture.
Nothing asserts that this capture already contains every leaf preimage. -/
theorem capture_exists {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (key : Keys) (mentioned : ref ∈ address key)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (visited : key ∈ ((Sampling.execute table program).2.map Sigma.fst)) :
    ∃ frozen, capture address ref program table = some frozen := by
  obtain ⟨events,found⟩ := PCSBCSFirstRootDisclosure.first_mention_exists
    address key ref mentioned program table visited
  exact ⟨freeze (ordinaryPrefix events) ref.root ref.shape,by
    simp only [capture,found,Option.map_some]⟩

/-- Source accessors receive the actual indexed prefix, not an arbitrary
digest-to-oracle map or a promise that a Merkle root is honestly generated. -/
theorem capture_provenance {R : Type} {n : Nat}
    (address : Keys → List Reference) (ref : Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (frozen : Frozen) (captured : capture address ref program table = some frozen) :
    ∃ events, PCSBCSFirstRootDisclosure.firstMention address ref program table = some events ∧
      frozen = freeze (ordinaryPrefix events) ref.root ref.shape ∧ events.length ≤ n := by
  unfold capture at captured
  obtain ⟨events,found,equal⟩ := Option.map_eq_some_iff.mp captured
  exact ⟨events,found,equal.symm,
    PCSBCSFirstRootDisclosure.first_mention_length address ref program table events found⟩

#print axioms capture_exists
#print axioms capture_provenance

#print axioms capture_answer_independent
#print axioms captureOther_table
end Whir.PCSBCSSourceRootCapture
