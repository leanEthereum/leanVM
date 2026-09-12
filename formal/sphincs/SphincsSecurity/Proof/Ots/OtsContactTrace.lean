import SphincsSecurity.Proof.Ots.OtsPrefixVisibleTrace
import SphincsSecurity.Proof.Ots.OtsPrefixAllocation
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

abbrev Trace := FreeMonoid (HashInput × HashOutput)

def EntryContact (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) : Prop :=
  ∃ query : segment.Query, segment.parse entry.1 = some query ∧ query.1.val + 1 = segment.digit.val ∧ truncateHash entry.2 = endpoint

def Seen (segment : OtsPrefix) (endpoint : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, EntryContact segment endpoint entry

theorem entryContact_selects (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput)
    (h : EntryContact segment endpoint entry) : segment.Selects (.inr entry.1) := by
  obtain ⟨query, hquery, _⟩ := h
  change segment.parse entry.1 ≠ none
  rw [hquery]
  exact Option.some_ne_none query

theorem entryContact_unique (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) (left right : OtsPrefix.ChainAddress)
    (hleft : EntryContact (OtsPrefix.atAddress parameter words left) (frontier left.1 left.2.1 left.2.2.1 left.2.2.2) entry)
    (hright : EntryContact (OtsPrefix.atAddress parameter words right) (frontier right.1 right.2.1 right.2.2.1 right.2.2.2) entry) : left = right :=
  OtsPrefix.atAddress_selects_unique parameter words left right (.inr entry.1)
    (entryContact_selects _ _ entry hleft) (entryContact_selects _ _ entry hright)

theorem seen_one (segment : OtsPrefix) (endpoint : Digest) : ¬Seen segment endpoint 1 := by
  simp [Seen]

theorem seen_of (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) :
    Seen segment endpoint (FreeMonoid.of entry) ↔ EntryContact segment endpoint entry := by
  simp [Seen]

theorem seen_mul (segment : OtsPrefix) (endpoint : Digest) (first second : Trace) :
    Seen segment endpoint (first * second) ↔ Seen segment endpoint first ∨ Seen segment endpoint second := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]

noncomputable def contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (trace : Trace) :
    Finset OtsPrefix.ChainAddress :=
  Finset.univ.filter fun address => Seen (OtsPrefix.atAddress parameter words address)
    (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace

theorem mem_contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ contacts parameter words frontier trace ↔ Seen (OtsPrefix.atAddress parameter words address)
      (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace := by simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]

theorem contacts_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    contacts parameter words frontier 1 = ∅ := by
  ext address
  simp only [mem_contacts, seen_one, Finset.notMem_empty]

theorem contacts_mul (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (first second : Trace) :
    contacts parameter words frontier (first * second) = contacts parameter words frontier first ∪ contacts parameter words frontier second := by
  ext address
  simp only [mem_contacts, seen_mul, Finset.mem_union]

attribute [local irreducible] contacts

theorem contacts_of_card_le_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) : (contacts parameter words frontier (FreeMonoid.of entry)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro left hleft right hright
  rw [mem_contacts, seen_of] at hleft hright
  exact entryContact_unique parameter words frontier entry left right hleft hright

theorem contacts_step_card_le (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) :
    (contacts parameter words frontier (trace * hashObservationTrace input answer)).card ≤
      (contacts parameter words frontier trace).card + 1 := by
  cases input with
  | inl input => simp only [hashObservationTrace, mul_one]; omega
  | inr input =>
      rw [hashObservationTrace, contacts_mul]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (contacts_of_card_le_one parameter words frontier (input, answer)) _)

theorem new_contact_of_two (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (before after : Trace) (hbefore : (contacts parameter words frontier before).card ≤ 1)
    (hafter : 2 ≤ (contacts parameter words frontier (before * after)).card) :
    ∃ address, address ∉ contacts parameter words frontier before ∧ address ∈ contacts parameter words frontier after := by
  by_contra h
  push Not at h
  have hsub : contacts parameter words frontier after ⊆ contacts parameter words frontier before := by
    intro address ha
    by_contra hb
    exact h address hb ha
  rw [contacts_mul, Finset.union_eq_left.mpr hsub] at hafter
  omega

end SphincsSecurity.Concrete.OtsContactTrace
