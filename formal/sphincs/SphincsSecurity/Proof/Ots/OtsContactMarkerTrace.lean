import SphincsSecurity.Proof.Ots.EncodingAdaptiveMarker
import SphincsSecurity.Proof.Base.TraceSum
namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
local instance (priority := 11000) : DecidableEq OtsPrefix.ChainAddress := inferInstance
attribute [local instance 10000] Classical.propDecidable
attribute [local irreducible] OtsContactTrace.contacts canonicalEncodingInputs Finset.univ

def ContactBeforeEntry (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (entry : HashInput × HashOutput) : Prop :=
  ∃ address ∈ OtsContactTrace.contacts parameter words frontier history, NewMarker parameter words history address entry

noncomputable def contactMarkerCount (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : OtsContactTrace.Trace) : Nat :=
  TraceSum.run (fun history entry => if ContactBeforeEntry parameter words frontier history entry then 1 else 0) 1 trace.toList

def ContactBeforeMarker (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : OtsContactTrace.Trace) : Prop :=
  ∃ before entry after, trace.toList = before ++ entry :: after ∧
    ContactBeforeEntry parameter words frontier (FreeMonoid.ofList before) entry

theorem contactMarkerCount_pos_iff (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : OtsContactTrace.Trace) :
    0 < contactMarkerCount parameter words frontier trace ↔ ContactBeforeMarker parameter words frontier trace := by
  rw [contactMarkerCount, TraceSum.run_pos_iff]
  have hi : ∀ p : Prop, (0 < (if p then 1 else 0 : Nat)) ↔ p := by
    intro p
    by_cases hp : p <;> simp [hp]
  simp only [one_mul, hi, ContactBeforeMarker]

theorem contactMarkerCount_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    contactMarkerCount parameter words frontier 1 = 0 := rfl

theorem contactMarkerCount_step (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (entry : HashInput × HashOutput) :
    contactMarkerCount parameter words frontier (history * FreeMonoid.of entry) =
      contactMarkerCount parameter words frontier history + if ContactBeforeEntry parameter words frontier history entry then 1 else 0 := by
  simp only [contactMarkerCount, FreeMonoid.toList_mul, FreeMonoid.toList_of, TraceSum.run_append,
    TraceSum.run_cons, TraceSum.run_nil, FreeMonoid.ofList_toList, one_mul, Nat.add_zero]

noncomputable def contactMarkerCharge (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (input : OracleWorld.Domain) : Nat :=
  if QueryClass.EncodingHash parameter input then (OtsContactTrace.contacts parameter words frontier history).card else 0

noncomputable def contactMarkerCost (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history tail : OtsContactTrace.Trace) : Nat :=
  TraceSum.run (fun history entry => contactMarkerCharge parameter words frontier history (.inr entry.1)) history tail.toList

theorem contactMarkerCost_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) : contactMarkerCost parameter words frontier history 1 = 0 := rfl

theorem contactMarkerCost_step (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) (tail : OtsContactTrace.Trace) :
    contactMarkerCost parameter words frontier history (hashObservationTrace input answer * tail) =
      contactMarkerCharge parameter words frontier history input +
        contactMarkerCost parameter words frontier (history * hashObservationTrace input answer) tail := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, one_mul, mul_one, contactMarkerCharge, QueryClass.EncodingHash, if_false, Nat.zero_add]
  | inr input => rfl

theorem contactMarkerCost_le (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history tail : OtsContactTrace.Trace) :
    contactMarkerCost parameter words frontier history tail ≤
      tail.toList.length * (OtsContactTrace.contacts parameter words frontier (history * tail)).card := by
  apply TraceSum.run_le_length_mul
  intro before entry after he
  have ht : tail = FreeMonoid.ofList before * FreeMonoid.ofList (entry :: after) := by
    simpa only [FreeMonoid.ofList_toList, FreeMonoid.ofList_append] using congrArg FreeMonoid.ofList he
  have hsub : OtsContactTrace.contacts parameter words frontier (history * FreeMonoid.ofList before) ⊆
      OtsContactTrace.contacts parameter words frontier (history * tail) := by
    rw [ht, ← mul_assoc, OtsContactTrace.contacts_mul parameter words frontier (history * FreeMonoid.ofList before)]
    exact Finset.subset_union_left
  dsimp only [contactMarkerCharge]
  split
  · exact Finset.card_le_card hsub
  · exact Nat.zero_le _

end SphincsSecurity.Concrete.OtsEncodingMarker
