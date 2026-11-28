import LeanVM.Guest.EndFinal
import LeanVM.Cost.GuestKnowledge

/-!
# The guest decoder's composition, pinned

The guest's knowledge soundness for the replaying decoder `LeanVM.Guest.End.decode`, from B2 and
`verify_sub`'s statement with its proof named by `vsPiOf` (`guest_knowledge_of`), from B2's
obligations (`guest_knowledge_of_obligations`), and `GuestKnowledgeSoundness` of any program that
computes it within its size bound and budget (`guestKnowledgeSoundness_of_spec`), on Lean's three
axioms.
-/

/-- info: 'LeanVM.Guest.End.guest_knowledge_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge_of

/-- info: 'LeanVM.Guest.End.guest_knowledge_of_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge_of_obligations

/-- info: 'LeanVM.Guest.End.guestKnowledgeSoundness_of_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guestKnowledgeSoundness_of_spec

/-- info: 'LeanVM.Guest.End.decode_binds_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds_of

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_of

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_of_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_of_obligations

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_of_vs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_of_vs
