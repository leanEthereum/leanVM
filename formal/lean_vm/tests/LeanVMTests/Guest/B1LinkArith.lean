import LeanVM.Guest.B1.Link.Arith.Check
import LeanVM.Guest.B1.VerifySub.PhLinkFacts

/-!
# The link section's arithmetic, pinned

The identities of `LeanVM.Guest.B1.Link.Arith` (the guest's computations between `verify_sub`'s
link callees against `linkTail`'s terms), the link section's core IR computing them, and the two
composed, proved on Lean's three axioms.
-/

open LeanVM.Guest.B1.Link.Arith

example : ClaimIdentity := claimIdentity
example : ProgramIdentity := programIdentity
example : SideIdentity := sideIdentity
example : RowIdentity := rowIdentity
example : TerminalIdentity := terminalIdentity
example : LinkTailEq := linkTailEq
example : LinkSecProgram := linkSecProgram
example : LinkSecRow := linkSecRow
example : LinkSecStatement := linkSecStatement
example : ReadsOfFacts := readsOfFacts
example : TerminalOfFacts := terminalOfFacts
example : LeanVM.Guest.B1.VerifySub.VsLinkFactsOfRun := LeanVM.Guest.B1.VerifySub.vsLinkFactsOfRun

/-- info: 'LeanVM.Guest.B1.Link.Arith.claimIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.claimIdentity

/-- info: 'LeanVM.Guest.B1.Link.Arith.programIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.programIdentity

/-- info: 'LeanVM.Guest.B1.Link.Arith.sideIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.sideIdentity

/-- info: 'LeanVM.Guest.B1.Link.Arith.rowIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.rowIdentity

/-- info: 'LeanVM.Guest.B1.Link.Arith.terminalIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.terminalIdentity

/-- info: 'LeanVM.Guest.B1.Link.Arith.linkTailEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.linkTailEq

/-- info: 'LeanVM.Guest.B1.Link.Arith.tablesL_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.tablesL_eq

/-- info: 'LeanVM.Guest.B1.Link.Arith.eval_eq_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.eval_eq_of_norm

/-- info: 'LeanVM.Guest.B1.Link.Arith.linkSecProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.linkSecProgram

/-- info: 'LeanVM.Guest.B1.Link.Arith.linkSecRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.linkSecRow

/-- info: 'LeanVM.Guest.B1.Link.Arith.linkSecStatement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.linkSecStatement

/-- info: 'LeanVM.Guest.B1.Link.Arith.readsOfFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.readsOfFacts

/-- info: 'LeanVM.Guest.B1.Link.Arith.terminalOfFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Link.Arith.terminalOfFacts

/-- info: 'LeanVM.Guest.B1.VerifySub.vsLinkFactsOfRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.vsLinkFactsOfRun

