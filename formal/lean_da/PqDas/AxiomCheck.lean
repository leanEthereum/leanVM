/-
# Axiom audit

The build fails if the axiom footprint of a main theorem ever grows beyond
Lean's three standard axioms, so no proof escape anywhere in the development
can go unnoticed.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Proof.PositionBinding
import PqDas.Proof.CodeBinding
import PqDas.Proof.CorollaryCodeBinding
import PqDas.Proof.CommittedSoundness.ForkingBound

/-- info: 'PqDas.scheme_positionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.scheme_positionBinding

/-- info: 'PqDas.scheme_codeBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.scheme_codeBinding

/-- info: 'PqDas.CommittedSoundness.niCommittedSoundness_forking_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.CommittedSoundness.niCommittedSoundness_forking_bound

/-- info: 'PqDas.scheme_perfectlyComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.scheme_perfectlyComplete

/-- info: 'PqDas.scheme_codeBinding_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.scheme_codeBinding_concrete

/-- info: 'PqDas.scheme_codeBinding_concrete_posBinding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PqDas.scheme_codeBinding_concrete_posBinding
