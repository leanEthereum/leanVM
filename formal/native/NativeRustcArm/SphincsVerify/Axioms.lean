module

public import NativeRustcArm.Sphincs

/-! # The parse's tail and the end theorem use Lean's three axioms only -/

/--
info: 'NativeRustcArm.SphincsVerifyProof.ParseTail.parseTail_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.SphincsVerifyProof.ParseTail.parseTail_spec

/--
info: 'NativeRustcArm.SphincsVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.SphincsVerifier.verify_correct
