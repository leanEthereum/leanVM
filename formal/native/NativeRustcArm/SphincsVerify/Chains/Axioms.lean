module

public import NativeRustcArm.SphincsVerify.Chains.Spec

/-! # The chains' region theorem uses Lean's three axioms only -/

/--
info: 'NativeRustcArm.SphincsVerifyProof.Chains.chainsSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcArm.SphincsVerifyProof.Chains.chainsSpec
