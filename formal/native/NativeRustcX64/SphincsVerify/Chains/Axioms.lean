module

public import NativeRustcX64.SphincsVerify.Chains.Spec

/-! # The chains' region theorem on x86-64 uses Lean's three axioms only -/

/--
info: 'NativeRustcX64.SphincsVerifyProof.Chains.chainsSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcX64.SphincsVerifyProof.Chains.chainsSpec
