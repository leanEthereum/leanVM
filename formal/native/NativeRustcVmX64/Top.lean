module

public import NativeRustcVmX64.Top.Correct
public import NativeRustcVmX64.Top.VerifyExecution

/-!
# `verify.rs` and `leanvm_verify` on x86-64

`seed`, `verify` and `leanvm_verify` meet their contracts (`NativeRustcVmX64.Top.Seed.seed_spec`,
`NativeRustcVmX64.Top.Verify.verify_spec`, `NativeRustcVmX64.Top.Leanvm.leanvmVerify_spec`;
statements in `NativeRustcVmX64/Spec/Top.lean`); the end theorem from `leanvm_verify`'s contract
(`NativeRustcVmX64.VmVerifier.verify_correct_of`) and from those of `decode` and
`verify_execution` (`NativeRustcVmX64.VmVerifier.verify_correct_of_specs`); `verify_execution`
meets its contract given its callees' (`NativeRustcVmX64.Top.VerifyExecution.verifyExecution_spec`),
with Lean's three axioms only.
-/

/--
info: 'NativeRustcVmX64.Top.Seed.seed_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Top.Seed.seed_spec

/--
info: 'NativeRustcVmX64.Top.Verify.verify_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Top.Verify.verify_spec

/--
info: 'NativeRustcVmX64.Top.Leanvm.leanvmVerify_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Top.Leanvm.leanvmVerify_spec

/--
info: 'NativeRustcVmX64.VmVerifier.verify_correct_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.VmVerifier.verify_correct_of

/--
info: 'NativeRustcVmX64.VmVerifier.leanvmVerify_spec_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.VmVerifier.leanvmVerify_spec_of

/--
info: 'NativeRustcVmX64.VmVerifier.verify_correct_of_specs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.VmVerifier.verify_correct_of_specs

/--
info: 'NativeRustcVmX64.Top.VerifyExecution.verifyExecution_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NativeRustcVmX64.Top.VerifyExecution.verifyExecution_spec
