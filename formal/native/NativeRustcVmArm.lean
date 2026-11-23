module

public import NativeRustcVmArm.Top.Assembly

/-!
# The rustc-compiled leanVM verifier on AArch64

`VmVerifier.verify_correct` proves the pinned rustc's `leanvm_verify` (`rustc/vm`), ingested as `NativeRustcVmArm.Vm.code`, against Kraken's AArch64 semantics and the verifier model. Every function contract is discharged by its blocks and proved callees. The theorem retains program placement, input representation, alignment, stack, and memory-separation assumptions, but no unproved callee contracts. The build fails if its axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmArm.VmVerifier.verify_correct_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.VmVerifier.verify_correct_of

/--
info: 'NativeRustcVmArm.VmVerifier.verify_correct_of_specs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.VmVerifier.verify_correct_of_specs

/-- info: 'NativeRustcVmArm.Top.Seed.seed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Top.Seed.seed_spec

/-- info: 'NativeRustcVmArm.Top.Verify.verify_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Top.Verify.verify_spec

/--
info: 'NativeRustcVmArm.Top.Leanvm.leanvmVerify_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Top.Leanvm.leanvmVerify_spec

/--
info: 'NativeRustcVmArm.Top.VerifyExecution.verifyExecution_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Top.VerifyExecution.verifyExecution_spec

/-- info: 'NativeRustcVmArm.VmVerifier.verify_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.VmVerifier.verify_correct
