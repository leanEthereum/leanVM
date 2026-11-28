module

public import NativeRustcVmArm.Layout.PushClaim
public import NativeRustcVmArm.Layout.Ladder
public import NativeRustcVmArm.Layout.CommitStack
public import NativeRustcVmArm.Layout.ReadOod

/-!
# Phase 2 and the claims on AArch64: `push_claim`, `ladder`, `commit_stack`, `read_ood`

The contracts of `stack.rs`'s `push_claim`, `commit_stack` and `read_ood` and `whir.rs`'s `ladder`,
proved. The build fails if an axiom footprint grows beyond Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmArm.Layout.PushClaim.pushClaim_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.PushClaim.pushClaim_spec

/-- info: 'NativeRustcVmArm.Layout.Ladder.ladder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.Ladder.ladder_spec

/-- info: 'NativeRustcVmArm.Layout.CommitStack.commitStack_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.CommitStack.commitStack_spec

/-- info: 'NativeRustcVmArm.Layout.ReadOod.readOod_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Layout.ReadOod.readOod_spec
