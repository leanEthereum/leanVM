module

public import NativeRustcVmX64.Layout.PushClaim
public import NativeRustcVmX64.Layout.Ladder
public import NativeRustcVmX64.Layout.CommitStack
public import NativeRustcVmX64.Layout.ReadOod

/-!
# Phase 2 and the claims on x86-64: `push_claim`, `ladder`, `commit_stack`, `read_ood`

The contracts of `stack.rs`'s `push_claim`, `commit_stack` and `read_ood` and `whir.rs`'s `ladder`
(`NativeRustcVmX64.Spec.Layout`), proved. The build fails if an axiom footprint grows beyond
Lean's three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Layout.PushClaim.pushClaim_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.PushClaim.pushClaim_spec

/-- info: 'NativeRustcVmX64.Layout.Ladder.ladder_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.Ladder.ladder_spec

/-- info: 'NativeRustcVmX64.Layout.CommitStack.commitStack_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.CommitStack.commitStack_spec

/-- info: 'NativeRustcVmX64.Layout.ReadOod.readOod_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Layout.ReadOod.readOod_spec
