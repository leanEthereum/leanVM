module

public import NativeRustcVmX64.KeccakGkr.KeccakPi
public import NativeRustcVmX64.KeccakGkr.LinearTranspose
public import NativeRustcVmX64.KeccakGkr.InstanceWeights
public import NativeRustcVmX64.KeccakGkr.SlotWeights
public import NativeRustcVmX64.KeccakGkr.FirstClaim

/-!
# `keccak_gkr.rs`'s functions on x86-64

The contracts (`NativeRustcVmX64.Spec.KeccakGkr`) of `keccak_pi`, `linear_transpose`,
`instance_weights`, `slot_weights` and `first_claim` met, each given its callees' contracts; their
axioms checked below.
-/

/-- info: 'NativeRustcVmX64.KeccakGkr.KeccakPi.keccakPi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.KeccakPi.keccakPi_spec

/-- info: 'NativeRustcVmX64.KeccakGkr.LinearTranspose.linearTranspose_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.LinearTranspose.linearTranspose_spec

/-- info: 'NativeRustcVmX64.KeccakGkr.InstanceWeights.instanceWeights_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.InstanceWeights.instanceWeights_spec

/-- info: 'NativeRustcVmX64.KeccakGkr.SlotWeights.slotWeights_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.SlotWeights.slotWeights_spec

/-- info: 'NativeRustcVmX64.KeccakGkr.FirstClaim.firstClaim_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.KeccakGkr.FirstClaim.firstClaim_spec
