module

public import NativeRustcVmArm.KeccakGkr.KeccakPi
public import NativeRustcVmArm.KeccakGkr.LinearTranspose
public import NativeRustcVmArm.KeccakGkr.InstanceWeights
public import NativeRustcVmArm.KeccakGkr.SlotWeights
public import NativeRustcVmArm.KeccakGkr.FirstClaim
public import NativeRustcVmArm.KeccakGkr.KeccakPhase
public import NativeRustcVmArm.KeccakGkr.VerifyLayer
public import NativeRustcVmArm.KeccakGkr.KeccakOpen
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak

/-!
# `keccak_gkr.rs`'s functions on AArch64 (phase 6)

The contracts (`NativeRustcVmArm.Spec.KeccakGkr`) of `keccak_pi`, `linear_transpose`,
`instance_weights` and `slot_weights` met, each given its callees' contracts; their axioms checked
below.
-/

/-- info: 'NativeRustcVmArm.KeccakGkr.KeccakPi.keccakPi_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.KeccakPi.keccakPi_spec

/-- info: 'NativeRustcVmArm.KeccakGkr.LinearTranspose.linearTranspose_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.LinearTranspose.linearTranspose_spec

/-- info: 'NativeRustcVmArm.KeccakGkr.InstanceWeights.instanceWeights_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.InstanceWeights.instanceWeights_spec

/-- info: 'NativeRustcVmArm.KeccakGkr.SlotWeights.slotWeights_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.SlotWeights.slotWeights_spec

/-- info: 'NativeRustcVmArm.KeccakGkr.FirstClaim.firstClaim_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.FirstClaim.firstClaim_spec

/--
info: 'NativeRustcVmArm.KeccakGkr.KeccakPhase.keccakPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.KeccakPhase.keccakPhase_spec

/--
info: 'NativeRustcVmArm.KeccakGkr.VerifyLayer.verifyLayer_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.VerifyLayer.verifyLayer_spec

/--
info: 'NativeRustcVmArm.KeccakGkr.KeccakOpen.keccakOpen_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.KeccakOpen.keccakOpen_spec

/--
info: 'NativeRustcVmArm.KeccakGkr.VerifyKeccak.verifyKeccak_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.KeccakGkr.VerifyKeccak.verifyKeccak_spec
