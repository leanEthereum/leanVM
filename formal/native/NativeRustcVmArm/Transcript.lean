module

public import NativeRustcVmArm.Transcript.DuplexInput
public import NativeRustcVmArm.Transcript.Duplex
public import NativeRustcVmArm.Transcript.Absorb
public import NativeRustcVmArm.Transcript.Squeeze
public import NativeRustcVmArm.Transcript.AbsorbNonce
public import NativeRustcVmArm.Transcript.StreamElement
public import NativeRustcVmArm.Transcript.PhaseCount
public import NativeRustcVmArm.Transcript.Phase
public import NativeRustcVmArm.Transcript.NextScalar
public import NativeRustcVmArm.Transcript.ReadScalar
public import NativeRustcVmArm.Transcript.ReadScalars
public import NativeRustcVmArm.Transcript.SampleChallenges
public import NativeRustcVmArm.Transcript.Grind
public import NativeRustcVmArm.Transcript.ReadCommitment

/-!
# `transcript.rs`'s and `input.rs`'s functions on AArch64

The contracts (`NativeRustcVmArm.Spec.Transcript`) of the sponge's (`duplex_input`, `duplex`,
`absorb`, `squeeze`, `absorb_nonce`), the decoded proof's (`stream_element`, `phase_count`, `phase`)
and the transcript's functions (`next_scalar`, `read_scalar`, `read_scalars`, `sample_challenges`,
`grind`, `read_commitment`) met, each given its callees' contracts; their axioms checked below.
-/

/-- info: 'NativeRustcVmArm.Transcript.DuplexInput.duplexInput_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.DuplexInput.duplexInput_spec

/-- info: 'NativeRustcVmArm.Transcript.Duplex.duplex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.Duplex.duplex_spec

/-- info: 'NativeRustcVmArm.Transcript.Absorb.absorb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.Absorb.absorb_spec

/-- info: 'NativeRustcVmArm.Transcript.Squeeze.squeeze_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.Squeeze.squeeze_spec

/-- info: 'NativeRustcVmArm.Transcript.AbsorbNonce.absorbNonce_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.AbsorbNonce.absorbNonce_spec

/-- info: 'NativeRustcVmArm.Transcript.StreamElement.streamElement_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.StreamElement.streamElement_spec

/-- info: 'NativeRustcVmArm.Transcript.PhaseCount.phaseCount_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.PhaseCount.phaseCount_spec

/-- info: 'NativeRustcVmArm.Transcript.Phase.phase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.Phase.phase_spec

/-- info: 'NativeRustcVmArm.Transcript.NextScalar.nextScalar_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.NextScalar.nextScalar_spec

/-- info: 'NativeRustcVmArm.Transcript.ReadScalar.readScalar_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.ReadScalar.readScalar_spec

/-- info: 'NativeRustcVmArm.Transcript.ReadScalars.readScalars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.ReadScalars.readScalars_spec

/-- info: 'NativeRustcVmArm.Transcript.SampleChallenges.sampleChallenges_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.SampleChallenges.sampleChallenges_spec

/-- info: 'NativeRustcVmArm.Transcript.Grind.grind_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.Grind.grind_spec

/-- info: 'NativeRustcVmArm.Transcript.ReadCommitment.readCommitment_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmArm.Transcript.ReadCommitment.readCommitment_spec
