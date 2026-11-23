module

public import NativeRustcVmX64.Transcript.DuplexInput
public import NativeRustcVmX64.Transcript.Duplex
public import NativeRustcVmX64.Transcript.Absorb
public import NativeRustcVmX64.Transcript.Squeeze
public import NativeRustcVmX64.Transcript.AbsorbNonce
public import NativeRustcVmX64.Transcript.StreamElement
public import NativeRustcVmX64.Transcript.PhaseCount
public import NativeRustcVmX64.Transcript.Phase
public import NativeRustcVmX64.Transcript.NextScalar
public import NativeRustcVmX64.Transcript.ReadScalar
public import NativeRustcVmX64.Transcript.ReadScalars
public import NativeRustcVmX64.Transcript.SampleChallenges
public import NativeRustcVmX64.Transcript.Grind
public import NativeRustcVmX64.Transcript.ReadCommitment

/-!
# `transcript.rs` and `input.rs` on x86-64

The contracts (`NativeRustcVmX64.Spec.Transcript`) of rustc's sponge, decoded-proof and transcript
functions, met: `Transcript.DuplexInput.duplexInput_spec`, `Transcript.Duplex.duplex_spec`, `Transcript.Absorb.absorb_spec`, `Transcript.Squeeze.squeeze_spec`, `Transcript.AbsorbNonce.absorbNonce_spec`, `Transcript.StreamElement.streamElement_spec`, `Transcript.PhaseCount.phaseCount_spec`, `Transcript.Phase.phase_spec`, `Transcript.NextScalar.nextScalar_spec`, `Transcript.ReadScalar.readScalar_spec`, `Transcript.ReadScalars.readScalars_spec`, `Transcript.SampleChallenges.sampleChallenges_spec`, `Transcript.Grind.grind_spec`, `Transcript.ReadCommitment.readCommitment_spec`. The build fails if an axiom footprint grows beyond Lean's three standard
axioms.
-/

/-- info: 'NativeRustcVmX64.Transcript.DuplexInput.duplexInput_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.DuplexInput.duplexInput_spec

/-- info: 'NativeRustcVmX64.Transcript.Duplex.duplex_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.Duplex.duplex_spec

/-- info: 'NativeRustcVmX64.Transcript.Absorb.absorb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.Absorb.absorb_spec

/-- info: 'NativeRustcVmX64.Transcript.Squeeze.squeeze_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.Squeeze.squeeze_spec

/-- info: 'NativeRustcVmX64.Transcript.AbsorbNonce.absorbNonce_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.AbsorbNonce.absorbNonce_spec

/-- info: 'NativeRustcVmX64.Transcript.StreamElement.streamElement_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.StreamElement.streamElement_spec

/-- info: 'NativeRustcVmX64.Transcript.PhaseCount.phaseCount_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.PhaseCount.phaseCount_spec

/-- info: 'NativeRustcVmX64.Transcript.Phase.phase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.Phase.phase_spec

/-- info: 'NativeRustcVmX64.Transcript.NextScalar.nextScalar_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.NextScalar.nextScalar_spec

/-- info: 'NativeRustcVmX64.Transcript.ReadScalar.readScalar_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.ReadScalar.readScalar_spec

/-- info: 'NativeRustcVmX64.Transcript.ReadScalars.readScalars_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.ReadScalars.readScalars_spec

/-- info: 'NativeRustcVmX64.Transcript.SampleChallenges.sampleChallenges_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.SampleChallenges.sampleChallenges_spec

/-- info: 'NativeRustcVmX64.Transcript.Grind.grind_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.Grind.grind_spec

/-- info: 'NativeRustcVmX64.Transcript.ReadCommitment.readCommitment_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Transcript.ReadCommitment.readCommitment_spec
