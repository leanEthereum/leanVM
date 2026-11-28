module

public import NativeRustcVmX64.Sumcheck.OpenPhase
public import NativeRustcVmX64.Sumcheck.QueryOpenings

/-!
# `open_phase` and `TState::query_openings` on x86-64

The contracts (`NativeRustcVmX64.Spec.Sumcheck`) met: `Sumcheck.OpenPhase.openPhase_spec`
(given `keccak256_words`' and `climb`'s), `Sumcheck.QueryOpenings.queryOpenings_spec` (given
`Decoded::phase`'s and `open_phase`'s). The build fails if an axiom footprint grows beyond Lean's
three standard axioms.
-/

/-- info: 'NativeRustcVmX64.Sumcheck.OpenPhase.openPhase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.OpenPhase.openPhase_spec

/-- info: 'NativeRustcVmX64.Sumcheck.QueryOpenings.queryOpenings_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustcVmX64.Sumcheck.QueryOpenings.queryOpenings_spec
