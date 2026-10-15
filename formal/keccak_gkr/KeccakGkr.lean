import KeccakGkr.GF192

/-! The build fails if the axiom footprint of the three theorems ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'KeccakGkr.keccak_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KeccakGkr.keccak_sound

/-- info: 'KeccakGkr.keccak_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KeccakGkr.keccak_complete

/-- info: 'KeccakGkr.keccak_sound_GF192' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KeccakGkr.keccak_sound_GF192
