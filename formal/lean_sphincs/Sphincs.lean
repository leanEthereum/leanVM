import Sphincs.Axioms

/-! # The end theorem of leanSPHINCS

`Sphincs.leanSphincsStronglyUnforgeable` proves `Sphincs.LeanSphincsStronglyUnforgeable`
(`Statement/LeanSphincs.lean`): in the random-permutation model, an adversary that itself makes at
most `q` calls of `π` and `π⁻¹` and at most `1,182,000,000` signing requests forges with probability
at most `(q + 2^19) · 2^-127`; the honest parties' hashing is not charged to `q`. Its proof passes
through the random-oracle model at the adversary's own count (upstream's
`FORS.Lifetimes.h26_layered_adversary`, a step) and upstream's model of the scheme (`FORS.Scheme`,
leanVM main `40f877dc`), then the crate's key generation and signer in the model's hash monad
(`FORS.Crate`, by `Common.SufCma.StaticSwap`), the statement's scheme through the maps of
`Sphincs/Model.lean` (`Sphincs/AdvRpm.lean`).
`Sphincs/Axioms.lean` and `FORS/Axioms.lean` pin the axiom footprints; the build fails if the
end theorem's grows beyond Lean's three. -/

example : Sphincs.LeanSphincsStronglyUnforgeable := Sphincs.leanSphincsStronglyUnforgeable

/-- info: 'Sphincs.leanSphincsStronglyUnforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Sphincs.leanSphincsStronglyUnforgeable
