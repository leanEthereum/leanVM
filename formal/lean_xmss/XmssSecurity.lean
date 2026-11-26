import XmssSecurity.Rpm

/-! # The end theorem of leanXMSS

`XmssSecurity.leanXmss_rpm_security` (`XmssSecurity/Rpm.lean`) proves
`LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable` (`Statement/LeanXmss.lean`): in the
random-permutation model, an adversary that itself makes at most `q` calls of `π` and `π⁻¹` and at
most `2^32` signing requests forges with probability at most `(q + 2^10) · 2^-127`; key
generation, the signer's hashing (its randomizer grinding included) and the forgery's verification
are not charged to `q`. The statement's leanXMSS is EthLib's, and the proof is EthLib's theorem,
carried to leanVM's oracles. -/

example : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable :=
    XmssSecurity.leanXmss_rpm_security

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a
`sorry` or `native_decide` anywhere in the proof, EthLib's included, cannot go unnoticed. -/

/--
info: 'XmssSecurity.leanXmss_rpm_security' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms XmssSecurity.leanXmss_rpm_security

/--
info: 'XmssSecurity.verifyWithKeccak_of_signWith' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms XmssSecurity.verifyWithKeccak_of_signWith
