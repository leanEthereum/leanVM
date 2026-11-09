import LeanXmss.Statement
import XmssSecurity.Proof.OwnBridge
import XmssSecurity.Rpm
import Common.WithHash

/-! # The end theorem of leanXMSS

`XmssSecurity.leanXmss_rpm_security` (`XmssSecurity/Rpm.lean`) proves
`LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable` (`Statement/LeanXmss.lean`): in the
random-permutation model, an adversary that itself makes at most `q` calls of `π` and `π⁻¹` and at
most `lifetime = 2^32` signing requests forges with probability at most `(q + 2^10) · 2^-127`; key
generation, the signer's hashing (its randomizer grinding included) and the forgery's verification
are not charged to `q`. Its proof passes through the random-oracle model at the adversary's own
count (`leanXmss_rom_adversary_bound`, a step). -/

example : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable :=
    XmssSecurity.leanXmss_rpm_security

namespace XmssSecurity

/-- leanXMSS at the adversary's own hash calls, in the random-oracle model: an adversary making at most
`q` hash calls of its own on every path (the signing oracle's, key generation's and the final
verification's not counted) and at most `lifetime` signing requests forges with probability at
most `(q + (2^10 - 1)) / 2^127`. The proof gives `530` in place of `2^10 - 1`: half of
`2 · 384 + 290 + 2`, the verification's calls in each lane, lane 1's forgery probes and the two seed
guesses. -/
theorem leanXmss_rom_adversary_bound (q : Nat) (adversary : LeanXmss.Security.Adversary)
    (hadv : LeanXmss.Security.AdversaryHashQueryBound adversary q)
    (hsign : LeanXmss.Security.SigningRequestBound adversary LeanXmss.lifetime) :
    LeanXmss.Security.forgeAdvantage adversary ≤
      ((q : ENNReal) + Bridge.romAdversarySlack) / ((2 ^ 127 : Nat) : ENNReal) :=
  Bridge.leanXmss_security q adversary hadv hsign

example : Bridge.romAdversarySlack + 1 = LeanXmss.RandomPermutationModel.securitySlack := rfl

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'XmssSecurity.leanXmss_rom_adversary_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_rom_adversary_bound

/-- info: 'XmssSecurity.leanXmss_rpm_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms leanXmss_rpm_security

end XmssSecurity
