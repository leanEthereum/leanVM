module

public import FORS.Lifetimes

@[expose] public section

/-!
# leanSPHINCS: the security theorem

`h26_layered` is the theorem of this library. Its proof lives in `Lifetimes.lean`, from the
certificates of `Certificates/H26.lean`; here it is a single reference, so a statement below that is
not exactly the one proved does not typecheck.

**What is proved.** `Secure127 P slack` (below) for the scheme with parameters `P`: in the SUF-CMA
game (`Statement.lean`), the secret key is a uniform 32-byte `SK.seed`, from which key generation
derives `PK.seed`, `SK.prf` and every secret, and the adversary gets the public key, the hash (a
random oracle) and a signing oracle that it may ask for at most `N` signatures (the signature limit of
`P`); it wins if it outputs a message and a signature that verify, other than a pair the signing
oracle answered. If the adversary itself makes at most `q` hash queries on every path
(`AdvCount.AdvHash`: key generation's, the signer's and the final verification's are not charged), it
wins with probability at most `(q + slack) / 2^127`; for the deployed parameters `slack = 265072`, key
generation's 264193 hash calls and verification's 879.

**The parameters** (`Scheme.lean`): `.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10)
(N := 1_182_000_000)`, an index of 26 bits, a hypertree of three layers, the two lower ones of height 8
and the top one of height 10, and FORS of 24 trees of height 10, up to 1,182,000,000 signatures.

**The hash** is not a parameter: the random oracle stands for Keccak-256. Its size and verification
cost are in `Configurations.lean`.
-/

namespace FORS

open Security ENNReal

/-- **The claim**, for the scheme with parameters `P`: every adversary that itself makes at most `q`
hash queries on every path forges with probability at most `(q + slack) / 2^127`. -/
def Secure127 (P : Params) (slack : ℕ) : Prop :=
  letI := P
  ∀ (adversary : Adversary) (q : ℕ), (∀ pk, (adversary.main pk).IsQueryBoundP AdvCount.AdvHash q) →
    forgeAdvantage adversary ≤ ((q : ℝ≥0∞) + (slack : ℝ≥0∞)) / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-- Layered key, 10 + 8 + 8: 1,182,000,000 signatures, at the adversary's own count. -/
theorem h26_layered :
    Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)) 265072 :=
  fun adversary q hq => Lifetimes.h26_layered_adversary adversary q hq

end FORS
