import FORS.Lifetimes

/-!
# leanSPHINCS: the security theorem

`h26_layered` is the theorem of this library, for leanSPHINCS as `crates/signatures/src/lean_sphincs`
implements it. Its proof lives in `Lifetimes.lean`, from the certificates of `Certificates/H26.lean`;
here it is a single reference, so a statement below that is not exactly the one proved does not
typecheck.

**What is proved.** `Secure127 P` (below) for the scheme with parameters `P`: in the SUF-CMA game
(`Statement.lean`), the key is generated from a uniform 32-byte seed `S0` through the scheme seed
`S = H(leanSPHINCS || S0)`, and the adversary gets the public key, the hash (a random oracle) and a
signing oracle that it may ask for at most `N` signatures (the signature limit of `P`); it wins if it
outputs a message and a signature that verify, other than a pair the signing oracle answered. If
every run of the game makes at most `q ≥ 1` hash queries in total (the adversary's, and those of key
generation, the hash of `S0` included, signing and verification), it wins with probability at most
`q / 2^127`.

**The parameters** (`Scheme.lean`): `.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10)
(N := 1_182_000_000)`, an index of 26 bits, a hypertree of three layers, the two lower ones of height 8
and the top one of height 10, and FORS of 24 trees of height 10, up to 1,182,000,000 signatures.

**The hash** is not a parameter: the random oracle stands for Keccak-256. Its size and verification
cost are in `Configurations.lean`.
-/

namespace FORS

open Security ENNReal

/-- **The claim**, for the scheme with parameters `P`: every adversary whose runs of the SUF-CMA game
make at most `q ≥ 1` hash queries in total forges with probability at most `q / 2^127`. -/
def Secure127 (P : Params) : Prop :=
  letI := P
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : Adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ 127 : ℕ) : ℝ≥0∞)

/-- Layered key, 10 + 8 + 8: 1,182,000,000 signatures. -/
theorem h26_layered : Secure127 (.layered (h := 26) (d := 3) (ℓ := 8) (k := 24) (a := 10) (N := 1_182_000_000)) :=
  Lifetimes.h26_layered_bits

/-- `Secure127` is the target `SecurityBits P 127` of `Statement.lean`, spelled out. -/
theorem secure127_iff (P : Params) : Secure127 P ↔ SecurityBits P 127 := Iff.rfl

end FORS
