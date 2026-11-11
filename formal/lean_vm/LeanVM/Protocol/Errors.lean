/-
  LeanVM.Protocol.Errors

  The exact errors of leanVM's knowledge soundness and completeness, which the proofs establish
  and the end statements (`Statement/LeanVm.lean`) bound in bits.
-/

module

public import Mathlib.Basic.ENNReal.Inv

/-!
# The errors the proofs establish

With Keccak-256 and Keccak-f[1600] two independent random functions, the proofs bound knowledge
soundness by `soundnessError Q` and completeness by `completenessError fuel`; building both
functions from one random permutation costs `rpmError q` more, `q` the experiment's permutation
calls (at most `verifierPermCalls` for the verifier, `completenessPermCalls fuel` for the honest
prover and the verifier). The end statements bound the sums in bits:
`LeanVM.Rpm.soundnessRpm_le_bits`, `LeanVM.Rpm.completenessRpm_le`.
-/

namespace LeanVM

open scoped ENNReal

@[expose] public section

/-- The verifier's oracle queries, at most, on every statement and proof: `12674` queries to
Keccak-256 and Keccak-f together (the IV, the seed's
permutation, the sponge's permutations, one per challenge and one per four absorbed scalars, and
every Merkle hash of the openings), the bound the proof establishes over every admissible shape
(`LeanVM.Protocol.Verifier.leanVmQueryBound`). The bound is not tight: it charges every WHIR
opening at the largest commitment height, and bounds the bus depth, the table heights and the
Keccak reduction's point by the window of the announced sizes. -/
def verifierQueries : ℕ := 12674

/-- **The soundness error** at `Q` queries, with Keccak-256 and Keccak-f[1600] two independent
random functions, counting the hash and permutation calls of the adversary (`Q`) and of the
verifier (at most `verifierQueries = V`): one `2^-128` per call, plus, per call,
`5 · (Q + V) / 2^256` for a fresh answer that collides with or predicts a value the answers
already refer to (a digest, or a state's capacity), plus one `2^-256` per call of the verifier, for
a fresh hash answer that is the stack's root the adversary announced without computing it (the
extractor, reading the adversary's evaluations only, would then miss the root's preimage). -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + verifierQueries : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((5 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (verifierQueries : ℝ≥0∞) / 2 ^ 256

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work, with two independent
random functions: each of the `Q` queries of the honest prover and the verifier may complete a
proof of work whose nonces all failed, a nonce failing a proof of work of at most `17` bits with
probability at most `1 - 2^-17`. -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  let Q : ℕ := 12676 + 50689 * (2 ^ 29 + 2 * fuel + 2)
  Q * (1 - (2 : ℝ≥0∞)⁻¹ ^ 17) ^ fuel

/-- The permutation calls of the verifier, at most, on every statement and proof: its
`verifierQueries = 12674` queries, each a permutation or a Keccak-256 hash of at most
`2^37 + 9` bytes (the IV's preimage: the `9`-byte version tag, then the bytecode, `16` words of `8`
bytes per instruction, at most `2^30` instructions), which is at most `⌊(2^37 + 9) / 136⌋ + 1 ≤
2^30` blocks, one permutation each. -/
def verifierPermCalls : ℕ := verifierQueries * 2 ^ 30

/-- The permutation calls of the honest prover and the verifier together, at most: the
`12676 + 50689 · (2^29 + 2·fuel + 2)` queries of `completenessError`, each at most `2^30`
blocks. -/
def completenessPermCalls (fuel : ℕ) : ℕ := (12676 + 50689 * (2 ^ 29 + 2 * fuel + 2)) * 2 ^ 30

/-- The cost of building Keccak-256 and Keccak-f[1600] from one random permutation rather than
taking them independent random functions, for an experiment of `q` permutation calls:
`q² / 2^508` (`Common.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

end

end LeanVM
