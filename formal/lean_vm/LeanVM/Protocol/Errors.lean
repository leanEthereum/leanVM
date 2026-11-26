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
soundness by `soundnessErrorAS Q` (`LeanVM.Protocol.LeanVMSoundAS`) and completeness by `completenessError fuel`; building both
functions from one random permutation costs `rpmError q` more, `q` the experiment's permutation
calls (at most `verifierPermCalls` for the verifier, `completenessPermCalls fuel` for the honest
prover and the verifier). The end statements bound the sums in bits:
`LeanVM.soundnessRpmAS_le_statement` (`LeanVM.Protocol.LeanVMSoundAS`), `LeanVM.Rpm.completenessRpm_le`.
-/

namespace LeanVM

open scoped ENNReal

@[expose] public section

/-- The verifier's oracle queries, at most, on every statement and proof: `13708` queries to
Keccak-256 and Keccak-f together (the IV, the seed's
permutation, the sponge's permutations, one per challenge and one per four absorbed scalars, and
every Merkle hash of the openings), the bound the proof establishes over every admissible shape
(`LeanVM.Protocol.Verifier.leanVmQueryBound`). The bound is not tight: it charges every WHIR
opening at the largest commitment height, and bounds the bus depth, the table heights and the
Keccak reduction's point by the window of the announced sizes. -/
def verifierQueries : ℕ := 13708

/-- The oracle queries of the honest prover and the verifier together, at most, at a fuel of `fuel`
nonces per proof of work: the seed's hash and permutation, then per quarter of the program's cost
(`leanVmCost = 54825`) one tree of at most `2^29` hashes or one search of `fuel` nonces at two
queries each (`proverFactor`), and the verifier's `13708`. -/
def completenessQueries (fuel : ℕ) : ℕ := 13710 + 54825 * (2 ^ 29 + 2 * fuel + 2)

/-- **The completeness error** at a fuel of `fuel` nonces per proof of work, with two independent
random functions: each of the `Q` queries of the honest prover and the verifier may complete a
proof of work whose nonces all failed, a nonce failing a proof of work of at most `27` bits (the
widest the honest prover meets, the bus's) with probability at most `1 - 2^-27 (1 - 2^-64)`, the
`1 - 2^-64` the chance that its challenge lies outside `K`, which the Keccak GKR's `s` asks
(`grindSample`). -/
noncomputable def completenessError (fuel : ℕ) : ℝ≥0∞ :=
  completenessQueries fuel * (1 - (2 : ℝ≥0∞)⁻¹ ^ 27 * (1 - (2 : ℝ≥0∞)⁻¹ ^ 64)) ^ fuel

/-- The permutation calls of the verifier, at most, on every statement and proof: its
`verifierQueries = 13708` queries, each a permutation or a Keccak-256 hash of at most
`2^37 + 9` bytes (the IV's preimage: the `9`-byte version tag, then the bytecode, `16` words of `8`
bytes per instruction, at most `2^30` instructions), which is at most `⌊(2^37 + 9) / 136⌋ + 1 ≤
2^30` blocks, one permutation each. -/
def verifierPermCalls : ℕ := verifierQueries * 2 ^ 30

/-- The permutation calls of the honest prover and the verifier together, at most: the
`completenessQueries fuel` queries of `completenessError`, each at most `2^30` blocks. -/
def completenessPermCalls (fuel : ℕ) : ℕ := completenessQueries fuel * 2 ^ 30

/-- The cost of building Keccak-256 and Keccak-f[1600] from one random permutation rather than
taking them independent random functions, for an experiment of `q` permutation calls:
`q² / 2^508` (`Common.keccak256_transfer2`). -/
noncomputable def rpmError (q : ℕ) : ℝ≥0∞ := (q ^ 2 : ℝ≥0∞) / 2 ^ 508

end

end LeanVM
