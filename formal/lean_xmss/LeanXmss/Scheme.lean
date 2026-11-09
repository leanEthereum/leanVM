module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import Statement.LeanXmss
public import LeanXmss.Compat
public import Common.WithHash

/-!
# leanXMSS

The scheme of `crates/signatures/src/lean_xmss`, specified in `doc/lean_xmss`: two layers of XMSS of height 16 over
WOTS+C one-time keys. Key `b` of the top tree signs the root of bottom tree `b`; a leaf index
`idx < 2^32` signs with bottom key `idx`, in bottom tree `idx / 2^16`.

* WOTS+C: 58 chains of 4 positions. A 16-byte digest is read as 64 base-4 digits, little endian; it
  is a codeword when the last 6 digits are zero and the other 58 sum to 106.
* Every hash input is `P || A || payload`: the 16-byte public parameter, the 16-byte address
  `lo (4 bytes) || hi (3 bytes) || (type + 32 step) || 0^8`, then the payload. The top layer sets
  bit 23 of `hi`. A chain step's address carries the step but not the chain, whose index follows the
  value in the payload.
* `H` is the leanVM hash, Keccak-256, modeled as a random oracle on the bytes
  of its input.
* The secret key is a 32-byte seed `S_0`. Every secret derives from `S = H("leanXMSS" || S_0)`, all
  32 bytes, and the signer keeps `S`.
* Signing a message `M` with key `e` of layer `l`: `R0 = Th(P, A_rnd(l, e), S || M)`, then the least
  `c < 2^32` such that `Th(P, A_msg(l, e), M || (R0 + c))` is a codeword.
-/

open OracleComp OracleSpec ENNReal

namespace LeanXmss

open HashSig

@[expose] public section

/-! ## The instance: parameters, types, and hash-input layout -/

/-- The digits of a digest, 128 bits of base `2^w`. -/
def numDigits : Nat := 64

/-! ### The codeword -/

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

/-! ## The chains and trees, in their own recursion

`Statement/LeanXmss.lean` writes the chains, the path fold and the tree as instances of
`walkChain`, `foldPath` and `buildTree`; their equations here are the proofs' unfolding of each,
step by step. -/

namespace Verification

open HashSig.OverPermutation

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
  (lay : Layer) (key : KeyIndex)

theorem chainWalk_eq_zero (chainIdx : ChainIndex) (start : Nat) (value : Digest) :
    chainWalkWithHash (m := m) parameter lay key chainIdx start 0 value = pure value := rfl

theorem chainWalk_eq_succ (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    chainWalkWithHash (m := m) parameter lay key chainIdx start (steps + 1) value = (do
      let previous ← chainWalkWithHash parameter lay key chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHashWithHash parameter (.chain lay key ⟨start + steps, hstep⟩)
          (chainPayload chainIdx previous)
      else
        pure 0) := rfl

theorem treeFold_eq_zero (path : Fin layerHeight → Digest) (value : Digest) :
    treeFoldWithHash (m := m) parameter lay key path 0 value = pure value := rfl

theorem treeFold_eq_succ (path : Fin layerHeight → Digest) (levels : Nat) (value : Digest) :
    treeFoldWithHash (m := m) parameter lay key path (levels + 1) value = (do
      let current ← treeFoldWithHash parameter lay key path levels value
      let sibling := if hlevel : levels < layerHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := key.val / 2 ^ (levels + 1)
      if key.val.testBit levels then
        tweakableHashWithHash parameter (.node lay (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHashWithHash parameter (.node lay (levels + 1) nodeIdx) (nodePayload current sibling)) := by
  show _ >>= _ = _ >>= _
  congr 1
  funext current
  split <;> rfl

end Verification

namespace KeyGenerationAndSigning

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
  (lay : Layer) (seed : MasterSeed)

theorem treeNode_eq_zero (nodeIdx : Nat) :
    treeNodeWithHash (m := m) parameter lay seed 0 nodeIdx = (do
      let key : KeyIndex := ⟨nodeIdx % lifetime, Nat.mod_lt _ (by decide)⟩
      let endpoints ← oneTimePublicKeyWithHash parameter lay key seed
      Verification.leafHashWithHash parameter lay key endpoints) := rfl

theorem treeNode_eq_succ (level nodeIdx : Nat) :
    treeNodeWithHash (m := m) parameter lay seed (level + 1) nodeIdx = (do
      let left ← treeNodeWithHash parameter lay seed level (2 * nodeIdx)
      let right ← treeNodeWithHash parameter lay seed level (2 * nodeIdx + 1)
      Verification.tweakableHashWithHash parameter (.node lay (level + 1) nodeIdx)
        (OverPermutation.nodePayload left right)) := rfl

end KeyGenerationAndSigning

end

end LeanXmss
