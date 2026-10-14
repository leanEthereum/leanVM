import Whir.PCSBCSMerkleRootCache
import Whir.PCSBCSSourceRootReferences
import Whir.PCSRoundByRoundSourceDecoderCorrectness

/-! The executable straight-line word extractor reads one frozen public prefix.
It hashes no invented oracle reply, rewinds no prover, and authenticates no
unavailable default. Failure probability requires the source restoration and
Merkle target-hit composition; output correctness does not assume those bounds. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicRootExtractor
open Concrete Protocol CausalGame
open PCSBCSMerkleRootCache PCSBCSSourceRootReferences

/-- Full image hashing and compact suffix extraction are performed by the
production-shaped cache constructor before the lane-wise Gao decoder. -/
def extract {m : Nat} (p : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (queryPrefix : PublicMerkleLog.PublicLog) (saved : AnchoredHeaderCodec.Record) :=
  let frozen := freeze queryPrefix saved.root (initialShape saved.shape)
  PCSRoundByRoundSource.run p lanes family points anchorPoint anchorValue frozen.raw

/-- One actual returned word explains ALL original ordinary/strided/anchor
claims, not only their randomized batched linear combination. -/
theorem output_explains {m : Nat} (p : ParameterBounds.Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (queryPrefix : PublicMerkleLog.PublicLog) (saved : AnchoredHeaderCodec.Record)
    (w : CausalGame.Witness (ParameterBounds.config p) lanes)
    (returned : extract p lanes family points anchorPoint anchorValue queryPrefix saved = some w) :
    PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) lanes
      (freeze queryPrefix saved.root (initialShape saved.shape)).raw
      family points anchorPoint anchorValue w :=
  PCSRoundByRoundSource.run_output_explains p lanes family points anchorPoint anchorValue
    (freeze queryPrefix saved.root (initialShape saved.shape)).raw w returned

#print axioms output_explains
end Whir.PCSBCSPublicRootExtractor
