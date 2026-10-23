import Sphincs.ForestCoverage
import Sphincs.Bytes
import Sphincs.Search

/-!
The candidate's single message-digest call: its first 234 bits are the digest, so a uniform block
gives the uniform 234-bit digest law.
-/

open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 512

namespace Sphincs.Security
open Concrete

/-- The oracle block induces exactly the uniform 234-bit digest law. -/
theorem evalDist_digestBlock_uniform :
    (truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)) =ᵈ ($ᵗ MessageDigest : ProbComp MessageDigest) :=
  evalDist_hashOutput_extract_uniform (width := messageDigestBits) (by decide)

/-- The exact byte string queried for a message digest. -/
abbrev digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : HashInput :=
  tweakableHashInput parameter .message (messageDigestPayload root message randomness)

end Sphincs.Security
