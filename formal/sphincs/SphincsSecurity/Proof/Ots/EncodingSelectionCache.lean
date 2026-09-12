import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingCharge
import SphincsSecurity.Proof.Ots.EncodingProbability
/-!
# Cache-derived encoding selection risk

The abstract conditional-selection schedule is instantiated with the concrete encoding inputs at
one structural position and one settled layer message. Every cached candidate retains its full hash
input as the identifier used to exclude the selected input itself.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 100000

def encodingRetryInput (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Nat) : HashInput :=
  tweakableHashInput parameter position.domain
    (digestBytes message ++ counterBytes (BitVec.ofNat counterBits counter))

theorem encodingRetryInput_injective_of_lt
    {parameter : PublicParameter} {position : EncodingPosition} {message : Digest}
    {left right : Nat} (hleft : left < encodingAttemptLimit)
    (hright : right < encodingAttemptLimit)
    (heq : encodingRetryInput parameter position message left =
      encodingRetryInput parameter position message right) :
    left = right := by
  have hpayload :=
    (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).2
  obtain ⟨_, hcounter⟩ :=
    List.append_inj hpayload (by simp [digestBytes_length])
  apply ofNat_inj_of_lt (w := counterBits)
    (by simpa [encodingAttemptLimit, counterBits] using hleft)
    (by simpa [encodingAttemptLimit, counterBits] using hright)
  exact bytesLE_injective hcounter
