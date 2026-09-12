import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Honest
/-!
# Reading a payload's blocks

The accounting has to charge a query whose answer is what fixes an honest input one level up. What it
charges against is the block of the parent's payload that answer would have to land in, so it needs to
read a block out of an input: `slotDigest_flatMap` says the `k`-th block of a payload built from a
list of values is the `k`-th value. Nothing here is about the scheme, only about the fixed-width
encoding every payload of it uses.
-/

namespace SphincsSecurity

open OracleComp

/-- What follows the tweak and the parameter in a hash input. -/
def payloadOf (input : HashInput) : HashInput := input.drop 32

theorem payloadOf_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : payloadOf (tweakableHashInput parameter domain payload) = payload := by
  have hlength : (tweakBytes domain ++ bytesLE 16 parameter).length = 32 := by
    simp [tweakBytes_length, bytesLE_length]
  simp only [payloadOf, tweakableHashInput]
  rw [← hlength, List.drop_left]

end SphincsSecurity
