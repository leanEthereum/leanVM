module

public import LeanVM.Cost.DecoderSpec
meta import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its top's index, and its size exactly the bound `Cost/DecoderSize.lean`
proves, `guestLanesRowSize + 2 + otherBodiesSize + (decTopC.costIdx - decTopC.costDeps.length)`
(the guest's packed frame cells, their array and literal, the other bodies, one per index without
a body), within `guestWitnessDecoderSizeBound`.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

@[expose] public section

#guard decTopC.costIdx == 903
#guard compiledGuestWitnessDecoder.size == 257768
#guard compiledGuestWitnessDecoder.size ==
  guestLanesRowSize + 2 + otherBodiesSize + (decTopC.costIdx - decTopC.costDeps.length)
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end
end LeanVMTests.Cost.DecoderSize
