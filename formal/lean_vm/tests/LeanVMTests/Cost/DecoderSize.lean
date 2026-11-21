import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its top's index, and its size exactly the bound `Cost/DecoderSize.lean`
proves, `guestLanesRowSize + 2 + otherBodiesSize + 2·(decTopC.costIdx - decTopC.costDeps.length)`
(the guest's packed frame cells, their array and literal, the other bodies, two per index without
a body), within `guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the
extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard decTopC.costIdx == 607
#guard compiledGuestWitnessDecoder.size ==
  guestLanesRowSize + 2 + otherBodiesSize + 2 * (decTopC.costIdx - decTopC.costDeps.length)
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
