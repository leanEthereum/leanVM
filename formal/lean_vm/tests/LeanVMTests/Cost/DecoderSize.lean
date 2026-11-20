import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `265979`, of which the guest's packed frame cells are `214111`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`264721 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, the exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 265979
#guard decTopC.costIdx == 1056
#guard 264721 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 265979
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
