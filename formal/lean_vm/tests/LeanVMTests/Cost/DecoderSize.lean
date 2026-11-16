import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `573837`, of which the guest's frame cells are `521157`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`572579 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, the exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 573837
#guard decTopC.costIdx == 1055
#guard 572579 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 573837
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
