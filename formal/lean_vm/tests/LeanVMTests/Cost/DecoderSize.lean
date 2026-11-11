import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `623824`, of which the guest's frame cells are `581382`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`622570 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, the exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 623824
#guard decTopC.costIdx == 1058
#guard 622570 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 623824
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
