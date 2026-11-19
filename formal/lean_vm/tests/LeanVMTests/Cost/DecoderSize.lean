import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `562048`, of which the guest's place codes are `515691`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`561694 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, its exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 562048
#guard decTopC.costIdx == 592
#guard 561694 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 562048
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
