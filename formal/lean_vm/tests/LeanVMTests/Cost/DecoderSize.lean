import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `561803`, of which the guest's place codes are `515439`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`561449 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, its exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 561803
#guard decTopC.costIdx == 592
#guard 561449 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 561803
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
