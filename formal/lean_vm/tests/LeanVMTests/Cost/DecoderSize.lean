import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `564497`, of which the guest's place codes are `517271`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
the conservative bound `563327 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 564497
#guard decTopC.costIdx == 1041
#guard 563327 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 564579
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
