module

public import LeanVM.Cost.DecoderSpec
meta import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `566531`, of which the guest's frame cells are `515352`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
the conservative bound `568151 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

@[expose] public section

#guard compiledGuestWitnessDecoder.size == 566531
#guard decTopC.costIdx == 613
#guard 568151 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 568507
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end
end LeanVMTests.Cost.DecoderSize
