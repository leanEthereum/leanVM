import LeanVM.Cost.DecoderSpec

/-!
# Tests: the guest decoder program's size

The compiled guest decoder's program (`LeanVM.Cost.compiledGuestWitnessDecoder`,
`Cost/DecoderSpec.lean`): its
exact size, `569980`, of which the guest's frame cells are `517728`, and its top's index;
`Cost/DecoderSize.lean` proves the size at most
`568726 + 2·(decTopC.costIdx - decTopC.costDeps.length)`, the exact size, within
`guestWitnessDecoderSizeBound`, as `LeanVMTests/Cost/Efficient.lean` records the extractor's.
-/

namespace LeanVMTests.Cost.DecoderSize

open LeanVM.Cost LeanVM.Cost.Decoder

#guard compiledGuestWitnessDecoder.size == 569980
#guard decTopC.costIdx == 1062
#guard 568726 + 2 * (decTopC.costIdx - decTopC.costDeps.length) == 569980
#guard compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound

end LeanVMTests.Cost.DecoderSize
