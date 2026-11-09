module

public import LeanVM.Cost.FastLib
public import LeanVM.Cost.Extractor.Runner
public import LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Fast.AfterRoot
import all LeanVM.Protocol.Extraction.Extractor
import all Statement.LeanVmVerifier

/-!
# The verifier's replay up to the stack's root, compiled

`afterRootLite bytecode π` (`Fast/AfterRoot.lean`): the announced sizes read and absorbed
(`readSizesLite`, `readPure`), the layout's fields the extractor reads (`buildLayoutLite`:
`placementsOf`, `columnKappas`, `stackOffsets`), and the stack's root read and absorbed at the shape
of the ladder's first level (`commitStackPure`, `commitPure`). Every permutation is answered by
`default` (`absorbPure`): no Keccak-f is computed.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Semantics LeanVM.Cost.FastLib

public section

/-! The functions the bounds name (`Bounds/Replay.lean`), compiled under names of their own, so
that their names do not depend on the program's indices. -/

cost_compile absorbPureC := absorbPure

cost_compile readPureC := readPure

cost_compile initialStateC := initialState

cost_compile digestOfScalarsC := LeanVM.Protocol.KeccakHash.digestFromHalves

cost_compile commitPureC := commitPure

cost_compile bitLengthC := bitLength

cost_compile log2StrictC := log2Strict

cost_compile tableLogFloorsC := tableLogFloors

cost_compile keccakSlotC := keccakSlot

cost_compile stackOffsetsC := stackOffsets

cost_compile placementsOfC := placementsOf

cost_compile queryTableC := LeanVM.Parameters.Whir.queryTable

cost_compile levelsFromC := LeanVM.Parameters.Whir.levelsFrom

cost_compile shapeC := LeanVM.Parameters.Whir.ladderShape

cost_compile ladderC := LeanVM.Parameters.Whir.ladder

/-! The replay. -/

cost_compile buildLayoutLiteC := buildLayoutLite

cost_compile readSizesLiteC := readSizesLite

cost_compile commitStackPureC := commitStackPure

cost_compile afterRootLiteC := afterRootLite

end

end LeanVM.Cost.Extractor
