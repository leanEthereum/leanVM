module

public import LeanVM.Cost.Extractor.Top
import all Statement.LeanVmVerifier
import all Statement.Verifier.Layout
import all Statement.Verifier.Multilinear
import all Statement.Verifier.Transcript
import all Statement.Field

/-!
# The layout's and the opening's sizes, compiled

The functions the bounds name (`Bounds/Replay.lean`), compiled under names of their own, so that
their names do not depend on the program's indices: the bit length, the strict logarithm, the
tables' floors, the stack's offsets, and the WHIR ladder.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

public section

cost_compile digestOfScalarsC := LeanVM.Protocol.KeccakHash.digestFromHalves

cost_compile bitLengthC := bitLength

cost_compile log2StrictC := log2Strict

cost_compile tableLogFloorsC := tableLogFloors

cost_compile stackOffsetsC := stackOffsets

cost_compile queryTableC := LeanVM.Parameters.Whir.queryTable

cost_compile levelsFromC := LeanVM.Parameters.Whir.levelsFrom

cost_compile shapeC := LeanVM.Parameters.Whir.ladderShape

cost_compile ladderC := LeanVM.Parameters.Whir.ladder

end

end LeanVM.Cost.Extractor
