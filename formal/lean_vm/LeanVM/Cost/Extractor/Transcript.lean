module

public import LeanVM.Cost.Extractor.GsRun
public import LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Transcript
import all LeanVM.Protocol.Extraction.Fast.Replay
import all LeanVM.Protocol.Extraction.Fast.Lookup
import all LeanVM.Protocol.Extraction.Fast.SortedMap
import all LeanVM.Protocol.Extraction.Extractor

/-!
# The transcript's index and the committed word, compiled

`transcriptIndex qs L` (`Fast/Transcript.lean`: the replay in sorted maps, the evaluations of at
most `L` bytes, their first answers and the preimage index) and `leafAt` (a position of the
committed word). The extractor's compiled modules form one import chain (indices are allocated
from what a module imports): this module follows the decoder's (`Decode.lean`) and precedes the
runner's.

The sorted maps' operations the bounds name (`Bounds/Transcript.lean`) are compiled first, under
names of their own (`searchPreC`, `carryPreC`, …), so the compiled transcript calls them and the
bounds do not depend on the order of on-demand compilation.
-/

namespace LeanVM.Cost.Extractor

open LeanVM.Cost LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Fast
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Semantics
open LeanVM.Cost.FastLib

public section

attribute [local instance] lexOrd

/-! ### Generic list functions -/

cost_compile compareLexC := @List.compareLex.{0}

cost_compile bytesBeqC := @List.beq UInt8 _

/-! ### The preimage index's map: keys `(digest words, length)` -/

cost_compile searchPreC := @searchIn (List UInt64 × ℕ) Hits _

cost_compile mergeNewerPreC := @mergeNewer (List UInt64 × ℕ) Hits _

cost_compile levelMergePreC := @Level.merge (List UInt64 × ℕ) Hits _ _ _

cost_compile carryPreC := @carry (List UInt64 × ℕ) Hits _ _ _

cost_compile insertPreC := @SortedMap.insert (List UInt64 × ℕ) Hits _ _ _

cost_compile getPreC := @SortedMap.get? (List UInt64 × ℕ) Hits _

cost_compile hitKeyC := hitKey

cost_compile hitsMergeC := Hits.merge

/-! ### The first answers' map: byte-string keys -/

cost_compile searchBytesC := @searchIn Bytes Digest _

cost_compile mergeNewerBytesC := @mergeNewer Bytes Digest _

cost_compile levelMergeBytesC := @Level.merge Bytes Digest _ _ _

cost_compile carryBytesC := @carry Bytes Digest _ _ _

cost_compile insertBytesC := @SortedMap.insert Bytes Digest _ _ _

cost_compile getBytesC := @SortedMap.get? Bytes Digest _

cost_compile insertIfNewC := @insertIfNew Bytes Digest _ _ _

/-! ### The transcript -/

cost_compile replayStepC := ReplayFast.step

cost_compile keccakUnpaddedC := keccakUnpaddedFast

cost_compile keccakEvaluationsC := keccakEvaluationsFast

cost_compile firstAnswersC := firstAnswers

cost_compile preimageIndexC := preimageIndex

cost_compile answerPairsC := @answerPairs

cost_compile transcriptIndexC := transcriptIndex

cost_compile leafAtC := leafAt

end

end LeanVM.Cost.Extractor
