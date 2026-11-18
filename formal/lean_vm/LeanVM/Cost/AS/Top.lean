module

public import LeanVM.Cost.AS.Replay
import all LeanVM.Protocol.EndToEnd.Sound.SkelPairs
import all LeanVM.Protocol.Extraction.AS.TopC
import all LeanVM.Protocol.Extraction.AS.TopA
import all LeanVM.Protocol.Extraction.AS.Top
import all LeanVM.Protocol.Verifier.Phases
import all LeanVM.Protocol.Extraction.AS.Lite
public import LeanVM.Protocol.Extraction.AS.Lite

/-!
# The agreement-set extractor, compiled

`extractL` (`Protocol/Extraction/AS/Lite.lean`), compiled on top of the descent's and the replay's
functions (`Cost/AS/Descent.lean`, `Cost/AS/Replay.lean`): the decoders of the announced sizes and
of the opening's trace on the lite layout, the body's skeleton, every root's word (its leaves
inverted through the transcript's compiled index, `leavesOf`), the finish, and the top
(`extractLC`). The chain starts after the shared one (`Cost/Extractor/Top.lean`), whose compiled
functions it reuses.
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Extraction.AS LeanVM.Protocol.EndToEnd.Sound LeanVM.Extraction.Fast LeanVM.Protocol.Verifier
open Common LeanVM.Protocol.Whir.Sound

public section

cost_compile decSizesLC := decSizesL

cost_compile skBodyLC := skBodyL

cost_compile decBodyLC := decBodyL

cost_compile laneRowC := laneRow

cost_compile laneRowsC := laneRows

cost_compile leavesAtC := leavesAt

cost_compile wordArrOfC := wordArrOf

cost_compile finishLC := finishL

cost_compile extractLC := extractL

end

end LeanVM.Cost.AS
