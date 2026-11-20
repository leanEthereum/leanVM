module

public import LeanVM.Cost.AS.Top
public import LeanVM.Cost.ExtractorProgram

/-!
# The agreement-set extractor's program

`compiledASExtractor`: function `0` is the entry `entryBody j` (`Cost/ExtractorProgram.lean`) with
`j = extractLC.costIdx`, the compiled agreement-set extractor (`Cost/AS/Top.lean`), the other
functions the bodies its spec needs (`extractLC.costDeps`).
-/

namespace LeanVM.Cost.AS

open LeanVM.Cost

public section

/-- The program's bodies: the entry at `0`, then the compiled extractor's. -/
@[expose] def asProgramBodies : List (ℕ × Term) :=
  (0, entryBody extractLC.costIdx) :: extractLC.costDeps

/-- **The agreement-set extractor's program.** -/
@[expose] def compiledASExtractor : MachineProgram := MachineProgram.ofList asProgramBodies

end

end LeanVM.Cost.AS
