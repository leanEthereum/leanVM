module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.DecoderSpec

/-!
# The decoder program's inclusions the budget's proof uses

`includes` on the decoder's top's list of bodies (a membership proof per body) takes about a second
each: each inclusion the budget's proof (`Budget.lean`) uses is a lemma of its own, here.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Decoder

public section

/-- `budget_includes n d`: the theorem `n : Includes compiledGuestWitnessDecoder d`, by `includes`
from `decoderProgram_includes`. -/
local macro "budget_includes " n:ident d:term : command =>
  `(theorem $n : Includes compiledGuestWitnessDecoder $d := by
      have := decoderProgram_includes
      includes)

budget_includes includes_budget_readerClosure Decoder.decTopTablesC.lam0.costDeps
budget_includes includes_budget_discreteLogWith Decoder.discreteLogWithC.costDeps
budget_includes includes_budget_powBelow powBelowC.costDeps
budget_includes includes_budget_preTestLam Decoder.decTopStatesC.lam1.costDeps
budget_includes includes_budget_preTestAt preTestAtC.costDeps
budget_includes includes_budget_entryArrayT entryArrayTC.costDeps
budget_includes includes_budget_getPc getPcC.costDeps
budget_includes includes_budget_frameAtA Decoder.frameAtAC.costDeps
budget_includes includes_budget_frameFpA Decoder.frameFpAC.costDeps
budget_includes includes_budget_mainValLam Decoder.decTopStatesC.lam0.costDeps
budget_includes includes_budget_mainVal Decoder.mainValC.costDeps
budget_includes includes_budget_decWitN Decoder.decWitNC.costDeps
budget_includes includes_budget_frameLam Decoder.decTopFramesC.lam0.costDeps
budget_includes includes_budget_xmssLam Decoder.decTopFramesC.lam1.costDeps
budget_includes includes_budget_sphincsLam Decoder.decTopFramesC.lam2.costDeps
budget_includes includes_budget_cursorLam Decoder.decTopFramesC.lam3.costDeps
budget_includes includes_budget_gLogD Decoder.gLogDC.costDeps
budget_includes includes_budget_cursorLength cursorLengthC.costDeps
budget_includes includes_budget_preTable Decoder.preTableC.costDeps
budget_includes includes_budget_pcTableT Decoder.pcTableTC.costDeps

end

end LeanVM.Cost.Bounds.Guest
