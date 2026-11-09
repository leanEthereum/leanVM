module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.DecoderSpec

/-!
# The decoder program's inclusions the budget's proof uses

`includes` on the decoder's top's list of bodies (a membership proof per body) takes about a second
each: each inclusion the budget's proof (`Budget.lean`) uses is a lemma of its own, here, as the
extractor's (`Bounds/TopIncludes.lean`).
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Decoder

public section

theorem includes_budget_readerClosure : Includes compiledGuestWitnessDecoder Decoder.decTopTablesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_discreteLogWith : Includes compiledGuestWitnessDecoder Decoder.discreteLogWithC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_powBelow : Includes compiledGuestWitnessDecoder powBelowC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTestLam : Includes compiledGuestWitnessDecoder Decoder.decTopStatesC.lam1.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTestAt : Includes compiledGuestWitnessDecoder preTestAtC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_entryArrayT : Includes compiledGuestWitnessDecoder
    entryArrayTC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_getPc : Includes compiledGuestWitnessDecoder getPcC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_frameAtA : Includes compiledGuestWitnessDecoder
    Decoder.frameAtAC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_frameFpA : Includes compiledGuestWitnessDecoder
    Decoder.frameFpAC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_mainValLam : Includes compiledGuestWitnessDecoder Decoder.decTopStatesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_mainVal : Includes compiledGuestWitnessDecoder
    Decoder.mainValC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_decWitN : Includes compiledGuestWitnessDecoder
    Decoder.decWitNC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_frameLam : Includes compiledGuestWitnessDecoder
    Decoder.decTopFramesC.lam0.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_xmssLam : Includes compiledGuestWitnessDecoder Decoder.decTopFramesC.lam1.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_sphincsLam : Includes compiledGuestWitnessDecoder Decoder.decTopFramesC.lam2.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_cursorLam : Includes compiledGuestWitnessDecoder Decoder.decTopFramesC.lam3.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_gLogD : Includes compiledGuestWitnessDecoder Decoder.gLogDC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_cursorLength : Includes compiledGuestWitnessDecoder
    cursorLengthC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_preTable : Includes compiledGuestWitnessDecoder
    Decoder.preTableC.costDeps := by
  have := decoderProgram_includes
  includes

theorem includes_budget_pcTableT : Includes compiledGuestWitnessDecoder
    Decoder.pcTableTC.costDeps := by
  have := decoderProgram_includes
  includes

end

end LeanVM.Cost.Bounds.Guest
