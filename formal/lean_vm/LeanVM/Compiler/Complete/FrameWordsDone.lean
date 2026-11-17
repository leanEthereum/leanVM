/-
  LeanVM.Compiler.Complete.FrameWordsDone

  The frame side's statement, from its proved pieces.
-/

module

public import LeanVM.Compiler.Complete.FrameChain

/-!
# The frame words

`openBody`: the open chain statement at the walk's instance (`openW_of`). With `chainBody_of`,
`faBody` and `aFaBody` it gives `frameWords : FrameWordsStmt`.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **`OpenBody`**: a block of a body entered by an open chain, at the walk's instance. -/
theorem openBody : OpenBody := by
  intro κ₀ W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd
  have hI := instK_ok (kfps := kfps) hW htf hpa hta hrd
  have hok := opOK_K (kfps := kfps) hW htf hpa hsc hta hw hrd
  have hfresh := hta.fresh
  exact openW_of placeMono placeNew_ok hI (fun h => hfp (by simpa [ctxOf] using h)) agOwn_K
    (fun _ => rfl) (fun q hq => hlocB_K hW htf hpa q hq)
    (fun x arms rest hg => ⟨fun a ha => .arm hg ha, .tail hg⟩)
    (faBody W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (fun x arms rest hin ht => (hfresh.2 x ht).1 (inBody_uses hin x (by simp [Stmt.uses])))
    (aFaBody W hW tf htf hsc pf hpa hta hns fp hfp kfps hdr σ es vs hw ha hrd)
    (inBlockOf hok hI)

/-- **The frame words**, from the proved pieces of the frame side. -/
theorem frameWords : FrameWordsStmt :=
  frameWords_of_fa_chain faBody aFaBody (chainBody_of openBody)

end

/-- info: 'LeanVM.Compiler.Complete.frameWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms frameWords

end LeanVM.Compiler.Complete
