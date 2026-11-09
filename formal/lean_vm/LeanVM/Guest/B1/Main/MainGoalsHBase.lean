/-
  LeanVM.Guest.B1.Main.MainGoalsHBase

  `main`'s honest words by buffer, and the children's claims' shapes: what the goals of the
  children's loop and of `aggregate_claims` share.
-/

module

public import LeanVM.Guest.B1.Main.MainGoals
public import LeanVM.Protocol.Verifier.DeferredShape
public import LeanVM.Guest.AcceptableChild

/-!
# `main`'s honest words, by buffer

`mem_hLmain`: buffer `i` of `main`'s honest words sits at its base; `reads_hLmain`: they read it
there. `kid_shapes`: under `NodeRelation`, every child's two claims on the bytecode have
`bytecodeVars` coordinates (the fresh one because the deferring verifier accepts its proof).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (bufL)

@[expose] public section

/-- Buffer `i` of `bufL` sits at its base. -/
theorem mem_bufL {b : ℕ} {sizes : List ℕ} {cs : List (List E)} {i : ℕ} (h1 : i < sizes.length)
    (h2 : i < cs.length) : ((bases b sizes).getD i 0, cs.getD i []) ∈ bufL b sizes cs := by
  have h1' : i < (bases b sizes).length := by rw [length_bases]; exact h1
  have hl : i < (bufL b sizes cs).length := by simp only [bufL, List.length_zip]; omega
  have he : (bufL b sizes cs)[i]'hl = ((bases b sizes)[i]'h1', cs[i]'h2) := List.getElem_zip
  rw [List.getD_eq_getElem _ _ h1', List.getD_eq_getElem _ _ h2, ← he]
  exact List.getElem_mem hl

variable (fs : String → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement) (w : NodeWitness)

/-- **Buffer `i` of `main`'s honest words** sits at its base. -/
theorem mem_hLmain {i : ℕ} (hi : i < 10) :
    ((mPos (hData seed s w) (fp + fs "main")).getD i 0, (hOwn seed s w).getD i []) ∈
      hLmain fs fp seed s w :=
  List.mem_append_left _ (mem_bufL (by simp [mSizes]; omega) (by simp [hOwn]; omega))

/-- `main`'s words read buffer `i` at `g` to its base. -/
theorem reads_hLmain {rd : Reader} (hM : B1.Main.MemL rd (hLmain fs fp seed s w)) {i : ℕ}
    (hi : i < 10) : ReadsAt rd (gen ^ (mPos (hData seed s w) (fp + fs "main")).getD i 0)
      ((hOwn seed s w).getD i []) :=
  B1.Da.reads_of_memL hM (mem_hLmain fs fp seed s w hi)

variable {seed s w}

/-- **The children's claims' shapes**: `bytecodeVars` coordinates each. -/
theorem kid_shapes {bytecode : List K} (hbl : bytecode.length = 2 ^ bytecodeVars)
    (hrel : NodeRelation bytecode seed s w) : ∀ c ∈ w.children,
      c.freshClaim.bytecodePoint.length = bytecodeVars ∧
        c.statement.deferredClaim.bytecodePoint.length = bytecodeVars := by
  have hlog : Nat.log2 bytecode.length = bytecodeVars := by rw [hbl, Nat.log2_two_pow]
  intro c hc
  obtain ⟨hsh, hv⟩ := hrel.2.2.1 c hc
  exact ⟨by rw [verifyDeferred_shaped hv, hlog], by rw [← hlog]; exact hsh⟩

end
end LeanVM.Guest.B1.Main
