/-
  LeanVM.Guest.CoreMode.AlignSlice

  A long function's alignment pass checked in windows over slices of its code chunks, from the
  pairing's states: no window walks the code before it.
-/

module

public import LeanVM.Guest.CoreMode.PairSlice

/-!
# The alignment's windows over slices

`Bridge.winOk` hands each window the whole code (`CompiledFunction.code`, the chunks flattened) and
drops the offsets before it, which the kernel flattens and walks every time. `winOkAS` hands it the
slice of the chunks between two cuts (`Bridge.slice`), as the pairing's `winOkHS` does, and a chain
of such windows (`SliceChain`) from the chunks' start to their end is the whole pass
(`alignOk_of_chainAS`, by `SliceChain.run`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge
open LeanVM.Guest.Core (Stmt)

@[expose] public section

/-- **A window of the alignment over a slice**: from the named state `Ka` the pass over the code's
chunks `C` between the cuts `a` and `b` reaches `Kb`. -/
noncomputable def winOkAS (X : AlignCtx) (body : List Stmt) (C : List (List OffsetInstruction))
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (a b : PCut) (Ka Kb : KSt) : Bool :=
  sliceOk C a b && X.seq fun X ↦ decide ((alignGo X (slice C a b) (stOfK body d.2.2 Ka) []).map
    (fun p ↦ keyOfSt d.2.2 p.1) = some Kb)

end

public section

/-- **A chain of the alignment's windows over slices is the whole pass.** -/
theorem alignOk_of_chainAS {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true) {ks : List (PCut × KSt)}
    (hc : SliceChain C (winOkAS X body C d) ((0, 0), ⟨0, 0, some ([], 0), [], []⟩) ks) :
    alignOk X body C.flatten d = true := by
  rw [alignOk, AlignCtx.seq_eq]
  change (alignPre X d && (alignRun X body C.flatten d).isSome) = true
  rw [hpre, Bool.true_and]
  refine SliceChain.run ⟨fun _ _ ↦ rfl, alignGo_append _, alignGo_acc _, fun c _ _ _ _ hst h ↦ (alignGo_ok _ c hst h).1⟩
    (fun _ _ _ _ h ↦ ?_) hc
  simpa only [winOkAS, Bool.and_eq_true, AlignCtx.seq_eq, decide_eq_true_eq] using h

end

end LeanVM.Guest.CoreMode
