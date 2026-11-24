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
of such windows (`ChainAS`) from the chunks' start to their end is the whole pass
(`alignOk_of_chainAS`, by `Bridge.slice_rest` and `alignGo_append`).
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

/-- **A chain of cuts and named states** of the alignment: each window over the slice from one to
the next, the last at the end. -/
def ChainAS (X : AlignCtx) (body : List Stmt) (C : List (List OffsetInstruction))
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : PCut × KSt → List (PCut × KSt) → Prop
  | (c, K), [] => chainEndS C c K = true
  | (c, K), (c', K') :: ks => winOkAS X body C d c c' K K' = true ∧ ChainAS X body C d (c', K') ks

end

public section

theorem chainAS_go {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} :
    ∀ (ks : List (PCut × KSt)) (c : PCut) (K : KSt) (st : St) (acc : List (ℕ × Zip)),
      ChainAS X body C d (c, K) ks → StOk body d.2.2 st → stOfK body d.2.2 K = st →
      ((alignGo X (restL C c) st acc).bind fun p ↦ alignEnd p.1 p.2).isSome
  | [], c, K, st, acc, hc, _, hk => by
    simp only [ChainAS, chainEndS, Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none,
      List.isEmpty_iff, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨⟨h1, h2⟩, hcur⟩, hpend⟩ := hc
    subst hk
    obtain ⟨c1, c2⟩ := c
    simp only at h1 h2
    subst h1 h2
    rw [restL_end]
    simp [alignGo, alignEnd, stOfK, hcur, hpend]
  | (c', K') :: ks, c, K, st, acc, hc, hst, hk => by
    obtain ⟨hw, hc⟩ := hc
    simp only [winOkAS, Bool.and_eq_true] at hw
    obtain ⟨hs, hw⟩ := hw
    rw [AlignCtx.seq_eq, decide_eq_true_eq, hk] at hw
    obtain ⟨⟨st1, acc1⟩, h1, hK⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨hst1, -⟩ := alignGo_ok X _ hst h1
    rw [← slice_rest hs, alignGo_append, alignGo_acc, h1]
    simp only [Option.map_some, Option.bind_some]
    exact chainAS_go ks c' K' st1 (acc1 ++ acc) hc hst1 (by rw [← hK]; exact stOfK_keyOfSt hst1)

/-- **A chain of the alignment's windows over slices is the whole pass.** -/
theorem alignOk_of_chainAS {X : AlignCtx} {body : List Stmt} {C : List (List OffsetInstruction)}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true) {ks : List (PCut × KSt)}
    (hc : ChainAS X body C d ((0, 0), ⟨0, 0, some ([], 0), [], []⟩) ks) : alignOk X body C.flatten d = true := by
  rw [alignOk, AlignCtx.seq_eq]
  change (alignPre X d && (alignRun X body C.flatten d).isSome) = true
  rw [hpre, Bool.true_and]
  have h0 : stOfK body d.2.2 ⟨0, 0, some ([], 0), [], []⟩ = ⟨0, d.2.2, some (Zip.init body), [], []⟩ := by
    simp [stOfK, zipOf, zUp, blockAt, Zip.init]
  have hst : StOk body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩
  have := chainAS_go ks _ _ _ [] hc hst h0
  simpa [alignRun, restL] using this

end

end LeanVM.Guest.CoreMode
