/-
  LeanVM.Guest.CoreMode.PairSlice

  A long function's pairing pass checked in windows over slices of its code chunks: no window walks
  the code before it.
-/

module

public import LeanVM.Guest.CoreMode.PairRun
public import LeanVM.Guest.Bridge.ProgAlSlice

/-!
# The pairing's windows over slices

`winOkH` (`PairDefs.lean`) hands each window the whole code and drops the offsets before it, which
the kernel walks every time; for a long function the walk outweighs a late window. `winOkHS` hands it
the slice of the code's chunks between two cuts (`Bridge.slice`, built from the chunks it touches),
and a chain of such windows (`ChainHS`) from the chunks' start to their end is the whole pass
(`pairOk_of_chainS`, by `Bridge.slice_rest` and `pairGo_append`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge
open LeanVM.Guest.Core (Stmt)
open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- **A window of the pairing over a slice**: from the named state `Ka` the pass over the code's
chunks `C` between the cuts `a` and `b` reaches `Kb`. -/
noncomputable def winOkHS (X : AlignCtx) (H : HCert) (O S : Trie Unit) (body : List Stmt)
    (C : List (List OffsetInstruction)) (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) (a b : PCut)
    (Ka Kb : KSt) : Bool :=
  sliceOk C a b && (PairCtx.ofH X H O S).seq fun P ↦ decide ((pairGo P (slice C a b)
    (stOfK body d.2.2 Ka) []).map (fun p ↦ keyOfSt d.2.2 p.1) = some Kb)

/-- The last cut and state: at the chunks' end, nothing pending. -/
def chainEndS (C : List (List OffsetInstruction)) (c : PCut) (K : KSt) : Bool :=
  Nat.beq c.1 (lenTR C 0) && Nat.beq c.2 0 && K.cur.isNone && K.pend.isEmpty

/-- **A chain of cuts and named states**: each window over the slice from one to the next, the last
at the end. -/
def ChainHS (X : AlignCtx) (H : HCert) (O S : Trie Unit) (body : List Stmt) (C : List (List OffsetInstruction))
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : PCut × KSt → List (PCut × KSt) → Prop
  | (c, K), [] => chainEndS C c K = true
  | (c, K), (c', K') :: ks => winOkHS X H O S body C d c c' K K' = true ∧ ChainHS X H O S body C d (c', K') ks

end

public section

theorem chainHS_go {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} :
    ∀ (ks : List (PCut × KSt)) (c : PCut) (K : KSt) (st : St) (acc : List (ℕ × Zip)),
      ChainHS X H O S body C d (c, K) ks → StOk body d.2.2 st → stOfK body d.2.2 K = st →
      ((pairGo (PairCtx.ofH X H O S) (restL C c) st acc).bind fun p ↦ alignEnd p.1 p.2).isSome
  | [], c, K, st, acc, hc, _, hk => by
    simp only [ChainHS, chainEndS, Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none,
      List.isEmpty_iff, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨⟨h1, h2⟩, hcur⟩, hpend⟩ := hc
    subst hk
    obtain ⟨c1, c2⟩ := c
    simp only at h1 h2
    subst h1 h2
    rw [restL_end]
    simp [pairGo, alignEnd, stOfK, hcur, hpend]
  | (c', K') :: ks, c, K, st, acc, hc, hst, hk => by
    obtain ⟨hw, hc⟩ := hc
    simp only [winOkHS, Bool.and_eq_true] at hw
    obtain ⟨hs, hw⟩ := hw
    rw [PairCtx.seq_eq, decide_eq_true_eq, hk] at hw
    obtain ⟨⟨st1, acc1⟩, h1, hK⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨hst1, -⟩ := pairGo_ok _ _ hst h1
    rw [← slice_rest hs, pairGo_append, pairGo_acc, h1]
    simp only [Option.map_some, Option.bind_some]
    exact chainHS_go ks c' K' st1 (acc1 ++ acc) hc hst1 (by rw [← hK]; exact stOfK_keyOfSt hst1)

/-- **A chain of windows over slices is the whole pass.** -/
theorem pairOk_of_chainS {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true)
    {ks : List (PCut × KSt)} (hc : ChainHS X H O S body C d ((0, 0), ⟨0, 0, some ([], 0), [], []⟩) ks) :
    pairOk X H O S body C.flatten d = true := by
  rw [pairOk, PairCtx.seq_eq]
  change (alignPre X d && (pairRun (PairCtx.ofH X H O S) body C.flatten d).isSome) = true
  rw [hpre, Bool.true_and]
  have h0 : stOfK body d.2.2 ⟨0, 0, some ([], 0), [], []⟩ = ⟨0, d.2.2, some (Zip.init body), [], []⟩ := by
    simp [stOfK, zipOf, zUp, blockAt, Zip.init]
  have hst : StOk body d.2.2 ⟨0, d.2.2, some (Zip.init body), [], []⟩ :=
    ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩
  have := chainHS_go ks _ _ _ [] hc hst h0
  simpa [pairRun, restL] using this

end

end LeanVM.Guest.CoreMode
