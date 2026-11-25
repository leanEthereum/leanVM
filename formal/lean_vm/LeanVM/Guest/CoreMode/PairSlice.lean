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
and a chain of such windows (`SliceChain`) from the chunks' start to their end is the whole pass, for
any pass with `SlicePass`'s laws (`SliceChain.run`, by `Bridge.slice_rest`): the pairing's here
(`pairOk_of_chainS`), the alignment's in `AlignSlice.lean`.
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

/-- **A chain of cuts and named states** for the window check `w` over the chunks `C`: each window
from one cut to the next, the last at the end. -/
def SliceChain (C : List (List OffsetInstruction)) (w : PCut → PCut → KSt → KSt → Bool) :
    PCut × KSt → List (PCut × KSt) → Prop
  | (c, K), [] => chainEndS C c K = true
  | (c, K), (c', K') :: ks => w c c' K K' = true ∧ SliceChain C w (c', K') ks

end

public section

/-- **A pass over code** (`pairGo`, `alignGo`) that a chain of windows can check: it composes over
concatenated code, threads the zippers it records, and keeps a state well formed. -/
structure SlicePass (body : List Stmt) (hs : List (ℕ × List Prover.Exec.Hint))
    (go : List OffsetInstruction → St → List (ℕ × Zip) → Option (St × List (ℕ × Zip))) : Prop where
  nil : ∀ st acc, go [] st acc = some (st, acc)
  append : ∀ c1 c2 st acc, go (c1 ++ c2) st acc = (go c1 st acc).bind fun p ↦ go c2 p.1 p.2
  acc : ∀ c st acc, go c st acc = (go c st []).map fun p ↦ (p.1, p.2 ++ acc)
  ok : ∀ c {st st' acc acc'}, StOk body hs st → go c st acc = some (st', acc') → StOk body hs st'

variable {body : List Stmt} {hs : List (ℕ × List Prover.Exec.Hint)}
  {go : List OffsetInstruction → St → List (ℕ × Zip) → Option (St × List (ℕ × Zip))}
  {C : List (List OffsetInstruction)} {w : PCut → PCut → KSt → KSt → Bool}

private theorem sliceChain_go (hg : SlicePass body hs go)
    (hw : ∀ a b Ka Kb, w a b Ka Kb = true → sliceOk C a b = true ∧
      (go (slice C a b) (stOfK body hs Ka) []).map (fun p ↦ keyOfSt hs p.1) = some Kb) :
    ∀ (ks : List (PCut × KSt)) (c : PCut) (K : KSt) (st : St) (acc : List (ℕ × Zip)),
      SliceChain C w (c, K) ks → StOk body hs st → stOfK body hs K = st →
      ((go (restL C c) st acc).bind fun p ↦ alignEnd p.1 p.2).isSome
  | [], (_, _), K, _, acc, hc, _, rfl => by
    simp only [SliceChain, chainEndS, Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none,
      List.isEmpty_iff, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨⟨rfl, rfl⟩, hcur⟩, hpend⟩ := hc
    rw [restL_end, hg.nil]
    simp [alignEnd, stOfK, hcur, hpend]
  | (c', K') :: ks, c, K, _, acc, ⟨hw', hc⟩, hst, rfl => by
    obtain ⟨hs', hw'⟩ := hw _ _ _ _ hw'
    obtain ⟨⟨st1, acc1⟩, h1, rfl⟩ := Option.map_eq_some_iff.mp hw'
    have hst1 := hg.ok _ hst h1
    rw [← slice_rest hs', hg.append, hg.acc, h1]
    simp only [Option.map_some, Option.bind_some]
    exact sliceChain_go hg hw ks c' _ st1 (acc1 ++ acc) hc hst1 (stOfK_keyOfSt hst1)

/-- **A chain of windows over slices is the whole pass**, from the body's start at offset `0`. -/
theorem SliceChain.run (hg : SlicePass body hs go)
    (hw : ∀ a b Ka Kb, w a b Ka Kb = true → sliceOk C a b = true ∧
      (go (slice C a b) (stOfK body hs Ka) []).map (fun p ↦ keyOfSt hs p.1) = some Kb)
    {ks : List (PCut × KSt)} (hc : SliceChain C w ((0, 0), ⟨0, 0, some ([], 0), [], []⟩) ks) :
    ((go C.flatten ⟨0, hs, some (Zip.init body), [], []⟩ []).bind fun p ↦ alignEnd p.1 p.2).isSome := by
  have h0 : stOfK body hs ⟨0, 0, some ([], 0), [], []⟩ = ⟨0, hs, some (Zip.init body), [], []⟩ := by
    simp [stOfK, zipOf, zUp, blockAt, Zip.init]
  have hst : StOk body hs ⟨0, hs, some (Zip.init body), [], []⟩ :=
    ⟨⟨0, rfl⟩, by simpa using zOk_init body, by simp, by simp⟩
  simpa [restL] using sliceChain_go hg hw ks _ _ _ [] hc hst h0

/-- **A chain of the pairing's windows over slices is the whole pass.** -/
theorem pairOk_of_chainS {X : AlignCtx} {H : HCert} {O S : Trie Unit} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (hpre : alignPre X d = true) {ks : List (PCut × KSt)}
    (hc : SliceChain C (winOkHS X H O S body C d) ((0, 0), ⟨0, 0, some ([], 0), [], []⟩) ks) :
    pairOk X H O S body C.flatten d = true := by
  rw [pairOk, PairCtx.seq_eq]
  change (alignPre X d && (pairRun (PairCtx.ofH X H O S) body C.flatten d).isSome) = true
  rw [hpre, Bool.true_and]
  refine SliceChain.run ⟨fun _ _ ↦ rfl, pairGo_append _, pairGo_acc _, fun c _ _ _ _ hst h ↦ (pairGo_ok _ c hst h).1⟩
    (fun _ _ _ _ h ↦ ?_) hc
  simpa only [winOkHS, Bool.and_eq_true, PairCtx.seq_eq, decide_eq_true_eq] using h

end

end LeanVM.Guest.CoreMode
