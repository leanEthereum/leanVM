/-
  LeanVM.Guest.CoreMode.PairSlice

  A long function's pairing pass checked in windows over slices of its code chunks and of its advice's
  parts: no window walks the code or the hints before it.
-/

module

public import LeanVM.Guest.CoreMode.PairRun
public import LeanVM.Guest.Bridge.ProgAlSlice

/-!
# The pairing's windows over slices

A window of the pass over the whole code would drop the offsets before it, which the kernel walks
every time; for a long function the walk outweighs a late window. `winOkHS` hands a window the slice
of the code's chunks between two cuts (`Bridge.slice`, built from the chunks it touches), and the
slice of the advice's parts its offsets consume (the parts the advice is written in, `Statement.Data`),
which it must consume whole. The hints after them are at later offsets, so the window's run is the
whole pass's there (`pairGo_appHs`), and a chain of such windows (`ChainHS`) from the chunks' start to
their end is the whole pass (`pairOk_of_chainS`, by `Bridge.slice_rest` and `pairGo_append`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Bridge
open LeanVM.Guest.Core (Stmt)
open LeanVM.Guest.Exec (Trie)

@[expose] public section

/-- **A window of the pairing over a slice**: from the named state `Ka`, the pass over the code's
chunks `C` between the cuts `a` and `b`, with the hints of the advice's parts `A` between the cuts
`ha` and `hb`, consumes them all and reaches `Kb`. -/
noncomputable def winOkHS (X : AlignCtx) (H : HCert) (O S : Trie Unit) (body : List Stmt)
    (C : List (List OffsetInstruction)) (A : List (List (ℕ × List Prover.Exec.Hint))) (a b ha hb : PCut)
    (Ka Kb : KSt) : Bool :=
  sliceOk C a b && sliceOk A ha hb && (PairCtx.ofH X H O S).seq fun P ↦
    (pairGo P (slice C a b) (stOfK body (slice A ha hb) Ka) []).any fun p ↦
      p.1.hs.isEmpty && decide (keyOfSt p.1 = Kb)

/-- The last cuts and state: at the chunks' end, no hint left, nothing pending. -/
def chainEndS (C : List (List OffsetInstruction)) (A : List (List (ℕ × List Prover.Exec.Hint))) (c h : PCut)
    (K : KSt) : Bool :=
  Nat.beq c.1 (lenTR C 0) && Nat.beq c.2 0 && (restL A h).isEmpty && K.cur.isNone && K.pend.isEmpty

/-- **A chain of cuts and named states**: each window over the slices from one to the next, the last
at the end. -/
def ChainHS (X : AlignCtx) (H : HCert) (O S : Trie Unit) (body : List Stmt) (C : List (List OffsetInstruction))
    (A : List (List (ℕ × List Prover.Exec.Hint))) : PCut × PCut × KSt → List (PCut × PCut × KSt) → Prop
  | (c, h, K), [] => chainEndS C A c h K = true
  | (c, h, K), (c', h', K') :: ks =>
    winOkHS X H O S body C A c c' h h' K K' = true ∧ ChainHS X H O S body C A (c', h', K') ks

end

public section

theorem winOkHS_run {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {A : List (List (ℕ × List Prover.Exec.Hint))} {a b ha hb : PCut}
    {Ka Kb : KSt} (h : winOkHS X H O S body C A a b ha hb Ka Kb = true) :
    sliceOk C a b = true ∧ sliceOk A ha hb = true ∧ ∃ st acc,
      pairGo (PairCtx.ofH X H O S) (slice C a b) (stOfK body (slice A ha hb) Ka) [] = some (st, acc) ∧
        st.hs = [] ∧ keyOfSt st = Kb := by
  simp only [winOkHS, Bool.and_eq_true, PairCtx.seq_eq] at h
  obtain ⟨⟨hc, ha⟩, h⟩ := h
  refine ⟨hc, ha, ?_⟩
  generalize pairGo _ _ _ _ = r at h
  obtain _ | ⟨st, acc⟩ := r
  · cases h
  · simp only [Option.any_some, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
    exact ⟨st, acc, rfl, h⟩

/-- The hints a chain leaves are at its first state's offsets or later. -/
theorem chainHS_rest {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {A : List (List (ℕ × List Prover.Exec.Hint))} :
    ∀ (ks : List (PCut × PCut × KSt)) (c h : PCut) (K : KSt), ChainHS X H O S body C A (c, h, K) ks →
      ∀ p ∈ restL A h, X.entry + K.i ≤ p.1
  | [], c, h, K, hc => by
    simp only [ChainHS, chainEndS, Bool.and_eq_true, List.isEmpty_iff] at hc
    simp [hc.1.1.2]
  | (c', h', K') :: ks, c, h, K, hc => by
    obtain ⟨hw, hc⟩ := hc
    obtain ⟨-, hs, st, acc, hrun, hnil, hK⟩ := winOkHS_run hw
    obtain ⟨hi, hcons⟩ := pairGo_eq _ _ hrun
    have ih := chainHS_rest ks c' h' K' hc
    intro p hp
    rw [← slice_rest hs, List.mem_append] at hp
    rcases hp with hp | hp
    · rcases hcons p hp with hp | hp
      · simp [hnil] at hp
      · exact hp
    · have := ih p hp
      rw [← hK] at this
      change X.entry + st.i ≤ p.1 at this
      change _ = K.i + _ at hi
      omega

theorem chainHS_go {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {A : List (List (ℕ × List Prover.Exec.Hint))} :
    ∀ (ks : List (PCut × PCut × KSt)) (c h : PCut) (K : KSt) (acc : List (ℕ × Zip)),
      ChainHS X H O S body C A (c, h, K) ks → StOk body (restL A h) (stOfK body (restL A h) K) →
      ((pairGo (PairCtx.ofH X H O S) (restL C c) (stOfK body (restL A h) K) acc).bind
        fun p ↦ alignEnd p.1 p.2).isSome
  | [], c, h, K, acc, hc, _ => by
    simp only [ChainHS, chainEndS, Bool.and_eq_true, Nat.beq_eq, Option.isNone_iff_eq_none,
      List.isEmpty_iff, lenTR_eq, Nat.add_zero] at hc
    obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, hcur⟩, hpend⟩ := hc
    obtain ⟨c1, c2⟩ := c
    simp only at h1 h2
    subst h1 h2
    rw [restL_end]
    simp [pairGo, alignEnd, stOfK, hcur, hpend]
  | (c', h', K') :: ks, c, h, K, acc, hc, hst => by
    obtain ⟨hw, hc⟩ := hc
    have hrest := chainHS_rest _ _ _ _ hc
    obtain ⟨hcs, hhs, st1, acc1, h1, hnil, hK⟩ := winOkHS_run hw
    have hst0 : StOk body (slice A h h') (stOfK body (slice A h h') K) :=
      ⟨⟨0, rfl⟩, hst.cur, hst.pend, hst.tabs⟩
    obtain ⟨hst1, hi⟩ := pairGo_ok _ _ hst0 h1
    have happ : stOfK body (restL A h) K = appHs (restL A h') (stOfK body (slice A h h') K) := by
      simp only [stOfK, appHs, ← slice_rest hhs]
    have hrun := pairGo_appHs (PairCtx.ofH X H O S) (restL A h') (slice C c c') (stOfK body (slice A h h') K) acc
      fun p hp ↦ by
        have := hrest p hp
        rw [← hK] at this
        change X.entry + st1.i ≤ p.1 at this
        change _ = K.i + _ at hi
        change X.entry + K.i + _ ≤ p.1
        omega
    rw [pairGo_acc _ _ (stOfK body (slice A h h') K) acc, h1] at hrun
    have hend : appHs (restL A h') st1 = stOfK body (restL A h') K' := by
      have := stOfK_keyOfSt hst1
      rw [hK, hnil] at this
      rw [← this]
      rfl
    rw [← slice_rest hcs, pairGo_append, happ, hrun]
    simp only [Option.map_some, Option.bind_some, hend]
    refine chainHS_go ks c' h' K' (acc1 ++ acc) hc ⟨⟨0, rfl⟩, ?_, ?_, ?_⟩
    all_goals rw [← hend]
    · exact hst1.cur
    · exact hst1.pend
    · exact hst1.tabs

/-- **A chain of windows over slices is the whole pass.** -/
theorem pairOk_of_chainS {X : AlignCtx} {H : HCert} {O S : Trie Unit} {body : List Stmt}
    {C : List (List OffsetInstruction)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hpre : alignPre X d = true)
    {A : List (List (ℕ × List Prover.Exec.Hint))} (hA : A.flatten = d.2.2) {ks : List (PCut × PCut × KSt)}
    (hc : ChainHS X H O S body C A ((0, 0), (0, 0), ⟨0, some ([], 0), [], []⟩) ks) :
    pairOk X H O S body C.flatten d = true := by
  rw [pairOk, PairCtx.seq_eq]
  change (alignPre X d && (pairRun (PairCtx.ofH X H O S) body C.flatten d).isSome) = true
  rw [hpre, Bool.true_and]
  have h0 : stOfK body (restL A (0, 0)) ⟨0, some ([], 0), [], []⟩ = ⟨0, d.2.2, some (Zip.init body), [], []⟩ := by
    simp [stOfK, zipOf, zUp, blockAt, Zip.init, restL, hA]
  have hst : StOk body (restL A (0, 0)) (stOfK body (restL A (0, 0)) ⟨0, some ([], 0), [], []⟩) := by
    rw [h0]
    exact ⟨⟨0, by simp [restL, hA]⟩, by simpa using zOk_init body, by simp, by simp⟩
  have := chainHS_go ks _ _ _ [] hc hst
  rw [h0] at this
  simpa [pairRun, restL] using this

end

end LeanVM.Guest.CoreMode
