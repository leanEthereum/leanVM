/-
  LeanVM.Guest.Complete.MainWins

  `main`'s body as one window from its windows' uniform hypotheses.
-/

module

public import LeanVM.Guest.Complete.MainWinData
public import LeanVM.Guest.Complete.MainWin
public import LeanVM.Guest.B1.VsC.VsWins

/-!
# `main`'s windows composed

The generated windows (`MainWinData.lean`: `wPre`, `wDa`, `wDaZ`, `wMid`, `wLeaf`, `wAgg`, `wPost`) compose by
`segA_winsT`, `seg_iteT` and `segT_bind` into `mainSs`, the body before its `ret []`: `main_seg` gives
`SegT … mainSs st K` on `mVal rd0 w` and its temporaries `mTL` read per memory (`over mTL`), from `MainHyp`,
the windows' hypotheses in continuation form. The atoms' equations come from the forward valuation
(`mVal_goodPre`, …), the kernel checks from `wPre_ok`, ….

`MainWinHyp al k s w`: on the node `(s, w)`, an evaluation memory `rd0`, an oracle `w'` and `main`'s own
words `Wo` (`WordsInA`) with `MainHyp` from `mSt0` (the `HeapBuf`s from the frame's end, the callees from
theirs, `Wo` held, no data claimed), its final condition `mainPostR` from the callees' posts.
`mainWindowAt_of_hyp : MainWinHyp al k s w → MainWindowAt al k s w`, and
`mainWindowFromCallees_of_hyp : MainWinHypFromCallees al k → MainWindowFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.B1.Main LeanVM.Node LeanVM.Protocol

@[expose] public section

theorem main_sel_tmp : mTL.lookup (.n 384) = none ∧ mTL.lookup (.n 423) = none := by decide +kernel

section
variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 : Reader) (w : ℕ → E)
  (Own R : ℕ → Prop) (Pre : Reader → Prop)

/-- **`main`'s windows' hypotheses** on `mVal rd0 w`, from the state `st`, `K` after them. -/
def MainHyp (st : St) (K : St → Prop) : Prop :=
  WinsHypT fs al cert k (mVal rd0 w) w Own R Pre wPre st fun s1 =>
    IteHypT fs al cert k (mVal rd0 w) w Own R Pre (.n 384) wDa wDaZ s1 fun s2 =>
      WinsHypT fs al cert k (mVal rd0 w) w Own R Pre wMid s2 fun s3 =>
        IteHypT fs al cert k (mVal rd0 w) w Own R Pre (.n 423) wLeaf wAgg s3 fun s4 =>
          WinsHypT fs al cert k (mVal rd0 w) w Own R Pre wPost s4 K

end

/-- **`main`'s body before its `ret []` is a window** from its windows' hypotheses. -/
theorem main_seg {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k fp : ℕ} {rd0 : Reader}
    {w : ℕ → E} {Own R : ℕ → Prop} {Pre : Reader → Prop} {st : St} {K : St → Prop}
    (h : MainHyp fs al cert k rd0 w Own R Pre st K) :
    SegT fs al cert k mTL "main" fp (mVal rd0 w) Own R Pre mainSs st K := by
  have gPre : ∀ x ∈ atomsW1 wPre, ∃ S, Good rd0 S w (mVal rd0 w) x := fun x hx => by
    have hm := mem_atomsW1 hx
    rw [wPre_flat] at hm
    exact ⟨_, mVal_goodPre (.atom x) hm⟩
  have gMid : ∀ x ∈ atomsW1 wMid, ∃ S, Good rd0 S w (mVal rd0 w) x := fun x hx => by
    have hm := mem_atomsW1 hx
    rw [wMid_flat] at hm
    exact ⟨_, mVal_goodMid (.atom x) hm⟩
  have gPost : ∀ x ∈ atomsW1 wPost, ∃ S, Good rd0 S w (mVal rd0 w) x := fun x hx => by
    have hm := mem_atomsW1 hx
    rw [wPost_flat] at hm
    exact ⟨_, mVal_goodPost (.atom x) hm⟩
  have gDa : mVal rd0 w (.n 384) = 0 → ∀ x ∈ atomsW1 wDa, ∃ S, Good rd0 S w (mVal rd0 w) x := fun h0 x hx => by
    have hm := mem_atomsW1 hx
    rw [wDa_flat] at hm
    exact ⟨_, mVal_goodDa h0 (.atom x) hm⟩
  have gDaZ : mVal rd0 w (.n 384) ≠ 0 → ∀ x ∈ atomsW1 wDaZ, ∃ S, Good rd0 S w (mVal rd0 w) x := fun h0 x hx => by
    have hm := mem_atomsW1 hx
    rw [wDaZ_flat] at hm
    exact ⟨_, mVal_goodDaZ h0 (.atom x) hm⟩
  have gLeaf : mVal rd0 w (.n 423) = 0 → ∀ x ∈ atomsW1 wLeaf, ∃ S, Good rd0 S w (mVal rd0 w) x :=
    fun h0 x hx => by
      have hm := mem_atomsW1 hx
      rw [wLeaf_flat] at hm
      exact ⟨_, mVal_goodLeaf h0 (.atom x) hm⟩
  have gAgg : mVal rd0 w (.n 423) ≠ 0 → ∀ x ∈ atomsW1 wAgg, ∃ S, Good rd0 S w (mVal rd0 w) x := fun h0 x hx => by
    have hm := mem_atomsW1 hx
    rw [wAgg_flat] at hm
    exact ⟨_, mVal_goodAgg h0 (.atom x) hm⟩
  rw [MainHyp] at h
  have e : mainSs = mPre ++ ([.ite (.n 384) mDa mDaZ] ++ (mMid ++ ([.ite (.n 423) mLeaf mAgg] ++ mPost))) := by
    rw [mainSs]; simp only [List.append_assoc]
  rw [e]
  have sPre := segA_winsT (T := mTL) (f := "main") (fp := fp) wPre st _ wPre_ok gPre h
  rw [wPre_flat] at sPre
  refine segT_bind (segT_mono sPre fun s1 h1 => ?_)
  have s1' := seg_iteT (T := mTL) (f := "main") (fp := fp) main_sel_tmp.1 (fun h0 => ⟨wDa_ok, gDa h0⟩)
    (fun h0 => ⟨wDaZ_ok, gDaZ h0⟩) h1
  rw [wDa_flat, wDaZ_flat] at s1'
  refine segT_bind (segT_mono s1' fun s2 h2 => ?_)
  have sMid := segA_winsT (T := mTL) (f := "main") (fp := fp) wMid s2 _ wMid_ok gMid h2
  rw [wMid_flat] at sMid
  refine segT_bind (segT_mono sMid fun s3 h3 => ?_)
  have s3' := seg_iteT (T := mTL) (f := "main") (fp := fp) main_sel_tmp.2 (fun h0 => ⟨wLeaf_ok, gLeaf h0⟩)
    (fun h0 => ⟨wAgg_ok, gAgg h0⟩) h3
  rw [wLeaf_flat, wAgg_flat] at s3'
  refine segT_bind (segT_mono s3' fun s4 h4 => ?_)
  have sPost := segA_winsT (T := mTL) (f := "main") (fp := fp) wPost s4 K wPost_ok gPost h4
  rwa [wPost_flat] at sPost

/-! ## `MainWindowAt` from the windows' hypotheses -/

/-- `main`'s events on `σ0` before its `ret []`. -/
noncomputable def mEs (σ0 : Val) : List Ev := outEvs (walk σ0 mainSs)

/-- The state `main`'s windows start from: its `HeapBuf`s from its frame's end, its callees from their
end, its own words `Wo` held, no data claimed, no callee yet. -/
noncomputable def mSt0 (σ0 : Val) (Wo : Words) : St :=
  ⟨B2C.fs "main", B2C.fs "main" + (allocs σ0 (mEs σ0)).sum, fun rd => HoldsWords rd Wo, fun _ => False, []⟩

/-- **What is left of `main`'s window** on the node `(s, w)`: an evaluation memory `rd0`, an oracle `o`
and `main`'s own words `Wo`, its `HeapBuf`s below `2^40` words and its calls at most `12`, its windows'
hypotheses on `mVal rd0 o` from `mSt0`, ending where the callees' posts give `mainPostR`. -/
def MainWinHyp (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) : Prop :=
  ∃ (rd0 : Reader) (o : ℕ → E) (Wo : Words),
    (allocs (mVal rd0 o) (mEs (mVal rd0 o))).sum < 2 ^ 40 ∧ (calls (mEs (mVal rd0 o))).length ≤ 12 ∧
    WordsInA Wo (0 + 2) (0 + B2C.fs "main") (B2C.fs "main")
      (B2C.fs "main" + (allocs (mVal rd0 o) (mEs (mVal rd0 o))).sum) ∧
    MainHyp B2C.fs al B2C.cert k rd0 o
      (ownData B2C.cert 0 (B2C.fs "main") "main" (allocs (mVal rd0 o) (mEs (mVal rd0 o))) (mEs (mVal rd0 o)))
      (· < 2) (mainPreR s) (mSt0 (mVal rd0 o) Wo)
      fun st => ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
        Tree.KidsValid coreProgram rd (over mTL (mVal rd0 o) rd) (calls (mEs (mVal rd0 o))) ts →
        KidsPost rd st.Qs (calls (mEs (mVal rd0 o))) ts →
        mainPostR s w rd (.node "main" (over mTL (mVal rd0 o) rd) (allocs (mVal rd0 o) (mEs (mVal rd0 o))) ts)

/-- **`main`'s window from its windows' hypotheses.** -/
theorem mainWindowAt_of_hyp {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness}
    (h : MainWinHyp al k s w) : MainWindowAt al k s w := by
  obtain ⟨rd0, o, Wo, hA, hC, hWo, hH⟩ := h
  obtain ⟨es, st', Qs, hw, hq, hseg, hb, hK⟩ := main_seg (fp := 0) hH
  have hes : mEs (mVal rd0 o) = es := congrArg outEvs hw
  have hq' : st'.Qs = Qs := by rw [hq]; rfl
  have ha' : st'.a = B2C.fs "main" + (allocs (mVal rd0 o) es).sum := hseg.1
  have e0 : (mSt0 (mVal rd0 o) Wo).kc = B2C.fs "main" + (allocs (mVal rd0 o) es).sum := by
    show B2C.fs "main" + (allocs _ (mEs _)).sum = _
    rw [hes]
  rw [hes] at hWo hK hA hC
  have hQl : Qs.length = (calls es).length := hseg.2.1
  have hfs := B2C.fs_lt "main"
  have h12 : (calls es).length * stepB ≤ 12 * stepB := Nat.mul_le_mul_right _ hC
  have hT : stepT = 2 ^ 57 := stepT_eq
  have hB : stepB = 2 ^ 52 := stepB_eq
  have hend : st'.kc < 2 ^ 57 := by
    have := hb (by rw [e0, hQl]; omega)
    rw [e0, hQl] at this
    omega
  refine ⟨mVal rd0 o, over mTL (mVal rd0 o), es, Wo, Qs, st'.O, st'.D, st'.kc, hend, hWo, ?_,
    fun rd hl hp ho ts hv hk => ?_⟩
  · rw [hes, ha', e0] at hseg
    exact hseg
  · rw [← hq'] at hk
    exact hK rd hl hp ho ts hv hk

/-- **What is left of `main`'s placed completeness**, as its windows' hypotheses: from its callees left
and `verify_sub`'s placed completeness, on every node, on a memory floor `17 ≤ k ≤ 23`. -/
def MainWinHypFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → MainWinHyp al k s w

theorem mainWindowFromCallees_of_hyp {al : String → Bool} {k : ℕ} (h : MainWinHypFromCallees al k) :
    MainWindowFromCallees al k :=
  fun hk hk' hc hvs s w hr hl hok => mainWindowAt_of_hyp (h hk hk' hc hvs s w hr hl hok)

end
end LeanVM.Guest.Complete
