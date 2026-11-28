/-
  LeanVM.Guest.Complete.MainMid

  `main`'s windows past its DA branch: what is left of `MainRestAt` once the DA branch is proved.
-/

module

public import LeanVM.Guest.Complete.MainDaWins

/-!
# `main`'s windows past the DA branch

`MainMidAt al k s w cover`: from every state with `PreInv … (mBase m 5) (qPre s w ++ qDa w)` (where the
DA branch ends, `da_hyp`), `mMid`'s, the leaf or aggregate branch's and `mPost`'s windows' hypotheses,
ending in `MainHypAt`'s final condition. `mainRestAt_of_mid`: `MainRestAt` from it.
`MainMidFromCallees al k`; `mainWinHypFromCallees_of_mid : MainMidFromCallees al k → MainWinHypFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol

@[expose] public section

/-- **`main`'s windows past its DA branch** at the honest oracle, from where the branch ends. -/
def MainMidAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ st, PreInv al s w cover (mBase (mainCounts s w) 5) (qPre s w ++ qDa w) st →
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) wMid st fun s3 =>
    IteHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) (.n 423) wLeaf wAgg s3 fun s4 =>
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) wPost s4 fun st => ∀ rd, LowDef k rd → mainPreR s rd → st.O rd → ∀ ts,
        Tree.KidsValid coreProgram rd (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd)
          (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        KidsPost rd st.Qs (calls (mEs (mVal (mRd0 s w cover) (mOrc al s w)))) ts →
        mainPostR s w rd (.node "main" (over mTL (mVal (mRd0 s w cover) (mOrc al s w)) rd) (mainCounts s w).bufs ts)

/-- **`MainRestAt` from the DA branch and the windows past it.** -/
theorem mainRestAt_of_mid {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hcl : MainCalleesAt al k s w cover) (h : MainMidAt al k s w cover) : MainRestAt al k s w cover :=
  fun _ hst => da_hyp hcl hst h

/-- **What is left of `main`'s window past its DA branch**, on every node and every coverage table the
callees' fields hold on. -/
def MainMidFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainMidAt al k s w cover

theorem mainWinHypFromCallees_of_mid {al : String → Bool} {k : ℕ} (h : MainMidFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_rest fun hk hk' hc hvs s w hr hlim hok cover hlen hat =>
    mainRestAt_of_mid hat (h hk hk' hc hvs s w hr hlim hok cover hlen hat)

end
end LeanVM.Guest.Complete
