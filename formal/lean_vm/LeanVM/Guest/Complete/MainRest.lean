/-
  LeanVM.Guest.Complete.MainRest

  `main`'s windows past `mPre`: what is left of `MainHypFromCallees` once `mPre`'s chain is proved.
-/

module

public import LeanVM.Guest.Complete.MainPreChain
public import LeanVM.Guest.Complete.ClaimCells

/-!
# `main`'s windows past `mPre`

`MainRestAt al k s w cover`: from every state with `PreInv … (mBase m 5) (qPre s w)` (where `mPre`'s
chain ends, `wPre_hyp`), the DA branch's, `mMid`'s, the leaf or aggregate branch's and `mPost`'s
windows' hypotheses, ending in `MainHypAt`'s final condition. `mainHypAt_of_rest`: `MainHypAt` from it.
`MainRestFromCallees al k`: `MainRestAt` on every node and coverage table the callees hold on;
`mainWinHypFromCallees_of_rest : MainRestFromCallees al k → MainWinHypFromCallees al k`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC
open LeanVM.Node LeanVM.Protocol

@[expose] public section

/-- **`main`'s windows past `mPre`** at the honest oracle, from where `mPre`'s chain ends. -/
def MainRestAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) : Prop :=
  ∀ st, PreInv al s w cover (mBase (mainCounts s w) 5) (qPre s w) st →
    IteHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) (.n 384) wDa wDaZ st fun s2 =>
    WinsHypT B2C.fs al B2C.cert k (mVal (mRd0 s w cover) (mOrc al s w)) (mOrc al s w)
      (ownData B2C.cert 0 (B2C.fs "main") "main" (mainCounts s w).bufs (mEs (mVal (mRd0 s w cover) (mOrc al s w))))
      (· < 2) (mainPreR s) wMid s2 fun s3 =>
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

/-- **`MainHypAt` from `mPre`'s chain and the windows past it.** -/
theorem mainHypAt_of_rest {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hk : 17 ≤ k) (hr : NodeRelation guestBytecode guestSeed s w) (hlim : DeployedLimits s w)
    (hl : (mainLists s w cover).map List.length = (mainCounts s w).bufs) (hcl : MainCalleesAt al k s w cover)
    (h : MainRestAt al k s w cover) : MainHypAt al k s w cover := by
  unfold MainHypAt MainHyp
  exact wPre_hyp hk hr hlim hl hcl h

/-- **What is left of `main`'s window past `mPre`**: its windows' hypotheses there, on every node and
every coverage table the callees' fields hold on. -/
def MainRestFromCallees (al : String → Bool) (k : ℕ) : Prop :=
  17 ≤ k → k ≤ 23 → MainCalleesA al k → VsCompleteHypA al k guestBytecode guestSeed →
    ∀ s w, NodeRelation guestBytecode guestSeed s w → DeployedLimits s w →
      ChildrenOk guestBytecode guestSeed w → ∀ cover : List E,
        cover.length = (mainCounts s w).sx + (mainCounts s w).ss → MainCalleesAt al k s w cover →
        MainRestAt al k s w cover

theorem mainHypFromCallees_of_rest {al : String → Bool} {k : ℕ} (h : MainRestFromCallees al k) :
    MainHypFromCallees al k := by
  intro hk hk' hc hvs s w hr hlim hok cover hlen hat
  have cc := claimCells_of hr hok
  exact mainHypAt_of_rest hk hr hlim (mainLists_length hlen cc.fresh cc.carried cc.own) hat
    (h hk hk' hc hvs s w hr hlim hok cover hlen hat)

/-- **`MainWinHypFromCallees` from the windows past `mPre`.** -/
theorem mainWinHypFromCallees_of_rest {al : String → Bool} {k : ℕ} (h : MainRestFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_hyp (mainHypFromCallees_of_rest h)

end
end LeanVM.Guest.Complete
