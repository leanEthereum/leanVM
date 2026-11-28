module

public import LeanVM.Guest.Complete.Agg.Pre3
public import LeanVM.Guest.Memory.GuestWordsA

/-!
# `MainCalleesAt.agg` from the node's final condition

Every field of `AggLeftAt` but `post` holds at the honest data (`agg_pre0`, `agg_pre1`, `agg_pre2`,
`agg_bs`, `agg_pre3` and the regions `agg_reg*`), so `aggLeftAt_of_post` builds it from the final
condition `AggPostAt` alone, and `agg_field_of_post` gives `MainCalleesAt.agg` (at every `al` and
`11 ≤ k`, in particular `alW` and `17`) from `AggPostHyp`.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`aggregate_claims`' final condition at the node `(s, w)` and cursor `c`**: `AggLeftAt.post`. -/
def AggPostAt (al : String → Bool) (k : ℕ) (s : NodeStatement) (w : NodeWitness) (cover : List E) (c : ℕ) :
    Prop :=
  ∀ st : St, (∀ rd, st.O rd → HoldsWords rd (aWo s w c)) →
    st.Qs = [FreePost, FreePost, FreePost, FreePost, FreePost] →
    AggK k (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (aVal (aRd0 al s w cover c) (aOrc w c) (aggArgs al (mainCounts s w))) st

/-- The final condition on every inner node and cursor below `2^62`. -/
def AggPostHyp (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → w.children ≠ [] →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss → ∀ c, c < 2 ^ 62 → AggPostAt al k s w cover c

section
variable {al : String → Bool} {k : ℕ} {s : NodeStatement} {w : NodeWitness} {cover : List E}

/-- **What is left of `aggregate_claims` is its final condition.** -/
theorem aggLeftAt_of_post (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w) (hne : w.children ≠ []) {fp c : ℕ} (hc : c < 2 ^ 62)
    (hpost : AggPostAt al k s w cover c) : AggLeftAt al k s w cover fp c where
  pre0 := agg_pre0 hr hok hne
  reg0 := agg_reg0
  pre1 := agg_pre1 hr hok hne
  reg1 := agg_reg1
  pre2 := agg_pre2 hr hok hne hd hc
  reg2 := agg_reg2
  bs := agg_bs hr hne hd hc
  regbs := agg_regbs
  pre3 := agg_pre3 hr hok hne hd hc
  reg3 := agg_reg3
  post := hpost

/-- **`MainCalleesAt.agg` from the final condition**, at every `al` and `11 ≤ k`. -/
theorem agg_field_of_post (hk : 11 ≤ k) (H : AggPostHyp al k) (hr : NodeRelation guestBytecode guestSeed s w)
    (hd : DeployedLimits s w) (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) :
    w.children ≠ [] → AtEveryB al k "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS al (mainCounts s w) + winTabAt)] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := fun hne =>
  agg_field_of_hypB (agg_fieldB_of_left hk fun s w cover hr hd hok hne hcv _ c _ _ hc =>
    aggLeftAt_of_post hr hd hok hne hc (H s w cover hr hd hok hne hcv c hc)) hr hd hok hcv hne

end

/-- **`MainCalleesOpenAt.agg` at the deployed choices** `alW`, `17`, from the final condition. -/
theorem agg_field_alW (H : AggPostHyp alW 17) {s : NodeStatement} {w : NodeWitness} {cover : List E}
    (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) :
    w.children ≠ [] → AtEveryB alW 17 "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS alW (mainCounts s w) + winTabAt)] []
      (mainR alW (mainCounts s w)) (MainPreA alW s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo alW (mainCounts s w)) (2 ^ 60) (2 ^ 40) :=
  agg_field_of_post (by norm_num) H hr hd hok hcv

end
end LeanVM.Guest.Complete.Agg
