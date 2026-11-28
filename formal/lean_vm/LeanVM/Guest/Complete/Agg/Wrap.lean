module

public import LeanVM.Guest.Complete.Agg.Wins

/-!
# Positions past the addresses

`addressOfIndex` has period `2^64 - 1`, so a run at `c` and one at `c + 2^64 - 1` share their
addresses. `callAtA_wrap`: any call is `CallAtA` at any position with the end `c + 2^64`, its own
words two such runs holding `0` and `1`, which no memory holds. The honest run never reaches such
positions (the guest's memory is below `2^24`); `agg_field_of_hypB` uses it only past `2^62`, where
`AggFieldHypB` (`AggFieldHyp` below `2^62`) does not reach.

This also shows `CallAtA`'s words may be unsatisfiable: a proof of `CallAtA` at a reachable position
by such words would leave the caller's memory unconstructible, so the end chain only works from
satisfiable words.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- Indices `2^64 - 1` apart share their address. -/
theorem addressOfIndex_wrap (c : ℕ) : addressOfIndex (c + (2 ^ 64 - 1)) = addressOfIndex c := by
  show g ^ (c + (2 ^ 64 - 1)) = g ^ c
  rw [pow_add, g_pow_card_sub_one, mul_one]

/-- **Every call is placed at every position**, by own words no memory holds. -/
theorem callAtA_wrap {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {f : String}
    {args rets : List E} {R D : ℕ → Prop} {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B fp c : ℕ} :
    ∃ e, CallAtA fs al cert k f args rets R D (fun _ => True) Pre Post B fp c e := by
  refine ⟨c + (2 ^ 64 - 1) + 1, [(c, [0]), (c + (2 ^ 64 - 1), [1])], ⟨?_, ?_⟩, by omega,
    fun _ _ => trivial, fun rd _ hW _ => ?_⟩
  · intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl <;> right <;> simp
  · exact List.pairwise_pair.mpr (Or.inl (by simp only [List.length_singleton]; omega))
  · exfalso
    have h0 := hW (c, [0]) (by simp) 0 (by simp)
    have h1 := hW (c + (2 ^ 64 - 1), [1]) (by simp) 0 (by simp)
    simp only [LoadHolds, Main.addr_ofK, Nat.add_zero, List.getElem_singleton] at h0 h1
    rw [addressOfIndex_wrap, h0.2] at h1
    exact zero_ne_one (Option.some.inj h1.2)

/-- **`AggFieldHyp` below `2^62`**: the cursors the honest run takes. -/
def AggFieldHypB (al : String → Bool) (k : ℕ) : Prop :=
  ∀ (s : NodeStatement) (w : NodeWitness) (cover : List E), NodeRelation guestBytecode guestSeed s w →
    DeployedLimits s w → ChildrenOk guestBytecode guestSeed w → w.children ≠ [] →
    cover.length = (mainCounts s w).sx + (mainCounts s w).ss →
    ∀ fp c, mLo al (mainCounts s w) ≤ fp → fp + B2C.fs "aggregate_claims" ≤ c → c < 2 ^ 62 →
      AggWinHyp al k (aggArgs al (mainCounts s w)) (mainR al (mainCounts s w)) (MainPreA al s w cover)
        (PopsPost (Prover.batchPushes w.batchingHints)) fp c

/-- **The field `agg` of `MainCalleesAt`**, from `AggFieldHypB`: past `2^62` by `callAtA_wrap`. -/
theorem agg_field_of_hypB {al : String → Bool} {k : ℕ} (H : AggFieldHypB al k) {s : NodeStatement}
    {w : NodeWitness} {cover : List E} (hr : NodeRelation guestBytecode guestSeed s w) (hd : DeployedLimits s w)
    (hok : ChildrenOk guestBytecode guestSeed w)
    (hcv : cover.length = (mainCounts s w).sx + (mainCounts s w).ss) (hne : w.children ≠ []) :
    AtEveryB al k "aggregate_claims"
      [gen ^ (mainCounts s w).nc, mPtr (mainCounts s w) 5 0, mPtr (mainCounts s w) 6 0, mPtr (mainCounts s w) 7 0,
        mPtr (mainCounts s w) 9 0, ptrAt (mGS al (mainCounts s w) + winTabAt)] []
      (mainR al (mainCounts s w)) (MainPreA al s w cover) (PopsPost (Prover.batchPushes w.batchingHints))
      (B2C.fs "aggregate_claims") (mLo al (mainCounts s w)) (2 ^ 60) (2 ^ 40) := by
  intro fp c hlo hfc
  by_cases hc : c < 2 ^ 62
  · exact agg_callAtA_of_hyp rfl hfc (H s w cover hr hd hok hne hcv fp c hlo hfc hc)
  · obtain ⟨e, he⟩ := callAtA_wrap (fs := B2C.fs) (al := al) (cert := B2C.cert) (k := k) (f := "aggregate_claims")
      (args := aggArgs al (mainCounts s w)) (rets := []) (R := mainR al (mainCounts s w)) (D := fun _ => False)
      (Pre := MainPreA al s w cover) (Post := PopsPost (Prover.batchPushes w.batchingHints))
      (B := B2C.fs "aggregate_claims") (fp := fp) (c := c)
    exact ⟨e, fun h => absurd (h.trans (by norm_num)) hc, he⟩

end
end LeanVM.Guest.Complete.Agg
