module

public import FORS.SmallBudget.Contact.PaidPotentialH
public import FORS.SmallBudget.Contact.Bound

@[expose] public section

/-! **The contact potential's payments with the honest signer**: `psiF` pays a new pair, any
other ordinary query and the end of the game under the invariants `BInvFH` (count kept for live
messages only), as under `BInvF`; and the contact bound for the game with the honest signer
(`advProgH`), given the honest signing call's payment and invariants. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open HiddenReveal PotentialA
open FORS.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

section PaysH

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

theorem psiF_newPair {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    NewPairPaysF K data Qtot model (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hb hB p hp0
  have hw := hfair.le_one
  set ℓ := (livePairs L P).length with hℓ
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · refine Or.inl (le_trans hcap ?_)
    unfold psiF psiCoreF
    exact le_add_self
  refine Or.inr ?_
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate K.p data wbar s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hB.count p.1 hlive; omega) (le_trans (landedCount_le hB.pinv L hlive) hlen)
  have hM := hB.minv
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the cap term keeps its mean
  have hlam : pairE (fun u => lam Lmax (livePairs L (addPair K.p P p u)).length y) ≤ lam Lmax ℓ (y + 1) := by
    by_cases hlive : MsgLive L p.1
    · have hl : ∀ u, lam Lmax (livePairs L (addPair K.p P p u)).length y =
          if Landed K.p (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) y else lam Lmax ℓ y := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, ite_eq_left (by simpa using hlive), List.length_cons]
          rfl
        · rfl
      simp only [hl]
      exact le_of_eq (lam_newPair K.p Lmax ℓ y)
    · have hl : ∀ u, lam Lmax (livePairs L (addPair K.p P p u)).length y = lam Lmax ℓ y := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, ite_eq_right (by simpa using hlive)]
          rfl
        · rfl
      simp only [hl, pairE_const]
      exact lam_mono le_rfl (Nat.le_succ y)
  unfold psiF psiCoreF
  rw [pairE_add]
  refine add_le_add ?_ hlam
  by_cases hL : signatureLimit < L.length
  · simp only [ite_eq_left hL, pairE_const, le_refl]
  simp only [ite_eq_right hL]
  have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hB.pinv.first p hp0
  have hi : ∀ call, K.initial (pblk K.p data p call) = none := fun call =>
    initial_none_of_fresh K.initial s hB.inv.prepared _ (hfresh call)
  have hnf : ∀ (call : DigestCall) (f : FIn), pblk K.p data p call ≠ f.input K.p := fun call f =>
    msg_ne_fleaf (msgInput_digestInput K.p data.root p.1 p.2 call)
  have hw' : ∀ (g : FIn → ℝ≥0∞) u, K.wsum g (withPair K.p data s p u) = K.wsum g s := fun g u =>
    K.wsum_storeAll_other g _ u s (pblk_call_injective K.p data p) hfresh hi hnf
  set wS := K.wsum (gA R 0) s with hwS
  set wU := K.wsum (fun f => if Settled R f then 0 else 1) s with hwU
  have hpt : ∀ u, K.wsum (gA R (coefU K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u)
        (addMsg Ms p.1) L d y)) (withPair K.p data s p u) =
      wS + wU * (sigRiskF L + coinRiskF K data (withPair K.p data s p u) (addMsg Ms p.1) L y +
        min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d y)) := by
    intro u
    rw [hw', wsum_gA]
    rfl
  simp only [hpt]
  rw [pairE_add, pairE_add, pairE_add, pairE_const, pairE_const_mul, pairE_add, pairE_add, pairE_const,
    pairE_const_mul, pairE_sum_range]
  have h0 := coinPotF_newPair K data hM L p hp0 y
  have h1 := coinRiskF_newPair K data hM L p hp0 y
  have h2 : pairE (fun u => min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u)
      (addMsg Ms p.1) L d y)) ≤ min 1 (potNF K data wbar Fail s P Ms L d (y + 1)) :=
    le_trans (pairE_min_leF _)
      (min_le_min le_rfl (potNF_newPair K data wbar Fail hw hB.pinv hM hp0 L hrate d y))
  have h3 : ∑ j ∈ Finset.range y, pairE (fun u =>
      potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d j) ≤
      ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P Ms L d j := by
    rw [Finset.sum_range_succ']
    exact le_trans (Finset.sum_le_sum fun j _ =>
      potNF_newPair K data wbar Fail hw hB.pinv hM hp0 L hrate d j) le_self_add
  rw [wsum_gA K R (coefU K data wbar Fail s P Ms L d (y + 1)) s, ← hwS, ← hwU]
  unfold coefU
  gcongr


theorem psiF_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate) (hw : wbar ≤ 1) {payB : ℝ≥0∞}
    (hκ : ν ≤ payB + κ * ν) (Lmax : ℕ) :
    OrdinaryPaysF K data Qtot model (IsFleafIn K.p) (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB)
      (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hb hB x hnew
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmass : ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] = 1 := by simp
  unfold psiF psiCoreF
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [add_right_comm]
  refine add_le_add ?_ (lam_mono le_rfl (Nat.le_succ y))
  by_cases hL : signatureLimit < L.length
  · simp only [ite_eq_left hL, mul_zero, tsum_zero, zero_le]
  simp only [ite_eq_right hL]
  set C0 := coefU K data wbar Fail s P Ms L d y with hC0
  set Q := potNF K data wbar Fail s P Ms L d y with hQ
  set S := ∑ j ∈ Finset.range y, potNF K data wbar Fail s P Ms L d j with hS
  set f1 : ℝ≥0∞ := if IsFleafIn K.p x then 1 else 0 with hf1
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      K.wsum (gA R (coefU K data wbar Fail r.2 P Ms L d y)) r.2 + coinPotF K data r.2 Ms L y +
          κ * ν * ∑ j ∈ Finset.range y, potNF K data wbar Fail r.2 P Ms L d j ≤
        K.wsum (gA R C0) r.2 + coinPotF K data s Ms L y + κ * ν * S := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    have hblocks := same_blocks (parameter := K.p) (data := data) hext (ordinaryStep_cache_ne model x s r hr) hnew
    have hcalls : ∀ q : Pair, LandedIn K.p data s q → ∀ call,
        r.2.cache (pblk K.p data q call) = s.cache (pblk K.p data q call) := by
      intro q hq call
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (hB.pinv.all q hq call)
      rw [hw]
      exact hext.1 _ w hw
    have hcoin : coinRiskF K data r.2 Ms L y = coinRiskF K data s Ms L y := by
      unfold coinRiskF
      simp only [offMass_blocks hblocks]
    have hgrow : ∀ j, potNF K data wbar Fail r.2 P Ms L d j ≤ potNF K data wbar Fail s P Ms L d j := fun j =>
      potG_grow wbar 0 Fail witnessNear_props (fun _ _ _ h => h) hw ENNReal.zero_ne_top hext hblocks
        hcalls (fun q hq => (hB.pinv.mem q).1 hq) Ms L d le_rfl
    have hcoinP : coinPotF K data r.2 Ms L y = coinPotF K data s Ms L y := by
      unfold coinPotF
      simp only [offMass_blocks hblocks]
    refine add_le_add (add_le_add (wsum_mono_g K (fun f => gA_mono R ?_ f) r.2) (le_of_eq hcoinP))
      (mul_le_mul_right (Finset.sum_le_sum fun j _ => hgrow j) _)
    rw [hC0]; unfold coefU; rw [hcoin]
    gcongr
    exact hgrow y
  have hC : ∀ f : FIn, x = f.input K.p → s.known f.inC = none → gA R C0 f ≤ C0 := by
    intro f _ hk
    unfold gA
    rw [ite_eq_right (not_settled_of_unknown hB.rinv hk)]
  have hmean := K.wsum_ordinary model hMp hMi hB.inv hB.gc x (gA R C0) C0 hC
  have hf1le : f1 ≤ 1 := by rw [hf1]; split_ifs <;> simp
  have hC0le : ν * C0 * f1 ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF K data s Ms L y +
      κ * ν * Q := by
    have hsig : sigRiskF L ≤ (signatureLimit : ℝ≥0∞) * revRate := by
      unfold sigRiskF
      gcongr
      exact_mod_cast Nat.sub_le _ _
    calc ν * C0 * f1 = (ν * sigRiskF L + ν * min 1 Q) * f1 + ν * coinRiskF K data s Ms L y * f1 := by
          rw [hC0]; unfold coefU; ring
      _ ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + (payB + κ * ν * Q)) * f1 + ν * coinRiskF K data s Ms L y * 1 := by
          gcongr
          exact capped_splitF hκ Q
      _ = (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF K data s Ms L y +
            κ * ν * Q * f1 := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hf1le)
  calc _ ≤ ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        (K.wsum (gA R C0) r.2 + coinPotF K data s Ms L y + κ * ν * S) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_right (hpt r hr) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
    _ = ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * K.wsum (gA R C0) r.2 +
          (coinPotF K data s Ms L y + κ * ν * S) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
        ring
    _ ≤ (K.wsum (gA R C0) s + ν * C0 * f1) + (coinPotF K data s Ms L y + κ * ν * S) :=
        add_le_add hmean le_rfl
    _ ≤ K.wsum (gA R C0) s + ((ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 +
          ν * coinRiskF K data s Ms L y + κ * ν * Q) + (coinPotF K data s Ms L y + κ * ν * S) := by
        gcongr
    _ = K.wsum (gA R C0) s + (coinPotF K data s Ms L y + ν * coinRiskF K data s Ms L y) + κ * ν * (S + Q) +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by ring
    _ ≤ K.wsum (gA R (coefU K data wbar Fail s P Ms L d (y + 1))) s +
          coinPotF K data s Ms L (y + 1) +
          κ * ν * ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P Ms L d j +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by
        rw [Finset.sum_range_succ, ← coinPotF_succ]
        gcongr
        refine wsum_mono_g K (fun f => gA_mono R ?_ f) s
        rw [hC0]; unfold coefU
        gcongr
        · exact coinRiskF_mono K data s Ms L (Nat.le_succ y)
        · exact potNF_mono K data wbar Fail hw s P (fun q hq => (hB.pinv.mem q).1 hq) Ms L d
            (Nat.le_succ y)


/-- A near cover of a valid finished game makes the near potential at least one. -/
theorem potNF_ge_of_near (hw : wbar ≤ 1) {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View} {R : List Coordinate} {L : QueryLog SigningSpec}
    (hB : BInvFH K data Qtot model s P Ms L d R budget) {T : Coordinate → Digest}
    {forgery : Forgery} {verified : Bool}
    (h : ForsNearRecorded s T K data.root (forgery, L, verified) R) :
    1 ≤ potNF K data wbar Fail s P Ms L d budget := by
  obtain ⟨hvalid, digest, hdig, -, hunsigned, κ, -, hcov⟩ := h
  set q : Pair := (forgery.message, forgery.signature.randomness) with hq
  have hpb : cachedDigest s.cache K.p data.root forgery.message forgery.signature.randomness =
      (pcache K.p data q.1 s q.2).map truncateMessageDigest := rfl
  rw [hpb] at hdig
  cases h0 : pcache K.p data q.1 s q.2 with
  | none =>
      rw [h0] at hdig
      cases hdig
  | some u =>
      rw [h0] at hdig
      have hdig' : truncateMessageDigest u = digest := by simpa using hdig
      subst hdig'
      have hlanded : LandedIn K.p data s q :=
        ⟨u firstCall, cached_of_pcache K.p data (p := q) h0 firstCall, landed_full _ _⟩
      have hqP := (hB.pinv.mem q).2 hlanded
      have hv : pview K.p data s q = Lifetime.localDigestView (truncateMessageDigest u) :=
        pview_of_pcache (q := q) h0
      unfold potNF potG
      rw [ite_eq_right (by
        rintro (h | h)
        · exact h
        · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
      unfold coreG
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candG
      rw [ite_eq_left (show Unsigned L q from hunsigned)]
      split_ifs
      · exact le_rfl
      · calc (1 : ℝ≥0∞) ≤ witnessNear (pview K.p data s q) d := by
              rw [hv]
              exact nearWitness_pos hB.dinv _ κ hcov
          _ ≤ _ := base_le_candValueG wbar witnessNear_props hw s Ms L d _ _ q

/-- **The end of the game.** -/
theorem psiF_final (hw : wbar ≤ 1) (Lmax : ℕ) :
    FinalPaysF K data Qtot model (psiF K data wbar κ Fail Lmax) (finalA4 K data.root) := by
  intro budget s P Ms L d R hB forgery verified
  unfold finalA4
  rw [Option.elim_some]
  by_cases hL : signatureLimit < L.length
  · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun T _ h => ?_) zero_le
    exact absurd h.1 (by simp [SigningTranscript.Valid]; omega)
  unfold psiF psiCoreF
  rw [ite_eq_right hL]
  refine le_trans ?_ (le_trans le_self_add (le_trans le_self_add le_self_add))
  let near : Prop := 1 ≤ potNF K data wbar Fail s P Ms L d budget
  have hsub : ∀ T, SigningTranscript.Valid L ∧ A4ev K data.root T s (forgery, L, verified) R →
      ∃ f ∈ (Finset.univ : Finset FIn), K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near) := by
    rintro T ⟨-, h | h⟩
    · obtain ⟨index, κ, leaf, hmem, v, hfct, hrec⟩ := h
      exact ⟨⟨index, κ, leaf, v⟩, Finset.mem_univ _, hfct, hrec, Or.inl hmem⟩
    · have hn := potNF_ge_of_near K data wbar Fail Qtot model hw hB h
      obtain ⟨-, digest, -, -, -, κ, ⟨v, hfct, hrec⟩, -⟩ := h
      exact ⟨_, Finset.mem_univ _, hfct, hrec, Or.inr hn⟩
  calc Pr{let T ← completion s.known}[SigningTranscript.Valid L ∧ A4ev K data.root T s (forgery, L, verified) R]
      ≤ Pr{let T ← completion s.known}[∃ f ∈ (Finset.univ : Finset FIn), K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near)] := prEvent_mono_of_support _ _ _ fun T _ h => hsub T h
    _ ≤ ∑ f ∈ (Finset.univ : Finset FIn),
          Pr{let T ← completion s.known}[K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near)] :=
        prEvent_exists_finset_le _ _ _
    _ ≤ K.wsum (gA R (coefU K data wbar Fail s P Ms L d budget)) s := by
        unfold Ctx.wsum
        refine Finset.sum_le_sum fun f _ => ?_
        by_cases hc : Ctx.Recd s f ∧ (Settled R f ∨ near)
        · rw [ite_eq_left hc.1]
          calc Pr{let T ← completion s.known}[K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near)]
              ≤ Pr{let T ← completion s.known}[K.FCT T s f] := prEvent_mono_of_support _ _ _ fun T _ h => h.1
            _ = K.cw s f := K.prob_fct s f
            _ ≤ gA R (coefU K data wbar Fail s P Ms L d budget) f * K.cw s f := by
                refine le_mul_of_one_le_left zero_le ?_
                unfold gA
                split_ifs with hS
                · exact le_rfl
                · rcases hc.2 with h | h
                  · exact absurd h hS
                  · unfold coefU
                    refine le_trans ?_ le_add_self
                    rw [min_eq_left h]
        · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun T _ h => hc h.2]
          exact zero_le


end PaysH

/-! ### The bound -/

section BoundH

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate)

include hMp hMi in
/-- **The contact bound with the honest signer**, for the game whose signer reads
honestly (`advProgH`), given that an honest signing call on a fresh message pays the potential
(`SignPaysF`) and keeps the invariants (`SignInvH`). -/
theorem a4F_bound (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (total : ℕ) {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : total ≤ Cmax)
    {payB : ℝ≥0∞} (hκ : ν ≤ payB + κ * ν)
    (hsign : SignPaysF K data total model (psiF K data wbar κ Fail Lmax))
    (hsinv : SignInvH K data total model)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M [])
    (known : HiddenReveal.Knowledge Coordinate) (hinv : K.Inv (DebtState.start K.initial known)) :
    ∑' out, Pr{let x ← interp K.tg K.initial model (advProgH K.p data M []) total (DebtState.start K.initial known)}[x = out] *
        finalA4 K data.root out.1.1 out.1.2.1 out.2 ≤
      (ν * (((Nat.choose total 2 : ℕ) : ℝ≥0∞) * rateS) +
        κ * ν * ∑ j ∈ Finset.range total, ((j : ℝ≥0∞) * (startNearF wbar j + failMass Fail) +
          signatureLimit * failMass Fail) + lam Lmax 0 total) +
        (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) *
          expCount K model (IsFleafIn K.p) (advProgH K.p data M []) total (DebtState.start K.initial known) := by
  rw [← psiF_start K data wbar κ Fail Lmax known total]
  exact final_le_startF K data model (IsFleafIn K.p) _ hMp hMi hparse
    (fun p call => by
      rintro ⟨f, hf⟩
      exact msg_ne_fleaf (msgInput_digestInput K.p data.root p.1 p.2 call) hf) hmsg hclean total
    (fun _ _ => rfl) (finalA4_le_one K data.root) (finalA4_store K data.root)
    (psiF_newPair K data wbar κ Fail total model hfair hQ)
    (psiF_ordinary K data wbar κ Fail total model hMp hMi hfair.le_one hκ Lmax)
    hsign hsinv
    (psiF_final K data wbar κ Fail total model hfair.le_one Lmax) M hnr known hinv

end BoundH

end FORS.Security.ForsPotential
