import FORS.SmallBudget.Contact.Signing

/-! **The end of the game for the contact potential, and the bound.** At the end, a recorded contact
at a revealed secret, or a near cover with a recorded contact, against a
completed table, has probability at most the weighted recorded contacts with their coefficients: a
contact has the chance of its weight, settled contacts pay one, and a near cover makes the capped
near potential one. Through the whole game the event is paid by the start potential and
`2^-128 (N rate) + payB` per FORS leaf query. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open HiddenReveal PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable


/-! ### The event -/

/-- **The event of A4** against a completed table: a recorded contact at a revealed secret, or a
near cover with a recorded contact. -/
def A4ev (K : Ctx) (root : Digest) (T : Coordinate → Digest) (s : State) (outcome : Outcome)
    (R : List Coordinate) : Prop :=
  (∃ index κ leaf, Coordinate.fors index κ leaf 0 ∈ R ∧ RecordedContactAt s T K index κ leaf) ∨
  ForsNearRecorded s T K root outcome R

/-- The final value of A4: the chance of a valid transcript and the event over the completion. -/
noncomputable def finalA4 (K : Ctx) (root : Digest) : FinalF := fun o R s =>
  o.elim 0 fun outcome =>
    Pr[fun T => SigningTranscript.Valid outcome.2.1 ∧ A4ev K root T s outcome R | completion s.known]

/-- The final value of A4 is at most one. -/
theorem finalA4_le_one (K : Ctx) (root : Digest) (o : Option HiddenBridge.Outcome) (R : List Coordinate)
    (s : State) : finalA4 K root o R s ≤ 1 := by
  unfold finalA4
  cases o with
  | none => exact zero_le_one
  | some outcome => exact probEvent_le_one

/-! ### The event is monotone in the cache -/

/-- A cached digest stays cached when the run caches more. -/
theorem cachedDigest_mono {s s' : State} (hext : Extends s s') {parameter : PublicParameter}
    {root : Digest} {message : Message} {randomness : Randomness} {digest : MessageDigest}
    (h : cachedDigest s.cache parameter root message randomness = some digest) :
    cachedDigest s'.cache parameter root message randomness = some digest := by
  unfold cachedDigest at h ⊢
  cases h0 : Completeness.allSome (α := fun _ => HashOutput) fun call : DigestCall =>
      s.cache (tweakableHashInput parameter (.message call)
        (messageDigestPayload root message randomness)) with
  | none =>
      rw [h0] at h
      cases h
  | some w =>
      rw [h0] at h
      rw [allSome_of_eq _ w fun call => hext.1 _ _ (allSome_some h0 call)]
      exact h

/-- **A fresh cache entry keeps the event of A4**: every part of it is monotone in the cache and in
the guesses. -/
theorem a4ev_store (K : Ctx) (root : Digest) (T : Coordinate → Digest) (s : State) (outcome : Outcome)
    (R : List Coordinate) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (h : A4ev K root T s outcome R) : A4ev K root T (s.store x u) outcome R := by
  have hext := extends_store s x u hx
  have hrec : ∀ index κ leaf, RecordedContactAt s T K index κ leaf →
      RecordedContactAt (s.store x u) T K index κ leaf := by
    rintro index κ leaf ⟨v, ⟨w, ⟨hc, hi⟩, ht⟩, hr⟩
    exact ⟨v, ⟨w, ⟨hext.1 _ _ hc, hi⟩, ht⟩, hext.2.2 _ hr⟩
  rcases h with ⟨index, κ, leaf, hmem, hc⟩ | ⟨hvalid, digest, hdig, hland, hunsigned, κ, hc, hcov⟩
  · exact Or.inl ⟨index, κ, leaf, hmem, hrec _ _ _ hc⟩
  · exact Or.inr ⟨hvalid, digest, cachedDigest_mono hext hdig, hland, hunsigned, κ, hrec _ _ _ hc, hcov⟩

/-- The final value of A4 grows with a fresh cache entry. -/
theorem finalA4_store (K : Ctx) (root : Digest) (o : Option HiddenBridge.Outcome) (R : List Coordinate)
    (s : State) (x : HashInput) (u : HashOutput) (hx : s.cache x = none) :
    finalA4 K root o R s ≤ finalA4 K root o R (s.store x u) := by
  unfold finalA4
  cases o with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      exact probEvent_mono fun T _ h => ⟨h.1, a4ev_store K root T s outcome R x u hx h.2⟩

/-! ### The end of the game -/

section Final

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- A near cover of a valid finished game makes the near potential at least one. -/
theorem potNF_ge_of_near (hw : wbar ≤ 1) {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View}
    {R : List Coordinate} (hB : BInvF K data Qtot model s P Ms d R budget) {T : Coordinate → Digest}
    {forgery : Forgery} {L : QueryLog SigningSpec} {verified : Bool}
    (h : ForsNearRecorded s T K data.root (forgery, L, verified) R) :
    1 ≤ potNF K data wbar Fail s P Ms L d budget := by
  obtain ⟨hvalid, digest, hdig, hland, hunsigned, κ, -, hcov⟩ := h
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
        ⟨u firstCall, cached_of_pcache K.p data (p := q) h0 firstCall,
          by rwa [Concrete.digestIndex_truncate] at hland⟩
      have hqP := (hB.pinv.mem q).2 hlanded
      have hv : pview K.p data s q = Lifetime.localDigestView (truncateMessageDigest u) :=
        pview_of_pcache (q := q) h0
      unfold potNF potG
      rw [if_neg (by
        rintro (h | h)
        · exact h
        · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
      unfold coreG
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candG
      rw [if_pos (show Unsigned L q from hunsigned)]
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
  simp only [finalA4, Option.elim]
  by_cases hL : signatureLimit < L.length
  · refine le_of_eq_of_le (probEvent_eq_zero fun T _ h => ?_) zero_le
    exact absurd h.1 (by simp [SigningTranscript.Valid]; omega)
  unfold psiF psiCoreF
  rw [if_neg hL]
  refine le_trans ?_ (le_trans le_self_add (le_trans le_self_add le_self_add))
  set near : Prop := 1 ≤ potNF K data wbar Fail s P Ms L d budget with hnear
  have hsub : ∀ T, SigningTranscript.Valid L ∧ A4ev K data.root T s (forgery, L, verified) R →
      ∃ f ∈ (Finset.univ : Finset FIn), K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near) := by
    rintro T ⟨-, h | h⟩
    · obtain ⟨index, κ, leaf, hmem, v, hfct, hrec⟩ := h
      exact ⟨⟨index, κ, leaf, v⟩, Finset.mem_univ _, hfct, hrec, Or.inl hmem⟩
    · have hn := potNF_ge_of_near K data wbar Fail Qtot model hw hB h
      obtain ⟨-, digest, -, -, -, κ, ⟨v, hfct, hrec⟩, -⟩ := h
      exact ⟨_, Finset.mem_univ _, hfct, hrec, Or.inr hn⟩
  calc Pr[fun T => SigningTranscript.Valid L ∧ A4ev K data.root T s (forgery, L, verified) R | completion s.known]
      ≤ Pr[fun T => ∃ f ∈ (Finset.univ : Finset FIn), K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near) |
          completion s.known] := probEvent_mono fun T _ h => hsub T h
    _ ≤ ∑ f ∈ (Finset.univ : Finset FIn),
          Pr[fun T => K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near) | completion s.known] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ K.wsum (gA R (coefU K data wbar Fail s P Ms L d budget)) s := by
        unfold Ctx.wsum
        refine Finset.sum_le_sum fun f _ => ?_
        by_cases hc : Ctx.Recd s f ∧ (Settled R f ∨ near)
        · rw [if_pos hc.1]
          calc Pr[fun T => K.FCT T s f ∧ Ctx.Recd s f ∧ (Settled R f ∨ near) | completion s.known]
              ≤ Pr[fun T => K.FCT T s f | completion s.known] := probEvent_mono fun T _ h => h.1
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
        · rw [probEvent_eq_zero fun T _ h => hc h.2]
          exact zero_le

end Final

/-! ### The bound -/

section Bound

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate) (hMo : model.outgoing = Address.outputCoordinate)

include hMp hMi hMo in
/-- **The contact bound.** In the lazy run of the rest of the game of an adversary that never
repeats a message, a valid finished game with the event A4 has chance at most the start potential
(the coin risk `total (2 − landing)/2^128` per contact, the near forecasts and the cap term
`lam Lmax 0 total`) plus `2^-128 N rate + payB` per expected FORS leaf query, once
`2^-128 ≤ payB + κ 2^-128`. -/
theorem a4F_bound (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : total ≤ Cmax)
    {payB : ℝ≥0∞} (hκ : ν ≤ payB + κ * ν)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M [])
    (known : HiddenReveal.Knowledge Coordinate) (hinv : K.Inv (DebtState.start K.initial known)) :
    ∑' out, Pr[= out | interp K.tg K.initial model (advProg K.p data M []) total (DebtState.start K.initial known)] *
        finalA4 K data.root out.1.1 out.1.2.1 out.2 ≤
      (ν * (((Nat.choose total 2 : ℕ) : ℝ≥0∞) * rateS) +
        κ * ν * ∑ j ∈ Finset.range total, ((j : ℝ≥0∞) * (startNearF wbar j + failMass Fail) +
          signatureLimit * failMass Fail) + lam Lmax 0 total) +
        (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) *
          expCount K model (IsFleafIn K.p) (advProg K.p data M []) total (DebtState.start K.initial known) := by
  rw [← psiF_start K data wbar κ Fail Lmax known total]
  exact final_le_startF K data model (IsFleafIn K.p) _ hMp hMi hparse
    (fun p call => by
      rintro ⟨f, hf⟩
      exact msg_ne_fleaf (msgInput_digestInput K.p data.root p.1 p.2 call) hf) hmsg hclean total
    (fun _ _ => rfl) (finalA4_le_one K data.root) (finalA4_store K data.root)
    (psiF_newPair K data wbar κ Fail total model hfair hQ)
    (psiF_ordinary K data wbar κ Fail total model hMp hMi hfair.le_one hκ Lmax)
    (psiF_sign K data wbar κ Fail total model hMp hMi hMo hparse hmsg hfail hfair.le_one Lmax)
    (psiF_final K data wbar κ Fail total model hfair.le_one Lmax) M hnr known hinv

end Bound

end FORS.Security.ForsPotential
