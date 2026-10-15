import Sphincs.BridgePotentialA5

/-! The linear potential on the interpreted comparison: every step of the cost-level lazy
comparison keeps the potential in expectation while paying the digest baseline, the invariant
is preserved, and the final payoff is bounded by the decided events, the pending debts and the
forest part (completing the unexposed coordinates decides each latent step with chance `2^-128`,
independently at different coordinates). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

namespace Ctx

variable (K : Ctx)

/-- A reveal keeps the potential in expectation. -/
theorem sample_mean (y : ℕ) (s : St) (c : Coordinate) :
    ∑' r, Pr[= r | sampleCoordinate c s] * K.pot y r.2 ≤ K.pot y s := by
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, tsum_probOutput_pure_mul]
  | none =>
      rw [sampleCoordinate_unknown c s hc, tsum_probOutput_map_mul]
      exact K.pot_expose_mean y s c hc

theorem inv_sample {s : St} (hinv : K.Inv s) (c : Coordinate) :
    ∀ r ∈ support (sampleCoordinate c s), K.Inv r.2 := by
  intro r hr
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact hinv
  | none =>
      rw [sampleCoordinate_expose c s r hr]
      exact hinv.expose c r.1 hc

theorem inv_read {s : St} (hinv : K.Inv s) (x : HashInput)
    (hguess : ∀ q, HiddenGraph.parse K.p (candidateActive K.p) x = some q →
      s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses) :
    ∀ r ∈ support (readOutside x s), K.Inv r.2 := by
  intro r hr
  rcases readOutside_support x s r hr with h | ⟨hc, h⟩
  · rw [h]
    exact hinv
  · rw [h]
    exact hinv.store x r.1 hc hguess

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : M.incoming = Address.inputCoordinate) (hMo : M.outgoing = Address.outputCoordinate)

include hMp hMi in
/-- **The invariant is preserved by every step.** -/
theorem inv_step (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (s : St) (hinv : K.Inv s) :
    ∀ r ∈ support (costStep M input s), K.Inv r.2 := by
  intro r hr
  rcases input with (draw | (bytes | c)) | amount
  · rw [costStep_inl, lazyStep_draw, support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact hinv
  · rw [costStep_inl] at hr
    cases hp : M.parse bytes with
    | none =>
        rw [lazyStep_unparsed M bytes s hp] at hr
        refine K.inv_read hinv bytes (fun q hq _ => ?_) r hr
        rw [← hMp, hp] at hq
        cases hq
    | some q =>
        have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
        have huniq : ∀ q', HiddenGraph.parse K.p (candidateActive K.p) bytes = some q' → q' = q :=
          fun q' hq' => Option.some.inj (hq'.symm.trans hq)
        cases hk : s.known (M.incoming q.1) with
        | none =>
            rw [lazyStep_guess M bytes s q hp hk, hMi] at hr
            refine K.inv_read (hinv.record _) bytes (fun q' hq' _ => ?_) r hr
            rw [huniq q' hq']
            exact List.mem_cons_self
        | some canonical =>
            by_cases heq : q.2 = canonical
            · rw [lazyStep_canonical M bytes s q hp canonical hk heq, support_map] at hr
              obtain ⟨r', hr', rfl⟩ := hr
              exact K.inv_sample hinv _ r' hr'
            · rw [lazyStep_other M bytes s q hp canonical hk heq] at hr
              refine K.inv_read hinv bytes (fun q' hq' hk' => ?_) r hr
              rw [huniq q' hq', ← hMi, hk] at hk'
              cases hk'
  · rw [costStep_inl, lazyStep_reveal] at hr
    exact K.inv_sample hinv c r hr
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hinv

theorem digestCount_bytes (tg' : Targeting HashInput HashOutput Coordinate) (bytes : HashInput) :
    (digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))))
      : ℝ≥0∞) = if tg'.digest bytes then 1 else 0 := by
  simp only [digestCount, recorded, List.filter_cons, List.filter_nil]
  split_ifs with h1 h2 h2 <;> simp_all

include hMp hMi hMo in
/-- **One step.** -/
theorem step (tg' : Targeting HashInput HashOutput Coordinate) (hdig : tg'.digest = ForestSigner.IsMsgInput)
    {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (hmsg : ∀ x, ForestSigner.IsMsgInput x → K.tg.kind x = .none)
    (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (budget : ℕ) (s : St) (hinv : K.Inv s)
    (hcost : sourceCost input ≤ budget) :
    ∑' r, Pr[= r | costStep M input s] * K.potCap total (budget - sourceCost input) r.2 +
      ENNReal.ofReal (K.ρ / 2 ^ 128) * digestCount tg' (recorded input) ≤ K.potCap total budget s := by
  unfold potCap
  by_cases hb : budget ≤ total
  swap
  · rw [if_neg hb]
    exact le_top
  rw [if_pos hb]
  have hpot : ∀ r : (SourceCostSpec HashInput HashOutput Coordinate).Range input × St,
      (if budget - sourceCost input ≤ total then K.pot (budget - sourceCost input) r.2 else ⊤) =
        K.pot (budget - sourceCost input) r.2 := fun r => if_pos ((Nat.sub_le _ _).trans hb)
  simp only [hpot]
  have hxr : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  rcases input with (draw | (bytes | c)) | amount
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate)
        (.inl (.inl draw))) = 0 := rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero, costStep_inl, lazyStep_draw, tsum_probOutput_map_mul]
    simp only [sourceCost, Nat.sub_zero]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · have hcost1 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))) = 1 :=
      rfl
    rw [hcost1] at hcost ⊢
    obtain ⟨y', rfl⟩ : ∃ y', budget = y' + 1 := ⟨budget - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := budget_le_x (by omega)
    rw [digestCount_bytes, hdig, payment_eq, costStep_inl]
    cases hp : M.parse bytes with
    | none =>
        rw [lazyStep_unparsed M bytes s hp]
        cases hc : s.cache bytes with
        | some u =>
            rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
            show K.pot y' s + _ ≤ _
            have h := K.pot_same hN.high (by linarith [hN.low]) y' s
              (if ForestSigner.IsMsgInput bytes then 1 else 0) (by split_ifs <;> simp)
            calc K.pot y' s + ν * ENNReal.ofReal K.ρ * (if ForestSigner.IsMsgInput bytes then 1 else 0)
                = K.pot y' s + ν * ((if ForestSigner.IsMsgInput bytes then 1 else 0) * ENNReal.ofReal K.ρ) := by ring
              _ ≤ _ := h
        | none =>
            by_cases hd : ForestSigner.IsMsgInput bytes
            · rw [if_pos hd, mul_one]
              exact K.fresh_digest hN hmsg hinv hc hd
            · rw [if_neg hd, mul_zero, add_zero]
              exact K.fresh_zero hN hxr hY hsec hinv hc
    | some q =>
        have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
        have hd : ¬ForestSigner.IsMsgInput bytes := fun hd => by
          rw [parse_msg_none _ _ bytes hd] at hq
          cases hq
        rw [if_neg hd, mul_zero, add_zero]
        cases hk : s.known (M.incoming q.1) with
        | none =>
            rw [lazyStep_guess M bytes s q hp hk, hMi]
            rw [hMi] at hk
            cases hc : s.cache bytes with
            | some u =>
                have hc' : (s.record (q.1.inputCoordinate, q.2)).cache bytes = some u := hc
                rw [readOutside_cached bytes _ u hc', tsum_probOutput_pure_mul]
                exact K.guess_cached hN y' hinv hc q hq hk
            | none => exact K.guess_fresh hN hxr hY hsec hinv hc q hq hk
        | some canonical =>
            by_cases heq : q.2 = canonical
            · rw [lazyStep_canonical M bytes s q hp canonical hk heq, tsum_probOutput_map_mul]
              calc ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot y' r.2
                  ≤ ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot (y' + 1) r.2 :=
                    ENNReal.tsum_le_tsum fun r => mul_le_mul_of_nonneg_left (K.pot_mono (Nat.le_succ _) _) bot_le
                _ ≤ _ := K.sample_mean (y' + 1) s _
            · rw [lazyStep_other M bytes s q hp canonical hk heq]
              cases hc : s.cache bytes with
              | some u =>
                  rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
                  exact K.pot_mono (Nat.le_succ _) s
              | none => exact K.fresh_zero hN hxr hY hsec hinv hc
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate)
        (.inl (.inr (.inr c)))) = 0 := rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero, costStep_inl, lazyStep_reveal]
    simp only [sourceCost, Nat.sub_zero]
    exact K.sample_mean budget s c
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inr amount)) = 0 :=
      rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero]
    change ∑' r, Pr[= r | (pure ((), s) : ProbComp _)] * _ ≤ _
    rw [tsum_probOutput_pure_mul]
    exact K.pot_mono (Nat.sub_le _ _) s

end Model

/-! ### The final payoff -/

theorem payoff_le_one (T : Coordinate → Digest) (s : St) : K.payoff T s ≤ 1 := by
  unfold payoff
  split_ifs <;> simp

/-- Completing an unexposed coordinate hits a set with its share of the space. -/
theorem completion_mem (known : Knowledge Coordinate) (c : Coordinate) (hc : known c = none)
    (S : Set Digest) : Pr[fun T => T c ∈ S | completion known] ≤ (S.encard : ℝ≥0∞) * ν := by
  set Sf : Finset Digest := Finset.univ.filter (· ∈ S) with hSf
  have hS : (S.encard : ℝ≥0∞) = (Sf.card : ℝ≥0∞) := by
    have : S = (Sf : Set Digest) := by
      ext t
      simp [hSf]
    rw [this, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe]
  calc Pr[fun T => T c ∈ S | completion known] = Pr[fun T => ∃ v ∈ Sf, T c = v | completion known] := by
        refine probEvent_ext fun T _ => ?_
        simp [hSf]
    _ ≤ ∑ v ∈ Sf, Pr[fun T => T c = v | completion known] := probEvent_exists_finset_le_sum _ _ _
    _ = ∑ _v ∈ Sf, ν := Finset.sum_congr rfl fun v _ => by rw [completion_guess known c v hc, one_div]; rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hS]

/-- The chance that a completed coordinate takes a value satisfying `Q`. -/
noncomputable def pinChance (o : Option Digest) (Q : Digest → Prop) : ℝ≥0∞ :=
  match o with
  | none => ((Finset.univ.filter Q).card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞)
  | some w => if Q w then 1 else 0

omit [Params] in
/-- **Pinning coordinates.** Completing a knowledge cache satisfies coordinatewise conditions with
the product of their chances. -/
theorem completion_pin (known : Knowledge Coordinate) (P : Coordinate → Digest → Prop) :
    Pr[fun T => ∀ c, P c (T c) | completion known] = ∏ c, pinChance (known c) (P c) := by
  classical
  let allowed : Coordinate → Finset Digest := fun c => match known c with
    | none => Finset.univ.filter (P c)
    | some w => if P c w then Finset.univ else ∅
  have hset : (Finset.univ.filter ((fun T : Coordinate → Digest => ∀ c, P c (T c)) ∘ tableExtending known)) =
      Fintype.piFinset allowed := by
    ext fresh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Function.comp_apply]
    refine forall_congr' fun c => ?_
    cases hc : known c with
    | none => simp [allowed, tableExtending, hc]
    | some w => by_cases hp : P c w <;> simp [allowed, tableExtending, hc, hp]
  rw [completion, probEvent_map, probEvent_uniformSample, hset, Fintype.card_piFinset, Fintype.card_fun]
  rw [Nat.cast_prod, Nat.cast_pow, show ((Fintype.card Digest : ℝ≥0∞)) ^ (Fintype.card Coordinate) =
      ∏ _c : Coordinate, (Fintype.card Digest : ℝ≥0∞) by rw [Finset.prod_const, Finset.card_univ],
    ← ENNReal.prod_div_distrib_of_ne_zero]
  · refine Finset.prod_congr rfl fun c _ => ?_
    cases hc : known c with
    | none => simp only [allowed, hc, pinChance]
    | some w =>
        by_cases hp : P c w
        · simp only [allowed, hc, hp, if_true, Finset.card_univ, pinChance]
          rw [card_digest_ennreal]
          exact ENNReal.div_self (by norm_num) (by norm_num)
        · simp [allowed, hc, hp, pinChance]
  · intro c _
    simp

omit [Params] in
theorem pinChance_true (o : Option Digest) : pinChance o (fun _ => True) = 1 := by
  cases o with
  | none =>
      simp only [pinChance]
      rw [Finset.filter_true, Finset.card_univ, card_digest_ennreal]
      exact ENNReal.div_self (by norm_num) (by norm_num)
  | some w => simp [pinChance]

omit [Params] in
theorem pinChance_congr (o : Option Digest) {Q Q' : Digest → Prop} (h : ∀ v, Q v ↔ Q' v) :
    pinChance o Q = pinChance o Q' := by
  have : Q = Q' := funext fun v => propext (h v)
  rw [this]

omit [Params] in
theorem pinChance_eq (o : Option Digest) (t : Digest) :
    pinChance o (fun v => v = t) = match o with | none => ν | some w => if w = t then 1 else 0 := by
  cases o with
  | none =>
      simp only [pinChance]
      have hc : ∀ inst : DecidablePred fun v : Digest => v = t,
          (@Finset.filter _ (fun v => v = t) inst Finset.univ).card = 1 :=
        fun inst => Finset.card_eq_one.2 ⟨t, by ext v; simp⟩
      rw [hc, Nat.cast_one, card_digest_ennreal, one_div]
      rfl
  | some w => simp [pinChance]

/-- The chance of one forest contact against the completion is its contact weight. -/
theorem prob_fct (s : St) (f : FIn) : Pr[fun T => K.FCT T s f | completion s.known] = K.cw s f := by
  by_cases hfe : K.FE s f
  · obtain ⟨u, hu⟩ := hfe
    have huniq : ∀ v, K.Fr s (f.input K.p) v → v = u := fun v hv => by
      have h1 := hv.1
      rw [hu.1] at h1
      exact (Option.some.inj h1).symm
    have hev : ∀ T, K.FCT T s f ↔ ∀ c, (fun c v => c = f.outC → v = truncateHash u) c (T c) := fun T => by
      constructor
      · rintro ⟨v, hv, ht⟩ c rfl
        rw [← ht, huniq v hv]
      · intro h
        exact ⟨u, hu, (h f.outC rfl).symm⟩
    rw [(probEvent_ext (fun T _ => hev T)).trans
      (completion_pin s.known (fun c v => c = f.outC → v = truncateHash u))]
    rw [Finset.prod_eq_single f.outC]
    · rw [pinChance_congr _ (Q' := fun v => v = truncateHash u) (fun v => by simp), pinChance_eq]
      unfold cw
      cases hk : s.known f.outC with
      | none =>
          have h1 : ¬K.FC s f := fun ⟨_, w, _, hw, _⟩ => by rw [hk] at hw; cases hw
          have h2 : K.Lat s f := ⟨⟨u, hu⟩, hk⟩
          simp only [h1, h2, if_false, if_true]
      | some w =>
          have h2 : ¬K.Lat s f := fun hl => by
            have h3 := hl.2
            rw [hk] at h3
            cases h3
          by_cases hw : w = truncateHash u
          · have h1 : K.FC s f := ⟨u, w, hu, hk, hw.symm⟩
            simp only [h1, hw, if_true]
          · have h1 : ¬K.FC s f := fun ⟨v, w', hv, hw', ht⟩ => by
              rw [hk] at hw'
              cases hw'
              exact hw (by rw [← ht, huniq v hv])
            simp only [h1, h2, hw, if_false]
    · intro c _ hc
      rw [pinChance_congr _ (Q' := fun _ => True) (fun v => by simp [hc]), pinChance_true]
    · simp
  · have h0 := K.cw_of_not_fe hfe
    rw [h0]
    exact probEvent_eq_zero fun T _ ⟨u, hu, _⟩ => hfe ⟨u, hu⟩

/-- The chance of two forest contacts writing different coordinates is the product of their weights. -/
theorem prob_fct2 (s : St) (f g : FIn) (hfg : f.outC ≠ g.outC) :
    Pr[fun T => K.FCT T s f ∧ K.FCT T s g | completion s.known] = K.cw s f * K.cw s g := by
  by_cases hfe : K.FE s f
  · by_cases hge : K.FE s g
    · obtain ⟨u, hu⟩ := hfe
      obtain ⟨u', hu'⟩ := hge
      have huniq : ∀ (h : FIn) (w0 v : HashOutput), K.Fr s (h.input K.p) w0 → K.Fr s (h.input K.p) v → v = w0 :=
        fun h w0 v h0 hv => by
          have h1 := hv.1
          rw [h0.1] at h1
          exact (Option.some.inj h1).symm
      have hev : ∀ T, (K.FCT T s f ∧ K.FCT T s g) ↔
          ∀ c, (fun c v => (c = f.outC → v = truncateHash u) ∧ (c = g.outC → v = truncateHash u')) c (T c) :=
        fun T => by
          constructor
          · rintro ⟨⟨v, hv, ht⟩, ⟨v', hv', ht'⟩⟩ c
            refine ⟨fun hc => ?_, fun hc => ?_⟩
            · rw [hc, ← ht, huniq f u v hu hv]
            · rw [hc, ← ht', huniq g u' v' hu' hv']
          · intro h
            exact ⟨⟨u, hu, ((h f.outC).1 rfl).symm⟩, ⟨u', hu', ((h g.outC).2 rfl).symm⟩⟩
      have hf1 := K.prob_fct s f
      have hg1 := K.prob_fct s g
      rw [(probEvent_ext (fun T _ => hev T)).trans (completion_pin s.known
        (fun c v => (c = f.outC → v = truncateHash u) ∧ (c = g.outC → v = truncateHash u')))]
      have hsplit : ∀ c, pinChance (s.known c)
          (fun v => (c = f.outC → v = truncateHash u) ∧ (c = g.outC → v = truncateHash u')) =
          pinChance (s.known c) (fun v => c = f.outC → v = truncateHash u) *
            pinChance (s.known c) (fun v => c = g.outC → v = truncateHash u') := by
        intro c
        by_cases hcf : c = f.outC
        · have hcg : c ≠ g.outC := fun h => hfg (hcf.symm.trans h)
          rw [pinChance_congr _ (Q' := fun v => c = f.outC → v = truncateHash u) (fun v => by simp [hcg]),
            pinChance_congr (s.known c) (Q := fun v => c = g.outC → v = truncateHash u') (Q' := fun _ => True)
              (fun v => by simp [hcg]), pinChance_true, mul_one]
        · rw [pinChance_congr _ (Q' := fun v => c = g.outC → v = truncateHash u') (fun v => by simp [hcf]),
            pinChance_congr (s.known c) (Q := fun v => c = f.outC → v = truncateHash u) (Q' := fun _ => True)
              (fun v => by simp [hcf]), pinChance_true, one_mul]
      rw [Finset.prod_congr rfl fun c _ => hsplit c, Finset.prod_mul_distrib]
      have hf2 : Pr[fun T => K.FCT T s f | completion s.known] =
          ∏ c, pinChance (s.known c) (fun v => c = f.outC → v = truncateHash u) := by
        refine (probEvent_ext fun T _ => ⟨fun ⟨v, hv, ht⟩ c hc => ?_, fun h => ⟨u, hu, (h f.outC rfl).symm⟩⟩).trans
          (completion_pin s.known (fun c v => c = f.outC → v = truncateHash u))
        rw [hc, ← ht, huniq f u v hu hv]
      have hg2 : Pr[fun T => K.FCT T s g | completion s.known] =
          ∏ c, pinChance (s.known c) (fun v => c = g.outC → v = truncateHash u') := by
        rw [← completion_pin]
        refine probEvent_ext fun T _ => ⟨fun ⟨v, hv, ht⟩ c hc => ?_, fun h => ⟨u', hu', (h g.outC rfl).symm⟩⟩
        rw [hc, ← ht, huniq g u' v hu' hv]
      rw [← hf2, ← hg2, hf1, hg1]
    · rw [K.cw_of_not_fe hge, mul_zero]
      exact probEvent_eq_zero fun T _ ⟨_, ⟨u, hu, _⟩⟩ => hge ⟨u, hu⟩
  · rw [K.cw_of_not_fe hfe, zero_mul]
    exact probEvent_eq_zero fun T _ ⟨⟨u, hu, _⟩, _⟩ => hfe ⟨u, hu⟩

/-- The indicator of a forest contact without guess record against a completed table. -/
noncomputable def ngInd (T : Coordinate → Digest) (s : St) (f : FIn) : ℝ≥0∞ :=
  if Recd s f then 0 else if K.FCT T s f then 1 else 0

/-- The indicator of two related recorded forest contacts against a completed table. -/
noncomputable def pairInd (T : Coordinate → Digest) (s : St) (f g : FIn) : ℝ≥0∞ :=
  if Recd s f ∧ Recd s g ∧ f.Rel g then (if K.FCT T s f ∧ K.FCT T s g then 1 else 0) else 0

/-- The pointwise bound of the payoff. -/
theorem payoff_le_split (T : Coordinate → Digest) (s : St) :
    K.payoff T s ≤ (if Hit K.tg K.initial T s ∨ K.WotsBad s then 1 else 0) + ∑ f, K.ngInd T s f +
      (∑ f, ∑ g, K.pairInd T s f g) / 2 := by
  unfold payoff
  by_cases h : Hit K.tg K.initial T s ∨ K.WotsBad s ∨ (∃ f, K.FCT T s f ∧ ¬Recd s f) ∨
      (∃ f g, f.Rel g ∧ K.FCT T s f ∧ K.FCT T s g)
  swap
  · rw [if_neg h]
    exact bot_le
  rw [if_pos h]
  have hng : ∀ f, K.FCT T s f → ¬Recd s f → (1 : ℝ≥0∞) ≤ ∑ f, K.ngInd T s f := fun f hc hr => by
    have h1 : K.ngInd T s f = 1 := by rw [ngInd, if_neg hr, if_pos hc]
    rw [← h1]
    exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ f)
  rcases h with h | h | ⟨f, hc, hr⟩ | ⟨f, g, hrel, hcf, hcg⟩
  · rw [if_pos (Or.inl h)]; exact le_add_right le_self_add
  · rw [if_pos (Or.inr h)]; exact le_add_right le_self_add
  · exact le_add_right ((hng f hc hr).trans le_add_self)
  · by_cases hrf : Recd s f
    · by_cases hrg : Recd s g
      · refine le_add_left ?_
        have hfgv : K.pairInd T s f g = 1 := by
          rw [pairInd, if_pos (show Recd s f ∧ Recd s g ∧ f.Rel g from ⟨hrf, hrg, hrel⟩),
            if_pos (show K.FCT T s f ∧ K.FCT T s g from ⟨hcf, hcg⟩)]
        have hgfv : K.pairInd T s g f = 1 := by
          rw [pairInd, if_pos (show Recd s g ∧ Recd s f ∧ g.Rel f from ⟨hrg, hrf, FIn.rel_symm hrel⟩),
            if_pos (show K.FCT T s g ∧ K.FCT T s f from ⟨hcg, hcf⟩)]
        have hne : f ≠ g := fun e => hrel.2 (by rw [e])
        have hrow : ∀ a b, K.pairInd T s a b ≤ ∑ b', K.pairInd T s a b' := fun a b =>
          Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ b)
        have h2 : (2 : ℝ≥0∞) ≤ ∑ a, ∑ b, K.pairInd T s a b := by
          calc (2 : ℝ≥0∞) = K.pairInd T s f g + K.pairInd T s g f := by rw [hfgv, hgfv]; norm_num
            _ ≤ ∑ b, K.pairInd T s f b + ∑ b, K.pairInd T s g b := add_le_add (hrow f g) (hrow g f)
            _ = ∑ a ∈ {f, g}, ∑ b, K.pairInd T s a b := by rw [Finset.sum_pair hne]
            _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        calc (1 : ℝ≥0∞) = 2 / 2 := (ENNReal.div_self (by norm_num) (by norm_num)).symm
          _ ≤ _ := ENNReal.div_le_div_right h2 2
      · exact le_add_right ((hng g hcg hrg).trans le_add_self)
    · exact le_add_right ((hng f hcf hrf).trans le_add_self)

theorem tsum_ind (μ : ProbComp (Coordinate → Digest)) (E : (Coordinate → Digest) → Prop) [DecidablePred E] :
    ∑' T, Pr[= T | μ] * (if E T then (1 : ℝ≥0∞) else 0) = Pr[E | μ] := by
  rw [probEvent_eq_tsum_ite]
  refine tsum_congr fun T => ?_
  split_ifs <;> simp

/-- **Final payoff.** The expected payoff is at most the decided events, the pending debts and the
forest part. -/
theorem endValue_le (s : St) (y : ℕ) : endValue K.payoff s ≤ K.pot y s := by
  have hHW : ∑' T, Pr[= T | completion s.known] * (if Hit K.tg K.initial T s ∨ K.WotsBad s then 1 else 0) ≤
      K.done s + K.pend s := by
    by_cases hb : K.Bad s
    · calc _ ≤ ∑' T, Pr[= T | completion s.known] :=
            ENNReal.tsum_le_tsum fun T => mul_le_of_le_one_right' (by split_ifs <;> simp)
        _ ≤ 1 := tsum_probOutput_le_one
        _ = K.done s := by rw [done, if_pos hb]
        _ ≤ _ := le_self_add
    · have hpay : ∀ T, (if Hit K.tg K.initial T s ∨ K.WotsBad s then (1 : ℝ≥0∞) else 0) ≤
          if ∃ c, s.known c = none ∧ T c ∈ debts K.tg K.initial s c then 1 else 0 := by
        intro T
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          rcases h1 with (hr | ⟨c, hc, hT⟩) | hw
          · exact hb (Or.inl hr)
          · exact h2 ⟨c, hc, hT⟩
          · exact hb (Or.inr hw)
        · exact bot_le
        · exact le_rfl
      calc _ ≤ ∑' T, Pr[= T | completion s.known] *
              (if ∃ c, s.known c = none ∧ T c ∈ debts K.tg K.initial s c then 1 else 0) :=
            ENNReal.tsum_le_tsum fun T => mul_le_mul_of_nonneg_left (hpay T) bot_le
        _ = Pr[fun T => ∃ c ∈ (Finset.univ : Finset Coordinate), s.known c = none ∧
              T c ∈ debts K.tg K.initial s c | completion s.known] := by
            rw [probEvent_eq_tsum_ite]
            refine tsum_congr fun T => ?_
            simp only [Finset.mem_univ, true_and]
            split_ifs <;> simp
        _ ≤ ∑ c ∈ (Finset.univ : Finset Coordinate),
              Pr[fun T => s.known c = none ∧ T c ∈ debts K.tg K.initial s c | completion s.known] :=
            probEvent_exists_finset_le_sum _ _ _
        _ ≤ K.pend s := by
            unfold pend
            refine Finset.sum_le_sum fun c _ => ?_
            by_cases hc : s.known c = none
            · rw [if_pos hc]
              calc Pr[fun T => s.known c = none ∧ T c ∈ debts K.tg K.initial s c | completion s.known]
                  ≤ Pr[fun T => T c ∈ debts K.tg K.initial s c | completion s.known] :=
                    probEvent_mono fun T _ h => h.2
                _ ≤ _ := completion_mem s.known c hc _
            · rw [if_neg hc]
              exact le_of_eq (probEvent_eq_zero fun T _ h => hc h.1)
        _ ≤ _ := le_add_self
  have hcell1 : ∀ f, ∑' T, Pr[= T | completion s.known] * K.ngInd T s f = if Recd s f then 0 else K.cw s f := by
    intro f
    by_cases hr : Recd s f
    · simp only [ngInd, hr, if_true, mul_zero, tsum_zero]
    · simp only [ngInd, hr, if_false]
      rw [tsum_ind, K.prob_fct s f]
  have hNG : ∑' T, Pr[= T | completion s.known] * ∑ f, K.ngInd T s f = K.ng s := by
    simp only [Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    exact Finset.sum_congr rfl fun f _ => hcell1 f
  have hcell2 : ∀ f g, ∑' T, Pr[= T | completion s.known] * K.pairInd T s f g =
      if Recd s f ∧ Recd s g ∧ f.Rel g then K.cw s f * K.cw s g else 0 := by
    intro f g
    by_cases hr : Recd s f ∧ Recd s g ∧ f.Rel g
    · simp only [pairInd, if_pos hr]
      rw [tsum_ind, K.prob_fct2 s f g (FIn.outC_ne_of_rel hr.2.2)]
    · simp only [pairInd, hr, if_false, mul_zero, tsum_zero]
  have hPP : ∑' T, Pr[= T | completion s.known] * ((∑ f, ∑ g, K.pairInd T s f g) / 2) = K.pp s / 2 := by
    have hmul : ∀ T, Pr[= T | completion s.known] * ((∑ f, ∑ g, K.pairInd T s f g) / 2) =
        (∑ f, ∑ g, Pr[= T | completion s.known] * K.pairInd T s f g) * 2⁻¹ := by
      intro T
      rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      simp only [Finset.mul_sum]
    refine (tsum_congr hmul).trans ?_
    rw [ENNReal.tsum_mul_right, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
      Finset.sum_congr rfl fun f _ => Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), div_eq_mul_inv]
    refine congrArg (· * 2⁻¹) ?_
    unfold pp
    exact Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => hcell2 f g
  calc endValue K.payoff s
      ≤ ∑' T, Pr[= T | completion s.known] * ((if Hit K.tg K.initial T s ∨ K.WotsBad s then 1 else 0) +
          ∑ f, K.ngInd T s f + (∑ f, ∑ g, K.pairInd T s f g) / 2) :=
        ENNReal.tsum_le_tsum fun T => mul_le_mul_of_nonneg_left (K.payoff_le_split T s) bot_le
    _ = ∑' T, Pr[= T | completion s.known] * (if Hit K.tg K.initial T s ∨ K.WotsBad s then 1 else 0) +
        ∑' T, Pr[= T | completion s.known] * ∑ f, K.ngInd T s f +
        ∑' T, Pr[= T | completion s.known] * ((∑ f, ∑ g, K.pairInd T s f g) / 2) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ K.done s + K.pend s + K.ng s + K.pp s / 2 := by
        rw [hNG, hPP]
        exact add_le_add (add_le_add hHW le_rfl) le_rfl
    _ ≤ K.pot y s := by
        unfold pot latent
        rw [← add_assoc (K.done s + K.pend s)]
        exact le_add_right le_self_add

theorem endValue_le_cap (total y : ℕ) (s : St) : endValue K.payoff s ≤ K.potCap total y s := by
  unfold potCap
  split_ifs
  · exact K.endValue_le s y
  · exact le_top

end Ctx

end Sphincs.Security.PotentialA
