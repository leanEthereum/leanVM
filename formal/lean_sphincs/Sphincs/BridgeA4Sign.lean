import Sphincs.BridgeA4F

/-! **The contact potential through a signing call.** The signer queries no forest step input, so
it records no forest step, keeps every forest step answer, and exposes the coordinate a step writes
only by revealing its chain. A contact whose chain the call opens at or below `min(t + 1, 3)` (an
event of chance at most the reveal rate plus the mass off the identity of the message, over every run)
is paid by the drop of the reveal rate; otherwise its weight does not move. A latent contact
exposed by the call is decided with chance `2^-128`, whatever the call does. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### What a run avoiding forest step inputs does to forest steps -/

section Avoid

variable (K : Ctx) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate) (hMo : model.outgoing = Address.outputCoordinate)

include hMp hMi in
/-- A run avoiding forest step inputs records no forest step. -/
theorem interp_recd_avoid {α : Type} (comp : OracleComp CostSpec α) (h : Avoids (IsFchainIn K.p) comp) :
    ∀ budget (s : State), ∀ out ∈ support (interp K.tg K.initial model comp budget s),
      ∀ f, Ctx.Recd out.2 f → Ctx.Recd s f := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout f hf
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact hf
  | query_bind input next ih =>
      intro budget s out hout f hf
      obtain ⟨hin, hnext⟩ := (avoids_query_bind (IsFchainIn K.p) input next).1 h
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        have h1 := ih result.1 (hnext result.1) _ result.2 inner hinner f hf
        rcases input with (draw | (bytes | coordinate)) | amount
        · change result ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hresult
          rw [support_map] at hresult
          obtain ⟨v, _, rfl⟩ := hresult
          exact h1
        · rw [costStep_ordinary] at hresult
          rcases ordinaryStep_shape bytes s result hresult with ⟨_, h2 | ⟨_, h2⟩⟩ |
              ⟨a, v, hp, _, ⟨_, h2⟩ | ⟨_, h2⟩⟩ | ⟨a, v, val, _, h2⟩
          · rw [h2] at h1; exact h1
          · rw [h2] at h1; exact h1
          · rw [h2] at h1
            rcases List.mem_cons.1 h1 with he | he
            · exact absurd ⟨f, K.input_of_guess model hMp hMi hp he.symm⟩ (hin bytes rfl)
            · exact he
          · rw [h2] at h1
            rcases List.mem_cons.1 h1 with he | he
            · exact absurd ⟨f, K.input_of_guess model hMp hMi hp he.symm⟩ (hin bytes rfl)
            · exact he
          · rw [h2] at h1; exact h1
        · change result ∈ support (sampleCoordinate coordinate s) at hresult
          rw [sampleCoordinate_expose _ s result hresult] at h1
          exact h1
        · change result ∈ support (pure ((), s) : ProbComp _) at hresult
          rw [support_pure, Set.mem_singleton_iff] at hresult
          subst hresult
          exact h1
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact hf

include hMp hMo in
/-- A query writing a forest chain coordinate is a forest step input. -/
theorem writes_fchain {c : Coordinate} (hc : IsFc c) {x : HashInput} (h : Writes model c x) : IsFchainIn K.p x := by
  obtain ⟨a, v, hp, hout⟩ := h
  rw [hMp] at hp
  obtain ⟨hx, -⟩ := (parse_some_iff _ _ x (a, v)).1 hp
  rw [hMo] at hout
  obtain ⟨index, cc, sp, j, a', i, q, rfl⟩ := hc
  cases a with
  | chain lay tree leaf chainIdx step =>
      simp only [Address.outputCoordinate] at hout
      cases hout
  | fchain index' c' s' j' a'' i' t =>
      exact ⟨FIn.mk index' c' s' j' a'' i' t v, by rw [hx]; rfl⟩

end Avoid

/-- The signing call (uniform start, then the scan) queries no forest step input. -/
theorem avoids_source_fchain (p : PublicParameter) (parameter : PublicParameter) (data : PublicData)
    (message : Message) : Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) (IsFchainIn p)
      (signCostSource parameter data message) :=
  avoids_bind _ (avoids_liftProb _ _) fun ρ => avoids_loop_fchain p parameter data message _ ρ

/-! ### One contact through a signing call -/

section Contact

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate) (hMo : model.outgoing = Address.outputCoordinate)

/-- The position up to which an opening of the chain of a step matters. -/
def kTop (f : FIn) : ℕ := min (f.t.val + 1) 3

/-- The call opens the chain of a step at or below `min(t + 1, 3)`. -/
def OpensF (f : FIn) (reveals : List Coordinate) : Prop :=
  ∃ q : FPos, q.val ≤ kTop f ∧ Coordinate.fchain f.index f.c f.s f.j f.a f.i q ∈ reveals

omit [Params] in
theorem kTop_lt (f : FIn) : kTop f < chainTop := by
  unfold kTop chainTop
  omega

variable {K data Qtot model}

include hMp hMi hMo in
/-- **Facts about one step through a signing call.** -/
theorem sign_step_facts {m : Message} {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View} {R : List Coordinate} (hB : BInvF K data Qtot model s P Ms d R budget)
    (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp K.tg K.initial model (signCostSource K.p data m) budget s))
    (f : FIn) :
    (∀ u, K.Fr o1.2 (f.input K.p) u ↔ K.Fr s (f.input K.p) u) ∧
    (o1.2.known f.outC ≠ none → s.known f.outC = none → OpensF f o1.1.2.1) ∧
    (¬OpensF f o1.1.2.1 → K.cw o1.2 f = K.cw s f) ∧
    (Settled (R ++ o1.1.2.1) f → ¬Settled R f → OpensF f o1.1.2.1) := by
  have havoid := avoids_source_fchain K.p K.p data m
  have hcache := interp_avoids_cache K.tg K.initial model _ _ havoid budget s o1 ho1 (f.input K.p) ⟨f, rfl⟩
  have hext := interp_extends K.tg K.initial model _ budget s o1 ho1
  have hfr : ∀ u, K.Fr o1.2 (f.input K.p) u ↔ K.Fr s (f.input K.p) u := fun u => by
    unfold Ctx.Fr
    rw [hcache]
  have hexp : o1.2.known f.outC ≠ none → s.known f.outC = none → OpensF f o1.1.2.1 := by
    intro hk hs
    have hw : Avoids (Writes model f.outC) (signCostSource K.p data m) :=
      avoids_mono (fun x hx => writes_fchain K model hMp hMo ⟨_, _, _, _, _, _, _, rfl⟩ hx) havoid
    rcases interp_known_new K.tg K.initial model _ f.outC hw budget s o1 ho1 hk with h | h
    · exact absurd hs h
    · -- the written coordinate is not the top: tops are anchors
      have ht : f.t.val + 1 ≤ 3 := by
        by_contra hlt
        have htop : f.t.val + 1 = chainTop := by
          have := f.t.isLt
          simp only [chainTop] at this ⊢
          omega
        have hanchor : K.Anchor f.outC := Or.inr ⟨f.index, f.c, f.s, f.j, f.a, f.i, by
          unfold FIn.outC
          congr 1
          exact Fin.ext htop⟩
        rw [hB.inv.anchored _ hanchor] at hs
        cases hs
      exact ⟨⟨f.t.val + 1, by simp only [chainTop]; omega⟩, by show f.t.val + 1 ≤ min (f.t.val + 1) 3; omega, h⟩
  refine ⟨hfr, hexp, fun hno => ?_, fun hS hnS => ?_⟩
  · refine K.cw_congr1 f hfr ?_
    cases hk : s.known f.outC with
    | none =>
        by_contra hne
        exact hno (hexp hne hk)
    | some w => exact hext.2.1 _ _ hk
  · obtain ⟨q, hq, hmem⟩ := hS
    rcases List.mem_append.1 hmem with h | h
    · exact absurd ⟨q, hq, h⟩ hnS
    · exact ⟨q, le_trans hq (by have := f.t.isLt; unfold kTop; simp only [chainTop] at this; omega), h⟩

include hMp hMi hMo in
/-- **The weight of a contact through a signing call**, and its part on runs opening its chain. -/
theorem sign_cw_mean {m : Message} {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View} {R : List Coordinate} (hB : BInvF K data Qtot model s P Ms d R budget) (f : FIn) :
    ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data m) budget s] *
        K.cw o1.2 f ≤ K.cw s f ∧
    ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data m) budget s] *
        ((if OpensF f o1.1.2.1 then 1 else 0) * K.cw o1.2 f) ≤
      K.cw s f * ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data m) budget s] *
        (if OpensF f o1.1.2.1 then 1 else 0) := by
  set run := interp K.tg K.initial model (signCostSource K.p data m) budget s with hrun
  have hfacts := fun o1 (ho1 : o1 ∈ support run) => sign_step_facts hMp hMi hMo hB o1 ho1 f
  have hmass : ∑' o1, Pr[= o1 | run] = 1 := HiddenDebt.interp_mass _ _ _ _ _ _
  by_cases hlat : K.Lat s f
  · -- a latent contact: decided only through an exposure, with chance `2^-128`
    obtain ⟨⟨u0, hu0⟩, hk⟩ := hlat
    have hfc : ¬K.FC s f := fun ⟨_, w, _, hw, _⟩ => by rw [hk] at hw; cases hw
    have hcw : K.cw s f = ν := by
      unfold Ctx.cw
      rw [if_neg hfc, if_pos ⟨⟨u0, hu0⟩, hk⟩]
    have hpt : ∀ o1 ∈ support run, K.cw o1.2 f ≤
        (if o1.2.known f.outC = some (truncateHash u0) then 1 else 0) +
          ν * (if o1.2.known f.outC = none then 1 else 0) := by
      intro o1 ho1
      obtain ⟨hfr, -, -, -⟩ := hfacts o1 ho1
      unfold Ctx.cw
      by_cases h1 : K.FC o1.2 f
      · have h2 : o1.2.known f.outC = some (truncateHash u0) := by
          obtain ⟨u, w, hu, hw, ht⟩ := h1
          have hu' := (hfr u).1 hu
          have : u = u0 := by
            have e1 := hu'.1
            rw [hu0.1] at e1
            exact (Option.some.inj e1).symm
          subst this
          rw [hw, ht]
        rw [if_pos h1, if_pos h2]
        exact le_self_add
      · rw [if_neg h1]
        by_cases h3 : K.Lat o1.2 f
        · rw [if_pos h3, if_pos h3.2, mul_one]
          exact le_add_self
        · rw [if_neg h3]
          exact zero_le
    have hvalue := HiddenDebt.interp_value_le K.tg K.initial model (signCostSource K.p data m)
      f.outC (truncateHash u0) budget s hk
    have hsplit : ∀ o1 ∈ support run, (if o1.2.known f.outC ≠ none then (1 : ℝ≥0∞) else 0) ≤
        (if OpensF f o1.1.2.1 then 1 else 0) * (if o1.2.known f.outC ≠ none then 1 else 0) := by
      intro o1 ho1
      by_cases hne : o1.2.known f.outC ≠ none
      · rw [if_pos hne, if_pos ((hfacts o1 ho1).2.1 hne hk), one_mul]
      · rw [if_neg hne]; exact zero_le
    have hshare : HiddenDebt.shareν = ν := rfl
    rw [hshare] at hvalue
    constructor
    · calc _ ≤ ∑' o1, Pr[= o1 | run] * ((if o1.2.known f.outC = some (truncateHash u0) then 1 else 0) +
            ν * (if o1.2.known f.outC = none then 1 else 0)) := by
            refine ENNReal.tsum_le_tsum fun o1 => ?_
            by_cases ho1 : o1 ∈ support run
            · exact mul_le_mul_right (hpt o1 ho1) _
            · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
        _ = ∑' o1, Pr[= o1 | run] * (if o1.2.known f.outC = some (truncateHash u0) then 1 else 0) +
            ν * ∑' o1, Pr[= o1 | run] * (if o1.2.known f.outC = none then 1 else 0) := by
            simp only [mul_add, ENNReal.tsum_add]
            rw [← ENNReal.tsum_mul_left]
            congr 1
            exact tsum_congr fun o1 => by ring
        _ ≤ ν * ∑' o1, Pr[= o1 | run] * (if o1.2.known f.outC ≠ none then 1 else 0) +
            ν * ∑' o1, Pr[= o1 | run] * (if o1.2.known f.outC = none then 1 else 0) := add_le_add hvalue le_rfl
        _ = ν * ∑' o1, Pr[= o1 | run] := by
            rw [← mul_add, ← ENNReal.tsum_add]
            congr 1
            refine tsum_congr fun o1 => ?_
            by_cases h : o1.2.known f.outC = none <;> simp [h]
        _ = K.cw s f := by rw [hmass, mul_one, hcw]
    · calc _ ≤ ∑' o1, Pr[= o1 | run] * ((if o1.2.known f.outC = some (truncateHash u0) then 1 else 0) +
            ν * ((if OpensF f o1.1.2.1 then 1 else 0) * (if o1.2.known f.outC = none then 1 else 0))) := by
            refine ENNReal.tsum_le_tsum fun o1 => ?_
            by_cases ho1 : o1 ∈ support run
            · refine mul_le_mul_right ?_ _
              by_cases hO : OpensF f o1.1.2.1
              · rw [if_pos hO, one_mul, one_mul]
                exact hpt o1 ho1
              · rw [if_neg hO, zero_mul, zero_mul, mul_zero, add_zero]
                exact zero_le
            · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
        _ = ∑' o1, Pr[= o1 | run] * (if o1.2.known f.outC = some (truncateHash u0) then 1 else 0) +
            ν * ∑' o1, Pr[= o1 | run] *
              ((if OpensF f o1.1.2.1 then 1 else 0) * (if o1.2.known f.outC = none then 1 else 0)) := by
            simp only [mul_add, ENNReal.tsum_add]
            rw [← ENNReal.tsum_mul_left]
            congr 1
            exact tsum_congr fun o1 => by ring
        _ ≤ ν * ∑' o1, Pr[= o1 | run] *
              ((if OpensF f o1.1.2.1 then 1 else 0) * (if o1.2.known f.outC ≠ none then 1 else 0)) +
            ν * ∑' o1, Pr[= o1 | run] *
              ((if OpensF f o1.1.2.1 then 1 else 0) * (if o1.2.known f.outC = none then 1 else 0)) := by
            refine add_le_add (le_trans hvalue (mul_le_mul_right (ENNReal.tsum_le_tsum fun o1 => ?_) _)) le_rfl
            by_cases ho1 : o1 ∈ support run
            · exact mul_le_mul_right (hsplit o1 ho1) _
            · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
        _ = ν * ∑' o1, Pr[= o1 | run] * (if OpensF f o1.1.2.1 then 1 else 0) := by
            rw [← mul_add, ← ENNReal.tsum_add]
            congr 1
            refine tsum_congr fun o1 => ?_
            by_cases h : o1.2.known f.outC = none <;> by_cases hO : OpensF f o1.1.2.1 <;> simp [h, hO]
        _ = _ := by rw [hcw]
  · -- a decided contact does not move
    have hconst : ∀ o1 ∈ support run, K.cw o1.2 f = K.cw s f := by
      intro o1 ho1
      obtain ⟨hfr, -, -, -⟩ := hfacts o1 ho1
      by_cases hfe : K.FE s f
      · have hk : s.known f.outC ≠ none := fun h => hlat ⟨hfe, h⟩
        obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hk
        exact K.cw_congr1 f hfr (by rw [(interp_extends K.tg K.initial model _ budget s o1 ho1).2.1 _ _ hw, hw])
      · have hfe' : ¬K.FE o1.2 f := fun ⟨u, hu⟩ => hfe ⟨u, (hfr u).1 hu⟩
        rw [K.cw_of_not_fe hfe, K.cw_of_not_fe hfe']
    have hcongr : ∀ (G : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞),
        ∑' o1, Pr[= o1 | run] * (G o1 * K.cw o1.2 f) = K.cw s f * ∑' o1, Pr[= o1 | run] * G o1 := by
      intro G
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun o1 => ?_
      by_cases ho1 : o1 ∈ support run
      · rw [hconst o1 ho1]
        ring
      · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul, mul_zero]
    constructor
    · have h := hcongr (fun _ => 1)
      simp only [one_mul, mul_one] at h
      rw [h, hmass, mul_one]
    · exact le_of_eq (hcongr _)

omit [Params] in
theorem settled_append {R : List Coordinate} {f : FIn} (h : Settled R f) (L : List Coordinate) :
    Settled (R ++ L) f := by
  obtain ⟨q, hq, hmem⟩ := h
  exact ⟨q, hq, List.mem_append_left _ hmem⟩

include hMp hMi hMo in
/-- **One contact through a signing call.** Its weight times its coefficient after the call is at
most its weight times the coefficient before: an opening of its chain has chance at most the
reveal rate plus the mass off the identity of the message, and costs at most `1 + Cd`. -/
theorem sign_contact {m : Message} {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View} {R : List Coordinate} (hB : BInvF K data Qtot model s P Ms d R budget)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none)
    (f : FIn) (Cd : ℝ≥0∞) (Z : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞) (hZ : ∀ o, Z o ≤ 1) :
    ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data m) budget s] *
        (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0) ≤
      K.cw s f * gA R (revRate + offMass K.p data s m + Cd +
        ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data m) budget s] *
          Z o1) f := by
  set run := interp K.tg K.initial model (signCostSource K.p data m) budget s with hrun
  set nm : ℝ≥0∞ := offMass K.p data s m with hnm
  have hfacts := fun o1 (ho1 : o1 ∈ support run) => sign_step_facts hMp hMi hMo hB o1 ho1 f
  obtain ⟨hmean, hopen⟩ := sign_cw_mean (m := m) hMp hMi hMo hB f
  have hmass : ∑' o1, Pr[= o1 | run] = 1 := HiddenDebt.interp_mass _ _ _ _ _ _
  by_cases hS : Settled R f
  · unfold gA
    rw [if_pos hS, mul_one]
    refine le_trans (ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right ?_ _) hmean
    split_ifs with h1 h2
    · rw [mul_one]
    · exact absurd (settled_append hS _) h2
    · exact zero_le
  -- an unsettled contact
  have hPO : ∑' o1, Pr[= o1 | run] * (if OpensF f o1.1.2.1 then 1 else 0) ≤ revRate + nm := by
    refine le_trans (le_of_eq (tsum_congr fun o1 => ?_)) (le_trans (reveal_le_all K.tg K.initial model K.p data m
      hparse budget f.index f.c f.s f.j f.a f.i (kTop f) (kTop_lt f))
      (add_le_add le_rfl (hitMass_le_offMass s m)))
    unfold OpensF
    congr 1
    split_ifs <;> rfl
  set PO := ∑' o1, Pr[= o1 | run] * (if OpensF f o1.1.2.1 then 1 else 0) with hPOdef
  set PN := ∑' o1, Pr[= o1 | run] * (if OpensF f o1.1.2.1 then 0 else 1) with hPNdef
  set EZ := ∑' o1, Pr[= o1 | run] * Z o1 with hEZ
  have hsum1 : PO + PN = 1 := by
    rw [hPOdef, hPNdef, ← ENNReal.tsum_add, ← hmass]
    refine tsum_congr fun o1 => ?_
    split_ifs <;> simp
  have hpt : ∀ o1 ∈ support run,
      (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0) ≤
        (1 + Cd) * ((if OpensF f o1.1.2.1 then 1 else 0) * K.cw o1.2 f) +
          K.cw s f * ((if OpensF f o1.1.2.1 then 0 else 1) * Cd + Z o1) := by
    intro o1 ho1
    obtain ⟨-, -, hsame, hset⟩ := hfacts o1 ho1
    split_ifs with hsome hO
    · -- an opening: the coefficient is at most `1 + Cd`
      refine le_add_right ?_
      rw [one_mul, mul_comm (1 + Cd)]
      refine mul_le_mul_right ?_ _
      unfold gA
      split_ifs
      · exact le_add_right le_rfl
      · rw [add_comm 1 Cd]
        exact add_le_add le_rfl (hZ o1)
    · -- no opening: the weight stays and the contact stays unsettled
      rw [zero_mul, mul_zero, zero_add, one_mul, hsame hO]
      unfold gA
      rw [if_neg (fun h => hO (hset h hS))]
    · exact zero_le
    · exact zero_le
  have hE : ∑' o1, Pr[= o1 | run] * (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0) ≤
      (1 + Cd) * (K.cw s f * PO) + K.cw s f * (PN * Cd + EZ) := by
    calc _ ≤ ∑' o1, Pr[= o1 | run] * ((1 + Cd) * ((if OpensF f o1.1.2.1 then 1 else 0) * K.cw o1.2 f) +
          K.cw s f * ((if OpensF f o1.1.2.1 then 0 else 1) * Cd + Z o1)) := by
          refine ENNReal.tsum_le_tsum fun o1 => ?_
          by_cases ho1 : o1 ∈ support run
          · exact mul_le_mul_right (hpt o1 ho1) _
          · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
      _ = ∑' o1, ((1 + Cd) * (Pr[= o1 | run] * ((if OpensF f o1.1.2.1 then 1 else 0) * K.cw o1.2 f)) +
          K.cw s f * Cd * (Pr[= o1 | run] * (if OpensF f o1.1.2.1 then 0 else 1)) +
          K.cw s f * (Pr[= o1 | run] * Z o1)) := tsum_congr fun o1 => by ring
      _ = (1 + Cd) * ∑' o1, Pr[= o1 | run] * ((if OpensF f o1.1.2.1 then 1 else 0) * K.cw o1.2 f) +
          K.cw s f * (PN * Cd + EZ) := by
          rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
            ENNReal.tsum_mul_left, ← hPNdef, ← hEZ]
          ring
      _ ≤ (1 + Cd) * (K.cw s f * PO) + K.cw s f * (PN * Cd + EZ) := by gcongr
  refine le_trans hE ?_
  unfold gA
  rw [if_neg hS]
  calc (1 + Cd) * (K.cw s f * PO) + K.cw s f * (PN * Cd + EZ)
      = K.cw s f * (PO + (PO + PN) * Cd + EZ) := by ring
    _ = K.cw s f * (PO + Cd + EZ) := by rw [hsum1, one_mul]
    _ ≤ K.cw s f * (revRate + nm + Cd + EZ) := by gcongr

end Contact

/-! ### Coins through a signing call -/

section Coins

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {parameter : PublicParameter} {data : PublicData}

/-- **The masses off the identity before a signing call**: the signed message and the other live
messages. -/
theorem offSum_split {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) {L : QueryLog SigningSpec}
    {m : Message} (hm : MsgLive L m) :
    ((live L Ms).map fun m' => offMass parameter data s m').sum =
      offMass parameter data s m + ((restMsgs m L Ms).map fun m' => offMass parameter data s m').sum := by
  rw [← offSum_addMsg hM L m, ((live_perm hm hM.nodup).map _).sum_eq, List.map_cons, List.sum_cons]

/-- **The masses off the identity after a signing call**: the signed message is no longer live and
the other messages keep their statuses. -/
theorem offSum_after (m : Message) (budget : ℕ) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) :
    ((live (L ++ [⟨m, r⟩]) (addMsg Ms m)).map fun m' => offMass parameter data out.2 m').sum =
      ((restMsgs m L Ms).map fun m' => offMass parameter data s m').sum := by
  have hkept : ∀ m' ∈ restMsgs m L Ms, offMass parameter data out.2 m' = offMass parameter data s m' := by
    intro m' hm'
    have hne : m' ≠ m := by
      unfold restMsgs at hm'
      simpa using (List.mem_filter.1 hm').2
    exact offMass_congr fun ρ => other_message_keptS tg initial model budget s out hout (m', ρ) hne
  rw [live_after, List.map_congr_left hkept]

end Coins

/-! ### A signing call -/

section SignPays

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : model.incoming = Address.inputCoordinate) (hMo : model.outgoing = Address.outputCoordinate)

include hMp hMi hMo in
/-- **A signing call on a fresh message.** -/
theorem psiF_sign (hparse : ∀ p, model.parse (pblk K.p data p) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (Lmax : ℕ) :
    SignPaysF K data Qtot model (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hB m hm
  have hM := hB.minv
  set run := interp K.tg K.initial model (signCostSource K.p data m) budget s with hrun
  set ℓ := (livePairs L P).length with hℓ
  have hmass : ∑' o1, Pr[= o1 | run] = 1 := HiddenDebt.interp_mass _ _ _ _ _ _
  -- the cap term does not grow
  have hlam : ∀ (o1 : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature),
      lam Lmax (livePairs (L ++ [⟨m, r⟩]) (newPairs K.p data m s o1.2 ++ P)).length
        (budget - traceCost o1.1.2.2.1) ≤ lam Lmax ℓ budget := by
    intro o1 r
    refine lam_mono ?_ (Nat.sub_le _ _)
    unfold livePairs
    rw [List.filter_append]
    have hnew : (newPairs K.p data m s o1.2).filter
        (fun q => decide (MsgLive (L ++ [⟨m, r⟩]) q.1)) = [] := by
      refine List.filter_eq_nil_iff.2 fun q hq => ?_
      obtain ⟨hqm, _, _⟩ := (mem_newPairs K.p data m s).1 hq
      simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
      exact fun _ => hqm
    rw [hnew, List.nil_append]
    refine (List.Sublist.length_le ?_)
    refine List.monotone_filter_right _ fun q hq => ?_
    simp only [decide_eq_true_eq, msgLive_append] at hq ⊢
    exact hq.1
  set X : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 (fun r => psiCoreF K data wbar κ Fail o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m)
      (L ++ [⟨m, r⟩]) (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) with hX
  have hsplitX : ∀ o1, o1.1.1.elim 0 (fun r => psiF K data wbar κ Fail Lmax o1.2 (newPairs K.p data m s o1.2 ++ P)
      (addMsg Ms m) (L ++ [⟨m, r⟩]) (discAfter K.p data m s d o1) (R ++ o1.1.2.1)
      (budget - traceCost o1.1.2.2.1)) ≤ X o1 + lam Lmax ℓ budget := by
    intro o1
    cases hres : o1.1.1 with
    | none => simp only [Option.elim]; exact zero_le
    | some r =>
        simp only [hX, hres, Option.elim]
        unfold psiF
        exact add_le_add le_rfl (hlam o1 r)
  suffices hmain : ∑' o1, Pr[= o1 | run] * X o1 ≤ psiCoreF K data wbar κ Fail s P Ms L d R budget by
    calc _ ≤ ∑' o1, Pr[= o1 | run] * (X o1 + lam Lmax ℓ budget) :=
          ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right (hsplitX o1) _
      _ = ∑' o1, Pr[= o1 | run] * X o1 + lam Lmax ℓ budget := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
      _ ≤ _ := by
          unfold psiF
          exact add_le_add hmain le_rfl
  by_cases hL : signatureLimit ≤ L.length
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun o1 => ?_) zero_le
    cases hres : o1.1.1 with
    | none => simp only [hX, hres, Option.elim, mul_zero]
    | some r =>
        simp only [hX, hres, Option.elim]
        unfold psiCoreF
        rw [if_pos (by simp only [List.length_append, List.length_singleton]; omega), mul_zero]
  push Not at hL
  set nm : ℝ≥0∞ := offMass K.p data s m with hnm
  set coinD : ℝ≥0∞ := ((restMsgs m L Ms).map fun m' => offMass K.p data s m').sum + budget * rateS with hcoinD
  have hcoinsplit : coinRiskF K data s Ms L budget = nm + coinD := by
    unfold coinRiskF
    rw [offSum_split hM hm, hcoinD, add_assoc]
  set restSum : ℝ≥0∞ := ((restMsgs m L Ms).map fun m' => offMass K.p data s m').sum with hrestSum
  set coinPD : ℝ≥0∞ := ν * ((budget : ℝ≥0∞) * restSum + ((Nat.choose budget 2 : ℕ) : ℝ≥0∞) * rateS) with hcoinPD
  set Cd : ℝ≥0∞ := ((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) * revRate + coinD with hCd
  set canon : ℕ → Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun k o1 =>
    canonL K.p data witnessNear wbar 0 Fail m s P Ms L d (fun _ => False) k o1 with hcanon
  set Z : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 => min 1 (canon budget o1) with hZ
  have hZ1 : ∀ o, Z o ≤ 1 := fun o => min_le_left _ _
  have hse : ∀ k, ∑' o1, Pr[= o1 | run] * canon k o1 ≤ potNF K data wbar Fail s P Ms L d k := fun k =>
    sign_expectG_level K.tg K.initial model K.p data wbar 0 Fail m witnessNear_props (fun _ => False) hparse
      ENNReal.zero_ne_top budget k s P Ms L hm d hM
  have hpoint : ∀ o1 ∈ support run, ∀ r, o1.1.1 = some r → ∀ k' K', k' ≤ K' →
      potNF K data wbar Fail o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
          (discAfter K.p data m s d o1) k' ≤
        canon K' o1 := fun o1 ho1 r hr k' K' hk =>
    sign_pointG_level K.tg K.initial model K.p data wbar 0 Fail Qtot m witnessNear_props (fun _ _ _ h => h)
      hparse (hfail m) hw ENNReal.zero_ne_top budget s P Ms L d R hB.inv.prepared hB.pinv hM
      hB.dinv hB.count o1 ho1 r hr hk
  -- the pointwise bound
  have hpt : ∀ o1 ∈ support run,
      X o1 ≤
        (∑ f, if Ctx.Recd s f then (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0)
          else 0) + coinPD + κ * ν * ∑ j ∈ Finset.range budget, canon j o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        simp only [hX, hres, Option.elim]
        exact zero_le
    | some r =>
        simp only [hX, hres, Option.elim]
        unfold psiCoreF
        rw [if_neg (by simp only [List.length_append, List.length_singleton]; omega)]
        set y' := budget - traceCost o1.1.2.2.1 with hy'
        have hy'le : y' ≤ budget := Nat.sub_le _ _
        have hrecd : ∀ f, Ctx.Recd o1.2 f ↔ Ctx.Recd s f := fun f =>
          ⟨interp_recd_avoid K model hMp hMi _ (avoids_source_fchain K.p K.p data m) budget s o1
            ho1 f, fun h => (interp_extends K.tg K.initial model _ budget s o1 ho1).2.2 _ h⟩
        have hlen : signatureLimit - (L ++ [(⟨m, r⟩ : (_ : Message) × Option Signature)]).length =
            signatureLimit - (L.length + 1) := by simp
        have hcoin : coinRiskF K data o1.2 (addMsg Ms m) (L ++ [⟨m, r⟩]) y' ≤ coinD := by
          unfold coinRiskF
          rw [offSum_after K.tg K.initial model m budget s Ms L o1 ho1 r, hcoinD]
          gcongr
        have hcoef : coefU K data wbar Fail o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
            (discAfter K.p data m s d o1) y' ≤ Cd + Z o1 := by
          unfold coefU sigRiskF
          rw [hlen, hCd]
          exact add_le_add (add_le_add le_rfl hcoin) (min_le_min le_rfl (hpoint o1 ho1 r hres y' budget hy'le))
        refine add_le_add (add_le_add ?_ ?_) ?_
        · refine le_trans (wsum_mono_g K (fun f => gA_mono _ hcoef f) o1.2) (le_of_eq ?_)
          unfold Ctx.wsum
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [Option.isSome_some, if_true]
          by_cases hr : Ctx.Recd s f
          · rw [if_pos ((hrecd f).2 hr), if_pos hr, mul_comm]
          · rw [if_neg (fun h => hr ((hrecd f).1 h)), if_neg hr]
        · unfold coinPotF
          rw [offSum_after K.tg K.initial model m budget s Ms L o1 ho1 r, hcoinPD]
          have hc : ((Nat.choose y' 2 : ℕ) : ℝ≥0∞) ≤ ((Nat.choose budget 2 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast Nat.choose_le_choose 2 hy'le
          gcongr
        · refine mul_le_mul_right ?_ _
          calc ∑ j ∈ Finset.range y', potNF K data wbar Fail o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m)
                (L ++ [⟨m, r⟩]) (discAfter K.p data m s d o1) j
              ≤ ∑ j ∈ Finset.range y', canon j o1 :=
                Finset.sum_le_sum fun j _ => hpoint o1 ho1 r hres j j le_rfl
            _ ≤ ∑ j ∈ Finset.range budget, canon j o1 :=
                Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hy'le)
  -- the expectation
  set EZ := ∑' o1, Pr[= o1 | run] * Z o1 with hEZ
  have hEZle : EZ ≤ min 1 (potNF K data wbar Fail s P Ms L d budget) :=
    le_trans (tsum_min_leF _ _) (min_le_min le_rfl (hse budget))
  have hcontact : ∀ f, ∑' o1, Pr[= o1 | run] *
      (if Ctx.Recd s f then (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0) else 0) ≤
      if Ctx.Recd s f then K.cw s f * gA R (revRate + nm + Cd + EZ) f else 0 := by
    intro f
    by_cases hr : Ctx.Recd s f
    · simp only [if_pos hr]
      exact sign_contact hMp hMi hMo hB hparse f Cd Z hZ1
    · simp only [if_neg hr, mul_zero, tsum_zero, le_refl]
  calc _ ≤ ∑' o1, Pr[= o1 | run] *
        ((∑ f, if Ctx.Recd s f then (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0)
          else 0) + coinPD + κ * ν * ∑ j ∈ Finset.range budget, canon j o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support run
        · exact mul_le_mul_right (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = (∑ f, ∑' o1, Pr[= o1 | run] *
          (if Ctx.Recd s f then (if o1.1.1.isSome then K.cw o1.2 f * gA (R ++ o1.1.2.1) (Cd + Z o1) f else 0)
            else 0)) + coinPD +
          κ * ν * ∑ j ∈ Finset.range budget, ∑' o1, Pr[= o1 | run] * canon j o1 := by
        simp only [mul_add, ENNReal.tsum_add, Finset.mul_sum]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ENNReal.tsum_mul_right, hmass, one_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun o1 => by ring
    _ ≤ (∑ f, if Ctx.Recd s f then K.cw s f * gA R (revRate + nm + Cd + EZ) f else 0) +
          coinPD + κ * ν * ∑ j ∈ Finset.range budget, potNF K data wbar Fail s P Ms L d j :=
        add_le_add (add_le_add (Finset.sum_le_sum fun f _ => hcontact f) le_rfl)
          (mul_le_mul_right (Finset.sum_le_sum fun j _ => hse j) _)
    _ ≤ psiCoreF K data wbar κ Fail s P Ms L d R budget := by
        unfold psiCoreF
        rw [if_neg (by omega)]
        have hXc : revRate + nm + Cd + EZ ≤ coefU K data wbar Fail s P Ms L d budget := by
          unfold coefU sigRiskF
          rw [hcoinsplit, hCd]
          have hn : ((signatureLimit - L.length : ℕ) : ℝ≥0∞) =
              ((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) + 1 := by
            rw [show signatureLimit - L.length = (signatureLimit - (L.length + 1)) + 1 by omega, Nat.cast_add,
              Nat.cast_one]
          rw [hn]
          calc revRate + nm + (((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) * revRate + coinD) + EZ
              = (((signatureLimit - (L.length + 1) : ℕ) : ℝ≥0∞) + 1) * revRate + (nm + coinD) + EZ := by ring
            _ ≤ _ := by gcongr
        have hcoinle : coinPD ≤ coinPotF K data s Ms L budget := by
          unfold coinPotF
          rw [offSum_split hM hm, hcoinPD]
          gcongr
          exact le_add_self
        gcongr
        · unfold Ctx.wsum
          refine Finset.sum_le_sum fun f _ => ?_
          split_ifs
          · rw [mul_comm]
            exact mul_le_mul_left (gA_mono R hXc f) _
          · exact le_rfl

end SignPays

end Sphincs.Security.ForsPotential
