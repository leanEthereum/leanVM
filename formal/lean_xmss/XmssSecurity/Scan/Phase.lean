module

public import XmssSecurity.Scan.Ledger
public import XmssSecurity.Scan.MomentLift
public import XmssSecurity.Scan.Card

@[expose] public section

/-!
# The adversary phase, query by query

The four potentials on the ghost state and their one-query steps, for `Frame`'s `expectedFinal_le`
and `expectedFinal_ge`:
* `f1 = N² 1{PreBad} + N openΦ`, raised by `aCost` on a fresh encoding query at an unsigned leaf index;
* `f2 = hvSum`, raised by at least `landing · aCost`;
* `f3 = F3 (nCount, vCount, count)`, raised by `A` on the same queries, and `⊤` past the budget;
* `f4 = N² 1{PostBad}`, raised by `N` on an encoding query at a signed leaf index.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

open Partner

local notation "N" => ((2 ^ digestBits : ℕ) : ℝ≥0∞)

/-- A cost charged on hash queries only. -/
def onHash (g : HashInput → State → ℝ≥0∞) (input : (OracleWorld + SigningSpec).Domain) (s : State) :
    ℝ≥0∞ :=
  Sum.elim (Sum.elim (fun _ => 0) fun x => g x s) (fun _ => 0) input

@[simp] theorem onHash_hash (g : HashInput → State → ℝ≥0∞) (x : HashInput) (s : State) :
    onHash g (.inl (.inr x)) s = g x s := rfl

@[simp] theorem onHash_unif (g : HashInput → State → ℝ≥0∞) (n : ℕ) (s : State) :
    onHash g (.inl (.inl n)) s = 0 := rfl

@[simp] theorem onHash_sign (g : HashInput → State → ℝ≥0∞) (request : SignRequest) (s : State) :
    onHash g (.inr request) s = 0 := rfl

/-! ### The landing probability -/

/-- `landing` as a real number. -/
noncomputable def pReal : ℝ := landing.toReal

theorem landing_eq_ofReal : landing = ENNReal.ofReal pReal := (ENNReal.ofReal_toReal landing_ne_top).symm

theorem pReal_eq : pReal = (TargetSum.validDigests.card : ℝ) / 2 ^ 128 := by
  rw [pReal, landing, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]
  rfl

theorem pReal_ge : 1 / 2 ^ 21 ≤ pReal := by
  rw [pReal_eq, le_div_iff₀ (by positivity)]
  have : (2 : ℝ) ^ 107 ≤ TargetSum.validDigests.card := by exact_mod_cast TargetSum.two_pow_107_le_validDigests_card
  linarith

theorem pReal_le : pReal ≤ 1 / 2 ^ 20 := by
  rw [pReal_eq, div_le_iff₀ (by positivity)]
  have : (TargetSum.validDigests.card : ℝ) ≤ 2 ^ 108 := by exact_mod_cast TargetSum.validDigests_card_le_two_pow_108
  linarith

theorem pReal_pos : 0 < pReal := lt_of_lt_of_le (by positivity) pReal_ge

theorem pReal_le_one : pReal ≤ 1 := pReal_le.trans (by norm_num)

theorem one_sub_landing : 1 - landing = ENNReal.ofReal (1 - pReal) := by
  rw [landing_eq_ofReal, ENNReal.ofReal_sub _ pReal_pos.le, ENNReal.ofReal_one]

theorem landing_ne_zero : landing ≠ 0 := by
  rw [landing_eq_ofReal]; exact (ENNReal.ofReal_pos.mpr pReal_pos).ne'

/-! ### Expectations -/

theorem tsum_le_add_mul_probEvent {β : Type} (mx : ProbComp β) (g : β → ℝ≥0∞) (a b : ℝ≥0∞)
    (E : β → Prop) [DecidablePred E] (h : ∀ r ∈ support mx, g r ≤ a + b * if E r then 1 else 0) :
    ∑' r, Pr{let x ← mx}[x = r] * g r ≤ a + b * Pr{let x ← mx}[E x] := by
  calc ∑' r, Pr{let x ← mx}[x = r] * g r ≤ ∑' r, Pr{let x ← mx}[x = r] * (a + b * if E r then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support mx
        · exact mul_le_mul_right (h r hr) _
        · simp [(prEvent_eq_zero_of_not_mem_support _) hr]
    _ = (∑' r, Pr{let x ← mx}[x = r]) * a + b * Pr{let x ← mx}[E x] := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun r => ?_
        split_ifs <;> ring
    _ ≤ a + b * Pr{let x ← mx}[E x] := by
        gcongr
        calc (∑' r, Pr{let x ← mx}[x = r]) * a ≤ 1 * a := by gcongr; exact (OracleComp.tsum_prEvent_le_one _)
          _ = a := one_mul a

theorem tsum_le_of_support {β : Type} (mx : ProbComp β) (g : β → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ r ∈ support mx, g r ≤ a) : ∑' r, Pr{let x ← mx}[x = r] * g r ≤ a := by
  classical
  simpa using tsum_le_add_mul_probEvent mx g a 0 (fun _ => False) (fun r hr => by simpa using h r hr)

theorem tsum_eq_of_support {β : Type} (mx : ProbComp β) (g : β → ℝ≥0∞) (a : ℝ≥0∞)
    (h : ∀ r ∈ support mx, g r = a) : ∑' r, Pr{let x ← mx}[x = r] * g r = a :=
  OracleComp.tsum_prEvent_mul_of_const_on_support mx h

theorem W_ne_top (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (y : Position) : W cache parameter leafIndex y ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun _ _ => LoopWalk.reach_ne_top _ _ _ _

theorem Φ_ne_top (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex) :
    Φ cache parameter leafIndex ≠ ⊤ :=
  ENNReal.sum_ne_top.2 fun y _ => by split_ifs; exacts [W_ne_top _ _ _ y, ENNReal.zero_ne_top]

/-! ### `f1`: the pre-signing collision -/

variable (publicKey : PublicKey) (secretKey : SecretKey)

open Classical in
noncomputable def f1 (s : State) : ℝ≥0∞ :=
  N * N * (if PreBad secretKey s.1.2 then 1 else 0) + N * openΦ secretKey.parameter s.1.1 s.1.2

noncomputable def cost1 : (OracleWorld + SigningSpec).Domain → State → ℝ≥0∞ :=
  onHash fun x s => aCost secretKey.parameter x s.1.1 s.1.2

theorem f1_step (input : (OracleWorld + SigningSpec).Domain) (s : State) :
    ∑' r, Pr{let x ← (impl publicKey secretKey input).run s}[x = r] * f1 secretKey r.2 ≤
      f1 secretKey s + cost1 secretKey input s := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  cases input with
  | inl w =>
      rw [expect_world]
      cases w with
      | inl n =>
          rw [romImpl_expect_unif n cache (fun c => f1 secretKey ((c, trace), tick (.inl (.inl n)) k))]
          exact le_self_add
      | inr x =>
          cases hc : cache x with
          | some o =>
              rw [romImpl_expect_cached hc (fun c => f1 secretKey ((c, trace), tick (.inl (.inr x)) k))]
              exact le_self_add
          | none =>
              rw [romImpl_expect_fresh hc (fun c => f1 secretKey ((c, trace), tick (.inl (.inr x)) k))]
              unfold cost1
              rw [onHash_hash]
              unfold f1
              classical
              rw [ex_add, ex_const (N * N * (if PreBad secretKey trace then 1 else 0)), ex_const_mul, add_assoc]
              refine add_le_add le_rfl ((mul_le_mul' le_rfl (openΦ_fresh hc)).trans (le_of_eq ?_))
              have hN : N * (aCost secretKey.parameter x cache trace * N⁻¹) =
                  aCost secretKey.parameter x cache trace := by
                rw [mul_comm (aCost _ _ _ _), ← mul_assoc, N_mul_inv, one_mul]
              rw [mul_add, hN]
  | inr request =>
      rw [expect_sign]
      classical
      set e := request.leafIndex
      set U : ℝ≥0∞ := if Unsigned trace e then Φ cache secretKey.parameter e else 0
      have hU : U ≤ openΦ secretKey.parameter cache trace := by
        rw [openΦ]
        exact Finset.single_le_sum (f := fun e' => if Unsigned trace e' then Φ cache secretKey.parameter e' else 0)
          (fun _ _ => zero_le) (Finset.mem_univ e)
      have hUtop : U ≠ ⊤ := by unfold U; split_ifs; exacts [Φ_ne_top _ _ _, ENNReal.zero_ne_top]
      refine (tsum_le_add_mul_probEvent _ _
        (N * N * (if PreBad secretKey trace then 1 else 0) + N * (openΦ secretKey.parameter cache trace - U))
        (N * N * if Unsigned trace e then 1 else 0)
        (fun r => (⟨request, r.1, cache, r.2⟩ : SigningCacheEntry).CachedSelectionCollision secretKey cache)
        fun r hr => ?_).trans ?_
      · have hΦ : openΦ secretKey.parameter r.2 (trace ++ [⟨request, r.1, cache, r.2⟩]) =
            openΦ secretKey.parameter cache trace - U :=
          ENNReal.eq_sub_of_add_eq hUtop (openΦ_sign secretKey hr)
        unfold f1
        rw [hΦ, add_right_comm]
        refine add_le_add ?_ le_rfl
        rw [mul_assoc (N * N), ← mul_add]
        refine mul_le_mul' le_rfl ?_
        by_cases h1 : PreBad secretKey (trace ++ [⟨request, r.1, cache, r.2⟩])
        · rw [ite_eq_left h1]
          rcases preBad_sign secretKey h1 with h | ⟨h, h'⟩
          · rw [ite_eq_left h]; exact le_self_add
          · rw [ite_eq_left h, ite_eq_left h', mul_one]; exact le_add_self
        · rw [ite_eq_right h1]; exact zero_le
      · rw [add_assoc, f1, cost1, onHash_sign, add_zero]
        refine add_le_add le_rfl ?_
        calc N * (openΦ secretKey.parameter cache trace - U) +
              N * N * (if Unsigned trace e then 1 else 0) *
                Pr{let x ← (simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
                  request.message)).run cache}[(⟨request, x.1, cache, x.2⟩ :
                    SigningCacheEntry).CachedSelectionCollision secretKey cache] ≤
            N * (openΦ secretKey.parameter cache trace - U) + N * U := by
              refine add_le_add le_rfl ?_
              unfold U
              split_ifs
              · rw [mul_one, mul_assoc]
                refine mul_le_mul' le_rfl ((mul_le_mul' le_rfl (sign_collision_le secretKey e request.message
                  cache)).trans (le_of_eq ?_))
                rw [mul_comm, mul_assoc, mul_comm _ N, N_mul_inv, mul_one]
              · rw [mul_zero, mul_zero, zero_mul]
          _ = N * openΦ secretKey.parameter cache trace := by
              rw [← mul_add, tsub_add_cancel_of_le hU]

theorem aCost_cached {parameter : PublicParameter} {x : HashInput} {cache : QueryCache HashSpec}
    {o : HashOutput} (hc : cache x = some o) (trace : SigningCacheTrace) :
    aCost parameter x cache trace = 0 := by
  unfold aCost
  cases dec parameter x with
  | none => rfl
  | some p => rw [Option.elim_some, ite_eq_right fun h => by rw [hc] at h; exact Option.some_ne_none _ h.1]

theorem counts_fresh_le {parameter : PublicParameter} {x : HashInput} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} (hx : cache x = none) (u : HashOutput) :
    nCount parameter (cache.cacheQuery x u) trace ≤ nCount parameter cache trace + 1 := by
  cases hd : dec parameter x with
  | none =>
      rw [(counts_fresh_closed (fun p hp => by rw [hd] at hp; cases hp) u).1]; omega
  | some p =>
      obtain ⟨e, z⟩ := p
      have hxe := dec_eq_some parameter hd
      simp only at hxe
      subst hxe
      by_cases hu : Unsigned trace e
      · rw [(counts_fresh_open hx hu u).1]
      · rw [(counts_fresh_closed (fun p hp => by
          rw [dec_input, Option.some.injEq] at hp; subst hp; exact hu) u).1]; omega

theorem tick_world_hash (x : HashInput) (k : ℕ) : tick (.inl (.inr x)) k = k + 1 := by
  simp [tick, IsAdvHash]

theorem tick_world_unif (n : ℕ) (k : ℕ) : tick (.inl (.inl n)) k = k := by
  simp [tick, IsAdvHash]

/-! ### `f2`: the compensator -/

noncomputable def f2 (s : State) : ℝ≥0∞ := hvSum secretKey.parameter s.1.1 s.1.2

theorem f2_step (input : (OracleWorld + SigningSpec).Domain) (s : State) :
    f2 secretKey s + landing * cost1 secretKey input s ≤
      ∑' r, Pr{let x ← (impl publicKey secretKey input).run s}[x = r] * f2 secretKey r.2 := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  cases input with
  | inl w =>
      rw [expect_world]
      cases w with
      | inl n =>
          rw [romImpl_expect_unif n cache (fun c => f2 secretKey ((c, trace), tick (.inl (.inl n)) k)),
            cost1, onHash_unif, mul_zero, add_zero]
          exact le_rfl
      | inr x =>
          cases hc : cache x with
          | some o =>
              rw [romImpl_expect_cached hc (fun c => f2 secretKey ((c, trace), tick (.inl (.inr x)) k)),
                cost1, onHash_hash, aCost_cached hc, mul_zero, add_zero]
              exact le_rfl
          | none =>
              rw [romImpl_expect_fresh hc (fun c => f2 secretKey ((c, trace), tick (.inl (.inr x)) k)),
                cost1, onHash_hash]
              exact hvSum_fresh hc
  | inr request =>
      rw [expect_sign, cost1, onHash_sign, mul_zero, add_zero]
      exact le_of_eq (tsum_eq_of_support _ _ _ fun r hr => (counts_sign secretKey hr).2.2).symm

/-! ### `f3`: the moment of the landed count -/

variable (Q : ℕ)

noncomputable def f3 (s : State) : ℝ≥0∞ :=
  F3 pReal Q (nCount secretKey.parameter s.1.1 s.1.2) (vCount secretKey.parameter s.1.1 s.1.2) s.2

noncomputable def cost3 (input : (OracleWorld + SigningSpec).Domain) (s : State) : ℝ≥0∞ :=
  overBudget Q input s +
    ENNReal.ofReal (momentA pReal Q) * onHash (fun x s => openInd secretKey.parameter x s.1.1 s.1.2) input s

def Inv (s : State) : Prop := nCount secretKey.parameter s.1.1 s.1.2 ≤ s.2

theorem inv_step (input : (OracleWorld + SigningSpec).Domain) (s : State) (hs : Inv secretKey s)
    (r) (hr : r ∈ support ((impl publicKey secretKey input).run s)) : Inv secretKey r.2 := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  unfold Inv at hs ⊢
  cases input with
  | inl w =>
      obtain ⟨r0, hr0, rfl⟩ := mem_support_world publicKey secretKey hr
      cases w with
      | inl n =>
          rw [romImpl_support_unif hr0, tick_world_unif]
          exact hs
      | inr x =>
          rw [tick_world_hash]
          cases hc : cache x with
          | some o => rw [romImpl_support_cached hc hr0]; exact hs.trans (Nat.le_succ k)
          | none =>
              rw [romImpl_support_fresh hc hr0]
              exact (counts_fresh_le hc r0.1).trans (Nat.succ_le_succ hs)
  | inr request =>
      obtain ⟨r0, hr0, rfl⟩ := mem_support_sign publicKey secretKey hr
      rw [(counts_sign secretKey hr0).1]
      exact hs

theorem f3_step (hQ : Q ≤ 2 ^ 127) (input : (OracleWorld + SigningSpec).Domain) (s : State)
    (hs : Inv secretKey s) :
    ∑' r, Pr{let x ← (impl publicKey secretKey input).run s}[x = r] * f3 secretKey Q r.2 ≤
      f3 secretKey Q s + cost3 secretKey Q input s := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  unfold Inv at hs
  by_cases hover : IsAdvHash input ∧ Q ≤ k
  · rw [cost3, overBudget, ite_eq_left hover, top_add, add_top]
    exact le_top
  cases input with
  | inl w =>
      rw [expect_world]
      cases w with
      | inl n =>
          rw [romImpl_expect_unif n cache (fun c => f3 secretKey Q ((c, trace), tick (.inl (.inl n)) k)),
            tick_world_unif]
          exact le_self_add
      | inr x =>
          have hk : k < Q := by
            by_contra h
            exact hover ⟨trivial, by omega⟩
          cases hc : cache x with
          | some o =>
              rw [romImpl_expect_cached hc (fun c => f3 secretKey Q ((c, trace), tick (.inl (.inr x)) k)),
                tick_world_hash]
              exact le_add_right (F3_budget hk)
          | none =>
              rw [romImpl_expect_fresh hc (fun c => f3 secretKey Q ((c, trace), tick (.inl (.inr x)) k)),
                tick_world_hash]
              have hclosed : (∀ p, dec secretKey.parameter x = some p → ¬Unsigned trace p.1) →
                  (ex fun u : HashOutput => f3 secretKey Q ((cache.cacheQuery x u, trace), k + 1)) ≤
                    f3 secretKey Q ((cache, trace), k) + cost3 secretKey Q (.inl (.inr x)) ((cache, trace), k) := by
                intro h
                have hconst : ∀ u : HashOutput, f3 secretKey Q ((cache.cacheQuery x u, trace), k + 1) =
                    F3 pReal Q (nCount secretKey.parameter cache trace) (vCount secretKey.parameter cache trace)
                      (k + 1) := fun u => by
                  unfold f3
                  rw [(counts_fresh_closed h u).1, (counts_fresh_closed h u).2]
                rw [show (fun u : HashOutput => f3 secretKey Q ((cache.cacheQuery x u, trace), k + 1)) =
                  fun _ => F3 pReal Q (nCount secretKey.parameter cache trace)
                    (vCount secretKey.parameter cache trace) (k + 1) from funext hconst, ex_const]
                exact le_add_right (F3_budget hk)
              cases hd : dec secretKey.parameter x with
              | none => exact hclosed fun p hp => by rw [hd] at hp; cases hp
              | some p =>
                  obtain ⟨e, z⟩ := p
                  have hxe := dec_eq_some secretKey.parameter hd
                  simp only at hxe
                  subst hxe
                  by_cases hu : Unsigned trace e
                  · have hopen : ∀ u : HashOutput, f3 secretKey Q ((cache.cacheQuery
                        (input secretKey.parameter e z) u, trace), k + 1) =
                        (fun st : LoopWalk.St => F3 pReal Q (nCount secretKey.parameter cache trace + 1)
                          (vCount secretKey.parameter cache trace + if st = .hit then 1 else 0) (k + 1))
                          (outcome u) := fun u => by
                      unfold f3
                      rw [(counts_fresh_open hc hu u).1, (counts_fresh_open hc hu u).2]
                    rw [show (fun u : HashOutput => f3 secretKey Q ((cache.cacheQuery
                        (input secretKey.parameter e z) u, trace), k + 1)) = _ from funext hopen,
                      ex_outcome (fun st : LoopWalk.St => F3 pReal Q (nCount secretKey.parameter cache trace + 1)
                          (vCount secretKey.parameter cache trace + if st = .hit then 1 else 0) (k + 1)),
                      ite_eq_left (rfl : LoopWalk.St.hit = .hit),
                      ite_eq_right (show ¬LoopWalk.St.miss = .hit by decide), add_zero,
                      cost3, overBudget, ite_eq_right hover, zero_add, onHash_hash, openInd, hd, Option.elim_some,
                      ite_eq_left (show cache (input secretKey.parameter e z) = none ∧ Unsigned trace e from ⟨hc, hu⟩),
                      mul_one, one_sub_landing, landing_eq_ofReal]
                    exact F3_encoding pReal_ge pReal_le hQ hs hk
                  · exact hclosed fun p hp hup => by
                      rw [dec_input, Option.some.injEq] at hp
                      subst hp
                      exact hu hup
  | inr request =>
      rw [expect_sign]
      refine le_add_right (le_of_eq (tsum_eq_of_support _ _ _ fun r hr => ?_))
      unfold f3
      rw [(counts_sign secretKey hr).1, (counts_sign secretKey hr).2.1]

/-- **The mass bound.** -/
theorem landing_mul_hvSum_le (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) :
    landing * hvSum parameter cache trace ≤
      landing ^ 2 * F3 pReal Q (nCount parameter cache trace) (vCount parameter cache trace) k := by
  set n := nCount parameter cache trace
  set v := vCount parameter cache trace
  have h1 : landing * hvSum parameter cache trace ≤
      landing * ((∑ e, V (frozen cache trace e) parameter e * C (frozen cache trace e) parameter e : ℕ) : ℝ≥0∞) +
        (1 - landing) * ((∑ e, V (frozen cache trace e) parameter e * V (frozen cache trace e) parameter e : ℕ) :
          ℝ≥0∞) := by
    unfold hvSum
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun e _ => ?_
    calc landing * ((V (frozen cache trace e) parameter e : ℝ≥0∞) * H (frozen cache trace e) parameter e) =
          V (frozen cache trace e) parameter e * (landing * H (frozen cache trace e) parameter e) := by ring
      _ ≤ V (frozen cache trace e) parameter e * (landing * C (frozen cache trace e) parameter e +
            V (frozen cache trace e) parameter e * (1 - landing)) := mul_le_mul' le_rfl landing_mul_H_le
      _ = _ := by ring
  have hVC : (∑ e, V (frozen cache trace e) parameter e * C (frozen cache trace e) parameter e) ≤ v * n := by
    refine (Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left (V (frozen cache trace e) parameter e) ?_).trans
      (Finset.sum_mul _ _ _).symm.le
    exact Finset.single_le_sum (f := fun e => C (frozen cache trace e) parameter e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)
  have hVV : (∑ e, V (frozen cache trace e) parameter e * V (frozen cache trace e) parameter e) ≤ v * v := by
    refine (Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left (V (frozen cache trace e) parameter e) ?_).trans
      (Finset.sum_mul _ _ _).symm.le
    exact Finset.single_le_sum (f := fun e => V (frozen cache trace e) parameter e) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)
  refine h1.trans ?_
  calc landing * ((∑ e, V (frozen cache trace e) parameter e * C (frozen cache trace e) parameter e : ℕ) : ℝ≥0∞) +
        (1 - landing) * ((∑ e, V (frozen cache trace e) parameter e * V (frozen cache trace e) parameter e : ℕ) :
          ℝ≥0∞) ≤ landing * ((v * n : ℕ) : ℝ≥0∞) + (1 - landing) * ((v * v : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ENNReal.ofReal (pReal * v * n + (1 - pReal) * v ^ 2) := by
        rw [one_sub_landing, landing_eq_ofReal, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul pReal_pos.le, ← ENNReal.ofReal_mul (by linarith [pReal_le_one]),
          ← ENNReal.ofReal_add (mul_nonneg pReal_pos.le (Nat.cast_nonneg _))
            (mul_nonneg (by linarith [pReal_le_one]) (Nat.cast_nonneg _))]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal (pReal ^ 2) * F3 pReal Q n v k := ofReal_le_F3 pReal_pos pReal_le_one n v k
    _ = _ := by rw [landing_eq_ofReal, ENNReal.ofReal_pow pReal_pos.le]

/-! ### `f4`: the post-signing collision -/

noncomputable def worldSigned (parameter : PublicParameter) (trace : SigningCacheTrace) :
    OracleWorld.Domain → ℝ≥0∞
  | .inr x => signedInd parameter x trace
  | _ => 0

theorem worldSigned_inr (parameter : PublicParameter) (trace : SigningCacheTrace) (x : HashInput) :
    worldSigned parameter trace (.inr x) = signedInd parameter x trace := rfl

theorem worldSigned_inl (parameter : PublicParameter) (trace : SigningCacheTrace) (n : ℕ) :
    worldSigned parameter trace (.inl n) = 0 := rfl

theorem postPot_romImpl (parameter : PublicParameter) (trace : SigningCacheTrace) (w : OracleWorld.Domain)
    (cache : QueryCache HashSpec) :
    ∑' r, Pr{let x ← (romImpl w).run cache}[x = r] * postPot parameter trace r.2 ≤
      postPot parameter trace cache + worldSigned parameter trace w * N⁻¹ := by
  cases w with
  | inl n =>
      rw [romImpl_expect_unif n cache (postPot parameter trace)]
      exact le_self_add
  | inr x =>
      cases hc : cache x with
      | some o =>
          rw [romImpl_expect_cached hc (postPot parameter trace)]
          exact le_self_add
      | none =>
          rw [romImpl_expect_fresh hc (postPot parameter trace), worldSigned_inr]
          exact postPot_fresh hc

theorem worldSigned_le (parameter : PublicParameter) (trace : SigningCacheTrace) (w : OracleWorld.Domain) :
    worldSigned parameter trace w ≤ if CappedEncodingMonitor.IsEncodingHashQuery parameter w then 1 else 0 := by
  cases w with
  | inl n => exact zero_le
  | inr x =>
      rw [worldSigned_inr]
      unfold signedInd
      cases hd : dec parameter x with
      | none => exact zero_le
      | some p =>
          have hx := dec_eq_some parameter hd
          have henc : CappedEncodingMonitor.IsEncodingHashQuery parameter (.inr x) := by
            have h := encodingInputLeafIndex?_encodingInput parameter p.1 p.2
            have h' : encodingInputLeafIndex? parameter x = some p.1 := by rw [hx]; exact h
            rw [CappedEncodingMonitor.IsEncodingHashQuery_inr, h']
            rfl
          rw [ite_eq_left henc, Option.elim_some]
          split_ifs
          · exact zero_le
          · exact le_rfl

theorem N_mul_N_mul_inv (a : ℝ≥0∞) : N * N * (a * N⁻¹) = N * a := by
  rw [mul_comm a, mul_assoc, ← mul_assoc N N⁻¹ a, N_mul_inv, one_mul]

noncomputable def f4 (s : State) : ℝ≥0∞ := N * N * postPot secretKey.parameter s.1.2 s.1.1

noncomputable def cost4 (input : (OracleWorld + SigningSpec).Domain) (s : State) : ℝ≥0∞ :=
  N * onHash (fun x s => signedInd secretKey.parameter x s.1.2) input s

theorem f4_step (input : (OracleWorld + SigningSpec).Domain) (s : State) :
    ∑' r, Pr{let x ← (impl publicKey secretKey input).run s}[x = r] * f4 secretKey r.2 ≤
      f4 secretKey s + cost4 secretKey input s := by
  obtain ⟨⟨cache, trace⟩, k⟩ := s
  cases input with
  | inl w =>
      rw [expect_world]
      calc _ = N * N * ∑' r, Pr{let x ← (romImpl w).run cache}[x = r] * postPot secretKey.parameter trace r.2 := by
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun r => ?_
            rw [mul_left_comm]
            rfl
        _ ≤ N * N * (postPot secretKey.parameter trace cache + worldSigned secretKey.parameter trace w * N⁻¹) :=
            mul_le_mul' le_rfl (postPot_romImpl _ _ _ _)
        _ = f4 secretKey ((cache, trace), k) + cost4 secretKey (.inl w) ((cache, trace), k) := by
            rw [mul_add, N_mul_N_mul_inv, f4, cost4]
            cases w with
            | inl n => rw [worldSigned_inl, onHash_unif]
            | inr x => rw [worldSigned_inr, onHash_hash]
  | inr request =>
      rw [expect_sign, cost4, onHash_sign, mul_zero, add_zero]
      refine tsum_le_of_support _ _ _ fun r hr => ?_
      exact mul_le_mul' le_rfl (postPot_sign secretKey hr)

end XmssSecurity.Ghost
