import Sphincs.BridgeInterpSupport

/-! Replaying a recorded hash computation: once every answer of a lazily sampled run is cached,
the interpreter returns the same result. Applied to the prepared encoding searches, a failed
final assembly happens only at an index whose prepared search failed. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- A lazily sampled run only grows its cache. -/
theorem randomOracle_run_grows [DecidableEq D] {α : Type} (c : OracleComp (D →ₒ R) α) :
    ∀ (cache0 : QueryCache (D →ₒ R)), ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) c).run cache0),
      ∀ x v, cache0 x = some v → r.2 x = some v := by
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro cache0 r hr x v hx
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]; exact hx
  | query_bind t next ih =>
      intro cache0 r hr x v hx
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hr
      obtain ⟨a, ha, hr⟩ := Set.mem_iUnion₂.1 hr
      change a ∈ support ((randomOracle (spec := D →ₒ R) t).run cache0) at ha
      cases hc : cache0 t with
      | some u =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih u cache0 r hr x v hx
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
          obtain ⟨u, _, rfl⟩ := ha
          refine ih u _ r hr x v ?_
          by_cases hxt : x = t
          · subst hxt; rw [hc] at hx; cases hx
          · show (cache0.cacheQuery t u) x = some v
            rw [QueryCache.cacheQuery_of_ne _ _ hxt]; exact hx

omit [Fintype ι] in
/-- **Replay.** The interpreter returns the recorded result once all answers are cached. -/
theorem interp_liftHash_replay [DecidableEq D] {α : Type} (c : OracleComp (D →ₒ R) α)
    (hrow : c.IsQueryBoundP (fun x => model.parse x ≠ none) 0) :
    ∀ (cache0 : QueryCache (D →ₒ R)), ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) c).run cache0),
      ∀ budget (s : DebtState D R ι), (∀ x v, r.2 x = some v → s.cache x = some v) →
        ∀ out ∈ support (interp tg initial model (liftM c : OracleComp (SourceCostSpec D R ι) α) budget s),
          ∀ v, out.1.1 = some v → v = r.1 := by
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro cache0 r hr budget s _ out hout v hv
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [liftM_pure, interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hv
      cases hv
      rw [hr]
  | query_bind t next ih =>
      intro cache0 r hr budget s hcache out hout v hv
      rw [isQueryBoundP_query_bind_iff] at hrow
      have hparse : model.parse t = none := by
        rcases hrow.1 with h | h
        · exact Classical.not_not.mp h
        · exact absurd h (lt_irrefl 0)
      have hnext : ∀ u, (next u).IsQueryBoundP (fun x => model.parse x ≠ none) 0 := by
        intro u
        have := hrow.2 u
        split_ifs at this with hq
        · exact absurd hparse hq
        · exact this
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hr
      obtain ⟨a, ha, hr⟩ := Set.mem_iUnion₂.1 hr
      change a ∈ support ((randomOracle (spec := D →ₒ R) t).run cache0) at ha
      -- the answer and the cache after the query
      have hans : a.2 t = some a.1 := by
        cases hc : cache0 t with
        | some u =>
            rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
            subst ha; exact hc
        | none =>
            rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
            obtain ⟨u, _, rfl⟩ := ha
            simp
      have hst : s.cache t = some a.1 := hcache t a.1 (randomOracle_run_grows (next a.1) a.2 r hr t a.1 hans)
      rw [liftM_bind] at hout
      change out ∈ support (interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl t)))) >>= fun u => liftM (next u)) budget s) at hout
      rw [interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse] at hout
        simp only at hout
        rw [readOutside_cached t s a.1 hst, pure_bind, support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        exact ih a.1 (hnext a.1) a.2 r hr (budget - 1) s hcache o ho v hv
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hv
        cases hv

/-- Every part of a recorded sequence was recorded from some cache, inside the final cache. -/
theorem sequenceFin_parts [DecidableEq D] {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (D →ₒ R) α) (cache0 : QueryCache (D →ₒ R)),
      ∀ res ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (Concrete.sequenceFin f)).run cache0),
        ∀ i, ∃ c0, ∃ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (f i)).run c0),
          r.1 = res.1 i ∧ ∀ x v, r.2 x = some v → res.2 x = some v
  | 0, f, cache0, res, _, i => i.elim0
  | n + 1, f, cache0, res, hres, i => by
      unfold Concrete.sequenceFin at hres
      simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hres
      obtain ⟨h, hh, t, ht, rfl⟩ := hres
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨cache0, h, hh, rfl, fun x v hx => randomOracle_run_grows _ _ t ht x v hx⟩
      · obtain ⟨c0, r, hr, h1, h2⟩ := sequenceFin_parts (fun j : Fin n => f j.succ) h.2 t ht j
        exact ⟨c0, r, hr, h1, h2⟩

/-- A recorded run keeps the cache at inputs it never queries. -/
theorem randomOracle_run_avoid [DecidableEq D] {P : D → Prop} [DecidablePred P] {α : Type}
    (c : OracleComp (D →ₒ R) α) (h : c.IsQueryBoundP P 0) :
    ∀ (cache0 : QueryCache (D →ₒ R)), ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) c).run cache0),
      ∀ x, P x → r.2 x = cache0 x := by
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro cache0 r hr x _
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | query_bind t next ih =>
      intro cache0 r hr x hx
      rw [isQueryBoundP_query_bind_iff] at h
      have ht : ¬P t := by
        rcases h.1 with h1 | h1
        · exact h1
        · exact absurd h1 (lt_irrefl 0)
      have hnext : ∀ u, (next u).IsQueryBoundP P 0 := by
        intro u
        have := h.2 u
        simpa [ht] using this
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hr
      obtain ⟨a, ha, hr⟩ := Set.mem_iUnion₂.1 hr
      change a ∈ support ((randomOracle (spec := D →ₒ R) t).run cache0) at ha
      have hxt : x ≠ t := fun e => ht (e ▸ hx)
      cases hc : cache0 t with
      | some u =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih u (hnext u) cache0 r hr x hx
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
          obtain ⟨u, _, rfl⟩ := ha
          rw [ih u (hnext u) _ r hr x hx]
          show (cache0.cacheQuery t u) x = cache0 x
          rw [QueryCache.cacheQuery_of_ne _ _ hxt]

/-- One component of a recorded sequence fails with at most the bound of one run, provided an
invariant of the cache is kept by the other components. -/
theorem sequenceFin_prob [DecidableEq D] {α : Type} (Inv : QueryCache (D →ₒ R) → Prop) (bad : α → Prop)
    (B : ℝ≥0∞) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (D →ₒ R) α) (i : Fin n),
      (∀ j, j ≠ i → ∀ c, Inv c → ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (f j)).run c), Inv r.2) →
      (∀ c, Inv c → Pr[fun r => bad r.1 | (simulateQ (randomOracle (spec := D →ₒ R)) (f i)).run c] ≤ B) →
      ∀ c0, Inv c0 → Pr[fun res => bad (res.1 i) |
        (simulateQ (randomOracle (spec := D →ₒ R)) (Concrete.sequenceFin f)).run c0] ≤ B
  | 0, _, i, _, _, _, _ => i.elim0
  | n + 1, f, i, hkeep, hone, c0, hc0 => by
      unfold Concrete.sequenceFin
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rw [probEvent_bind_eq_tsum]
      refine Fin.cases ?_ (fun j => ?_) i hkeep hone
      · intro _ hone0
        calc _ ≤ ∑' a, Pr[= a | (simulateQ (randomOracle (spec := D →ₒ R)) (f 0)).run c0] *
              (if bad a.1 then 1 else 0) := by
              refine ENNReal.tsum_le_tsum fun a => mul_le_mul_right ?_ _
              split_ifs with hb
              · exact probEvent_le_one
              · refine le_of_eq (probEvent_eq_zero fun res hres hbad => hb ?_)
                rw [support_bind] at hres
                obtain ⟨t, _, ht⟩ := Set.mem_iUnion₂.1 hres
                rw [support_pure, Set.mem_singleton_iff] at ht
                rw [ht] at hbad
                exact hbad
          _ = Pr[fun r => bad r.1 | (simulateQ (randomOracle (spec := D →ₒ R)) (f 0)).run c0] := by
              rw [probEvent_eq_tsum_ite]
              refine tsum_congr fun a => ?_
              split_ifs <;> simp
          _ ≤ B := hone0 c0 hc0
      · intro hkeep' hone'
        calc _ ≤ ∑' a, Pr[= a | (simulateQ (randomOracle (spec := D →ₒ R)) (f 0)).run c0] * B := by
              refine ENNReal.tsum_le_tsum fun a => ?_
              by_cases ha : a ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (f 0)).run c0)
              · refine mul_le_mul_right ?_ _
                have hinv := hkeep' 0 (Fin.succ_ne_zero j).symm c0 hc0 a ha
                have h := sequenceFin_prob Inv bad B (fun j' : Fin n => f j'.succ) j
                  (fun j' hj' c hc r hr => hkeep' j'.succ (fun e => hj' (Fin.succ_injective _ e)) c hc r hr)
                  hone' a.2 hinv
                refine le_trans (le_of_eq ?_) h
                rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite]
                refine tsum_congr fun t => ?_
                rw [probEvent_pure]
                simp only [Fin.cases_succ]
                split_ifs <;> simp
              · rw [probOutput_eq_zero_of_not_mem_support ha, zero_mul, zero_mul]
          _ ≤ B := by
              rw [ENNReal.tsum_mul_right]
              exact mul_le_of_le_one_left' tsum_probOutput_le_one

end Sphincs.Security.HiddenDebt
