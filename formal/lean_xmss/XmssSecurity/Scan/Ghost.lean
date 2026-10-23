import XmssSecurity.Proof.CappedUnifiedExpectedDigest
import XmssSecurity.Proof.CappedEncodingGameTrace
import XmssSecurity.Scan.Frame

/-!
# The adversary phase with a ghost query count

The traced handler of `cappedCacheTracedMappedAdversaryImpl`, extended with a count of the
adversary's own hash queries. Under a hash-query bound the count never reaches the budget
(`expectedSimulatedCost_overBudget_eq_zero`), and the adversary's encoding queries are counted by the
source game (`expectedSimulatedCost_advEncoding_le`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Ghost

/-- A hash query of the adversary. -/
def IsAdvHash : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

noncomputable instance : DecidablePred IsAdvHash := Classical.decPred _

/-- An encoding query of the adversary. -/
def IsAdvEncoding (parameter : PublicParameter) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl input => CappedEncodingMonitor.IsEncodingHashQuery parameter input
  | .inr _ => False

noncomputable instance (parameter : PublicParameter) : DecidablePred (IsAdvEncoding parameter) :=
  Classical.decPred _

abbrev State := (QueryCache HashSpec × SigningCacheTrace) × ℕ

/-- The count after a query. -/
noncomputable def tick (input : (OracleWorld + SigningSpec).Domain) (k : ℕ) : ℕ :=
  if IsAdvHash input then k + 1 else k

/-- The traced handler with the ghost count of adversary hash queries. -/
noncomputable def impl (publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT State ProbComp) :=
  QueryImpl.extendState (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
    fun input _ _ _ k => tick input k

variable (publicKey : PublicKey) (secretKey : SecretKey)

theorem impl_run (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) :
    (impl publicKey secretKey input).run ((cache, trace), k) =
      (fun r => (r.1, ((r.2, signingCacheTraceUpdate input cache r.1 r.2 trace), tick input k))) <$>
        (simulateQ romImpl (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run
          cache := by
  rw [impl, QueryImpl.extendState_apply, cappedCacheTracedMappedAdversaryImpl,
    QueryImpl.extendState_apply, CappedEncodingMonitor.cappedUnloggedMappedAdversaryImpl_eq_source_compose]
  simp only [QueryImpl.apply_compose, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]

theorem source_world (input : OracleWorld.Domain) :
    cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inl input) =
      liftM (OracleWorld.query input) := rfl

theorem source_sign (request : SignRequest) :
    cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inr request) =
      Concrete.scheme.sign secretKey request.leafIndex request.message := rfl

theorem simulateQ_source_world (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey (.inl input))).run
      cache = (romImpl input).run cache := by
  rw [source_world]
  change (simulateQ romImpl (liftM (OracleWorld.query input) :
    OracleComp OracleWorld (OracleWorld.Range input))).run cache = _
  rw [simulateQ_spec_query]

theorem expect_world (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) (F : State → ℝ≥0∞) :
    ∑' r, Pr{let x ← (impl publicKey secretKey (.inl input)).run ((cache, trace), k)}[x = r] * F r.2 =
      ∑' r, Pr{let x ← (romImpl input).run cache}[x = r] * F ((r.2, trace), tick (.inl input) k) := by
  rw [impl_run, OracleComp.tsum_prEvent_map_mul, simulateQ_source_world]
  rfl

theorem expect_sign (request : SignRequest) (cache : QueryCache HashSpec)
    (trace : SigningCacheTrace) (k : ℕ) (F : State → ℝ≥0∞) :
    ∑' r, Pr{let x ← (impl publicKey secretKey (.inr request)).run ((cache, trace), k)}[x = r] * F r.2 =
      ∑' r, Pr{let x ← ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
          request.message)).run cache)}[x = r] *
        F ((r.2, trace ++ [⟨request, r.1, cache, r.2⟩]), k) := by
  rw [impl_run, OracleComp.tsum_prEvent_map_mul]
  simp [tick, IsAdvHash, signingCacheTraceUpdate, source_sign]

theorem mem_support_world {input : OracleWorld.Domain} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {k : ℕ} {r}
    (hr : r ∈ support ((impl publicKey secretKey (.inl input)).run ((cache, trace), k))) :
    ∃ r0 ∈ support ((romImpl input).run cache), r = (r0.1, ((r0.2, trace), tick (.inl input) k)) := by
  rw [impl_run, support_map, simulateQ_source_world] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  exact ⟨r0, hr0, rfl⟩

theorem mem_support_sign {request : SignRequest} {cache : QueryCache HashSpec}
    {trace : SigningCacheTrace} {k : ℕ} {r}
    (hr : r ∈ support ((impl publicKey secretKey (.inr request)).run ((cache, trace), k))) :
    ∃ r0 ∈ support ((simulateQ romImpl (Concrete.scheme.sign secretKey request.leafIndex
        request.message)).run cache),
      r = (r0.1, ((r0.2, trace ++ [⟨request, r0.1, cache, r0.2⟩]), k)) := by
  rw [impl_run, support_map] at hr
  obtain ⟨r0, hr0, rfl⟩ := hr
  exact ⟨r0, hr0, by simp [tick, IsAdvHash, signingCacheTraceUpdate]⟩

/-- Forgetting the count gives the source game's adversary run. -/
theorem impl_run_proj (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (fun r => (r.1, r.2.1.1)) <$> (simulateQ (impl publicKey secretKey) computation).run ((cache, []), 0) =
      (simulateQ romImpl (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation)).run cache := by
  rw [← CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source,
    ← cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey computation cache [],
    ← OracleComp.extendState_run_proj_eq (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      (fun input _ _ _ k => tick input k) computation (cache, []) 0, Functor.map_map]
  rfl

theorem simulateQ_source_query_bind (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input >>= fun r =>
        simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (next r) := by
  simp [simulateQ_bind]

/-- The cost of an adversary hash query made with the budget `Q` spent. -/
noncomputable def overBudget (Q : ℕ) (input : (OracleWorld + SigningSpec).Domain) (s : State) : ℝ≥0∞ :=
  if IsAdvHash input ∧ Q ≤ s.2 then ⊤ else 0

/-- **The budget is never exceeded.** -/
theorem expectedSimulatedCost_overBudget_eq_zero (Q : ℕ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      HashQueryBound (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation) cache (Q - k) → k ≤ Q →
      expectedSimulatedCost (impl publicKey secretKey) (overBudget Q) computation ((cache, trace), k) = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k hbound hk
      rw [simulateQ_source_query_bind] at hbound
      rw [expectedSimulatedCost_query_bind]
      cases input with
      | inl world =>
          have hb : HashQueryBound (liftM (OracleWorld.query world) >>= fun r =>
              simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (next r))
              cache (Q - k) := hbound
          obtain ⟨r1, hr1⟩ := probComp_support_nonempty ((romImpl world).run cache)
          have hfirst := (hashQueryBound_query_bind world _ cache (Q - k) hb r1 hr1).1
          have hcost : overBudget Q (.inl world) ((cache, trace), k) = 0 := by
            unfold overBudget
            rw [ite_eq_right]
            rintro ⟨hadv, hQ⟩
            cases world with
            | inl _ => exact hadv
            | inr _ => simp at hfirst; omega
          rw [hcost, zero_add]
          refine ENNReal.tsum_eq_zero.2 fun r => ?_
          by_cases hr : r ∈ support ((impl publicKey secretKey (.inl world)).run ((cache, trace), k))
          · obtain ⟨r0, hr0, rfl⟩ := mem_support_world publicKey secretKey hr
            have hnext := (hashQueryBound_query_bind world _ cache (Q - k) hb r0 hr0).2
            rw [ih r0.1 r0.2 trace _ _ _, mul_zero]
            · cases world with
              | inl _ => simpa [tick, IsAdvHash] using hnext
              | inr _ => simpa [tick, IsAdvHash, Nat.sub_sub] using hnext
            · cases world with
              | inl _ => simpa [tick, IsAdvHash] using hk
              | inr _ => simp at hfirst; simp [tick, IsAdvHash]; omega
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]
      | inr request =>
          have hcost : overBudget Q (.inr request) ((cache, trace), k) = 0 := by
            unfold overBudget; rw [ite_eq_right]; rintro ⟨hadv, _⟩; exact hadv
          rw [hcost, zero_add]
          refine ENNReal.tsum_eq_zero.2 fun r => ?_
          by_cases hr : r ∈ support ((impl publicKey secretKey (.inr request)).run ((cache, trace), k))
          · obtain ⟨r0, hr0, rfl⟩ := mem_support_sign publicKey secretKey hr
            rw [ih r0.1 r0.2 _ k (hashQueryBound_bind_right _ _ cache _ hbound r0 hr0) hk, mul_zero]
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]

theorem expectedSimulatedQueryCount_liftM_query (parameter : PublicParameter)
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery parameter)
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _) cache =
      if CappedEncodingMonitor.IsEncodingHashQuery parameter input then 1 else 0 := by
  rw [← bind_pure (liftM (OracleWorld.query input) : OracleComp OracleWorld _),
    expectedSimulatedQueryCount_query_bind]
  simp

/-- **The source game counts the adversary's encoding queries.** -/
theorem expectedSimulatedCost_advEncoding_le (parameter : PublicParameter)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      expectedSimulatedCost (impl publicKey secretKey)
          (fun input _ => if IsAdvEncoding parameter input then 1 else 0) computation ((cache, trace), k) ≤
        expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery parameter)
          (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k
      rw [expectedSimulatedCost_query_bind, simulateQ_source_query_bind, expectedSimulatedQueryCount_bind,
        impl_run, OracleComp.tsum_prEvent_map_mul]
      refine add_le_add ?_ (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih _ _ _ _) _)
      cases input with
      | inl world =>
          rw [source_world]
          refine le_trans ?_ (le_of_eq (expectedSimulatedQueryCount_liftM_query parameter world cache).symm)
          by_cases h : CappedEncodingMonitor.IsEncodingHashQuery parameter world
          · rw [ite_eq_left h]; exact le_of_eq_of_le (ite_eq_left (show IsAdvEncoding parameter (.inl world) from h)) le_rfl
          · rw [ite_eq_right (show ¬IsAdvEncoding parameter (.inl world) from h)]; exact zero_le
      | inr request =>
          rw [ite_eq_right (show ¬IsAdvEncoding parameter (.inr request) from id)]; exact zero_le

end XmssSecurity.Ghost
