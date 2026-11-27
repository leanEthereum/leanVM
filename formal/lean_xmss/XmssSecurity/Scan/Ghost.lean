module

public import XmssSecurity.Proof.CappedEncodingSourceImpl

@[expose] public section

/-!
# The adversary phase with a ghost query count

The traced handler `cappedCacheTracedMappedAdversaryImpl`, extended with a count of the
adversary's own hash queries (`impl`, `tick`), its steps through the source handler, and the cost
`overBudget` of a hash query made once the budget is spent. `OwnSecondLane` proves that cost zero
under the adversary's hash-query bound (`expectedSimulatedCost_overBudget`).
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
theorem impl_run_proj {α : Type _} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (cache : QueryCache HashSpec) :
    (fun r => (r.1, r.2.1.1)) <$> (simulateQ (impl publicKey secretKey) computation).run ((cache, []), 0) =
      (simulateQ romImpl (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        computation)).run cache := by
  rw [← CappedEncodingMonitor.cappedUnloggedMappedAdversary_simulateQ_run_eq_source,
    ← cappedCacheTracedMappedAdversaryImpl_cache_projection publicKey secretKey computation cache [],
    ← OracleComp.extendState_run_proj_eq (cappedCacheTracedMappedAdversaryImpl publicKey secretKey)
      (fun input _ _ _ k => tick input k) computation (cache, []) 0, Functor.map_map]
  rfl

theorem simulateQ_source_query_bind {α : Type _} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey)
        (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey input >>= fun r =>
        simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (next r) := by
  simp [simulateQ_bind]

/-- The cost of an adversary hash query made with the budget `Q` spent. -/
noncomputable def overBudget (Q : ℕ) (input : (OracleWorld + SigningSpec).Domain) (s : State) : ℝ≥0∞ :=
  if IsAdvHash input ∧ Q ≤ s.2 then ⊤ else 0

end XmssSecurity.Ghost
