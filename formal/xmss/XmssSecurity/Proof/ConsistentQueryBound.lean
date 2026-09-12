import XmssSecurity.Proof.QueryCounting
import VCVio.OracleComp.QueryTracking.SubSpec
import XmssSecurity.Proof.IdealStatement

namespace XmssSecurity

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

noncomputable def countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  QueryCounting.counted (fun input : OracleWorld.Domain => input matches .inr _) computation

def HashQueryBound {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ romImpl (countHashQueries computation)).run' cache), result.2 ≤ q

theorem countHashQueries_pure {α : Type} (value : α) :
    countHashQueries (pure value) = pure (value, 0) := rfl

theorem countHashQueries_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    countHashQueries (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← countHashQueries (next answer)
      pure (result.1, (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) + result.2)) := rfl

theorem countHashQueries_bind {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) :
    countHashQueries (first >>= next) = (do
      let a ← countHashQueries first
      let b ← countHashQueries (next a.1)
      pure (b.1, a.2 + b.2)) :=
  QueryCounting.counted_bind (fun input : OracleWorld.Domain => input matches .inr _) first next

theorem countHashQueries_map {α β : Type} (first : OracleComp OracleWorld α) (f : α → β) :
    countHashQueries (f <$> first) = (fun result => (f result.1, result.2)) <$> countHashQueries first :=
  QueryCounting.counted_map (fun input : OracleWorld.Domain => input matches .inr _) first f

theorem probComp_support_nonempty {α : Type} (computation : ProbComp α) :
    (support computation).Nonempty := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨value, by simp⟩
  | query_bind input next ih =>
      obtain ⟨value, hv⟩ := ih default
      exact ⟨value, (mem_support_bind_iff _ _ _).mpr ⟨default, mem_support_query input default, hv⟩⟩

theorem hashQueryBound_iff_run {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound computation cache q ↔
      ∀ result ∈ support ((simulateQ romImpl (countHashQueries computation)).run cache), result.1.2 ≤ q := by
  simp only [HashQueryBound, StateT.run'_eq, support_map, Set.forall_mem_image]

theorem hashQueryBound_map_iff {α β : Type} (computation : OracleComp OracleWorld α)
    (f : α → β) (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound (f <$> computation) cache q ↔ HashQueryBound computation cache q := by
  simp only [HashQueryBound, countHashQueries_map, simulateQ_map, StateT.run'_eq,
    StateT.run_map, Functor.map_map, support_map, Set.forall_mem_image]

theorem hashQueryBound_iff_of_map_eq {α β : Type} {first : OracleComp OracleWorld α}
    {second : OracleComp OracleWorld β} {f : α → β} (heq : f <$> first = second)
    (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound first cache q ↔ HashQueryBound second cache q := by
  rw [← heq, hashQueryBound_map_iff]

theorem hashQueryBound_bind {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= next) cache q)
    (result : (α × Nat) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (countHashQueries first)).run cache)) :
    result.1.2 ≤ q ∧ HashQueryBound (next result.1.1) result.2 (q - result.1.2) := by
  rw [hashQueryBound_iff_run] at hbound ⊢
  simp only [countHashQueries_bind, simulateQ_bind, StateT.run_bind,
    bind_pure_comp, simulateQ_map, StateT.run_map] at hbound
  have hsum : ∀ tail ∈ support ((simulateQ romImpl (countHashQueries (next result.1.1))).run result.2),
      result.1.2 + tail.1.2 ≤ q := by
    intro tail htail
    apply hbound ((tail.1.1, result.1.2 + tail.1.2), tail.2)
    rw [mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [support_map]
    exact ⟨tail, htail, rfl⟩
  obtain ⟨tail, htail⟩ := probComp_support_nonempty
    ((simulateQ romImpl (countHashQueries (next result.1.1))).run result.2)
  exact ⟨(Nat.le_add_right _ _).trans (hsum tail htail), fun tail ht => by have := hsum tail ht; omega⟩

theorem countHashQueries_lift_prob {α : Type} (computation : ProbComp α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, countHashQueries_pure, map_pure]
  | query_bind input next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      rfl

theorem hashQueryBound_of_sampling_bind {α β : Type} (first : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound ((liftM first : OracleComp OracleWorld α) >>= next) cache q)
    (value : α) (hvalue : value ∈ support first) : HashQueryBound (next value) cache q := by
  have hrun : ((value, 0), cache) ∈
      support ((simulateQ romImpl (countHashQueries (liftM first : OracleComp OracleWorld α))).run cache) := by
    rw [countHashQueries_lift_prob, simulateQ_map, StateT.run_map, romImpl,
      QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run]
    simp only [Functor.map_map, support_map]
    exact ⟨value, hvalue, rfl⟩
  exact (hashQueryBound_bind _ next cache q hbound _ hrun).2

theorem simulateQ_countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ romImpl (countHashQueries computation) = (simulateQ countedRomImpl computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [countHashQueries_pure, simulateQ_pure, WriterT.run_pure]; rfl
  | query_bind input next ih =>
      simp only [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, ih, WriterT.run_bind]
      cases input <;> simp [countedRomImpl, QueryImpl.withAddCost, QueryImpl.withCost,
        QueryImpl.withTraceBefore_apply, WriterT.run_bind, WriterT.run_liftM,
        WriterT.run_tell, map_eq_bind_pure_comp, bind_assoc] <;>
        first | rfl | simp only [Function.comp_def, bind_pure]

theorem hasHashQueryBound_iff {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) :
    HasHashQueryBound scheme adversary q ↔ HashQueryBound (gameCore scheme adversary) ∅ q := by
  simp only [HasHashQueryBound, HashQueryBound, simulateQ_countHashQueries]
  rfl

theorem countHashQueries_forget {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countHashQueries computation = computation :=
  QueryCounting.counted_forget _ computation

theorem countHashQueries_run_forget {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ romImpl (countHashQueries computation)).run cache =
        (simulateQ romImpl computation).run cache := by
  have h := congrArg (fun c : OracleComp OracleWorld α => (simulateQ romImpl c).run cache)
    (countHashQueries_forget computation)
  simpa only [simulateQ_map, StateT.run_map] using h

theorem HashQueryBound.mono {α : Type} {computation : OracleComp OracleWorld α}
    {cache : QueryCache HashSpec} {q r : Nat} (hbound : HashQueryBound computation cache q)
    (hle : q ≤ r) : HashQueryBound computation cache r :=
  fun result hr => (hbound result hr).trans hle

theorem hashQueryBound_bind_run {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= next) cache q) (result : α × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl first).run cache)) :
    ∃ cost, cost ≤ q ∧ HashQueryBound (next result.1) result.2 (q - cost) := by
  rw [← countHashQueries_run_forget first cache, support_map] at hr
  obtain ⟨record, hrecord, rfl⟩ := hr
  exact ⟨record.1.2, hashQueryBound_bind first next cache q hbound record hrecord⟩

theorem hashQueryBound_bind_right {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= next) cache q) (result : α × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl first).run cache)) :
    HashQueryBound (next result.1) result.2 q := by
  obtain ⟨cost, _, hnext⟩ := hashQueryBound_bind_run first next cache q hbound result hr
  exact hnext.mono (Nat.sub_le _ _)

theorem hashQueryBound_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (liftM (OracleWorld.query input) >>= next) cache q)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hr : result ∈ support ((romImpl input).run cache)) :
    (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) ≤ q ∧
      HashQueryBound (next result.1) result.2 (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0)) := by
  apply hashQueryBound_bind _ next cache q hbound
    ((result.1, if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0), result.2)
  rw [← bind_pure (liftM (OracleWorld.query input)), countHashQueries_query_bind]
  simp only [countHashQueries_pure, map_pure, Nat.add_zero, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map]
  exact ⟨result, hr, by cases input <;> rfl⟩

end XmssSecurity
