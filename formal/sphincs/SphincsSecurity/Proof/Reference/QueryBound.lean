import SphincsSecurity.Proof.Base.QueryCap
import SphincsSecurity.Proof.IdealStatement

namespace SphincsSecurity

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

noncomputable def countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  QueryCap.counted (fun input : OracleWorld.Domain => input matches .inr _) computation

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
  QueryCap.counted_bind (fun input : OracleWorld.Domain => input matches .inr _) first next

theorem countHashQueries_map {α β : Type} (first : OracleComp OracleWorld α) (f : α → β) :
    countHashQueries (f <$> first) = (fun result => (f result.1, result.2)) <$> countHashQueries first :=
  QueryCap.counted_map (fun input : OracleWorld.Domain => input matches .inr _) first f

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

end SphincsSecurity
