import SphincsSecurity.Proof.Reference.FiniteHashWorld

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] hashInputs

def FixedHashQueryBound {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (q : Nat) : Prop :=
  ∀ result ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries computation)), result.2 ≤ q

theorem fixedHashWorld_congr {α : Type} (computation : OracleComp OracleWorld α)
    (first second : QueryImpl HashSpec Id) (h : ∀ input ∈ hashInputs computation, first input = second input) :
    simulateQ (fixedHashWorld first) computation = simulateQ (fixedHashWorld second) computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind input next ih =>
      have hnext := fun answer => ih answer (fun row hr => h row (hashInputs_next_subset input next answer hr))
      simp only [simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl input => exact bind_congr hnext
      | inr input => simp only [fixedHashWorld, h input (mem_hashInputs_hash_bind input next), pure_bind, hnext]

theorem fixedHashWorld_support_rom {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (result : α)
    (hresult : result ∈ support (simulateQ (fixedHashWorld oracle) computation)) :
    result ∈ support ((simulateQ romImpl computation).run' ∅) := by
  classical
  let inputs := hashInputs computation
  letI : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have heq := evalDist_romRun_eq_finiteHash computation inputs (Finset.Subset.refl _) ∅
  have hs : support ((simulateQ romImpl computation).run' ∅) =
      support (do
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) computation) := by
    ext value
    simp only [mem_support_iff, probOutput_def, heq]
  rw [hs, mem_support_bind_iff]
  refine ⟨(fun input => oracle input.val), by simp, ?_⟩
  rw [fixedHashWorld_congr computation (finiteHashAnswer ∅ inputs (fun input => oracle input.val)) oracle]
  · exact hresult
  · intro input hin
    simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, inputs, dif_pos hin]

theorem hashQueryBound_fixed {α : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (q : Nat) (hbound : HashQueryBound computation ∅ q) :
    FixedHashQueryBound oracle computation q := by
  intro result hresult
  exact hbound result (fixedHashWorld_support_rom oracle (countHashQueries computation) result hresult)

theorem fixedHashQueryBound_map_iff {α β : Type} (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (f : α → β) (q : Nat) :
    FixedHashQueryBound oracle (f <$> computation) q ↔ FixedHashQueryBound oracle computation q := by
  simp only [FixedHashQueryBound, countHashQueries_map, simulateQ_map, support_map, Set.forall_mem_image]

theorem fixedHashQueryBound_iff_of_map_eq {α β : Type} (oracle : QueryImpl HashSpec Id)
    {first : OracleComp OracleWorld α} {second : OracleComp OracleWorld β} {f : α → β}
    (heq : f <$> first = second) (q : Nat) :
    FixedHashQueryBound oracle first q ↔ FixedHashQueryBound oracle second q := by
  rw [← heq, fixedHashQueryBound_map_iff]

theorem fixedHashQueryBound_bind {α β : Type} (oracle : QueryImpl HashSpec Id)
    (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (q : Nat)
    (hbound : FixedHashQueryBound oracle (first >>= next) q) (result : α × Nat)
    (hresult : result ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries first))) :
    result.2 ≤ q ∧ FixedHashQueryBound oracle (next result.1) (q - result.2) := by
  simp only [FixedHashQueryBound, countHashQueries_bind, simulateQ_bind,
    bind_pure_comp, simulateQ_map] at hbound ⊢
  have hsum : ∀ tail ∈ support (simulateQ (fixedHashWorld oracle) (countHashQueries (next result.1))),
      result.2 + tail.2 ≤ q := by
    intro tail ht
    apply hbound (tail.1, result.2 + tail.2)
    rw [mem_support_bind_iff]
    refine ⟨result, hresult, ?_⟩
    rw [support_map]
    exact ⟨tail, ht, rfl⟩
  obtain ⟨tail, ht⟩ := probComp_support_nonempty (simulateQ (fixedHashWorld oracle) (countHashQueries (next result.1)))
  exact ⟨(Nat.le_add_right _ _).trans (hsum tail ht), fun tail ht => by have := hsum tail ht; omega⟩

theorem fixedHashQueryBound_query_bind {α : Type} (oracle : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α) (q : Nat)
    (hbound : FixedHashQueryBound oracle (liftM (OracleWorld.query input) >>= next) q)
    (answer : OracleWorld.Range input) (ha : answer ∈ support (fixedHashWorld oracle input)) :
    (if input matches .inr _ then 1 else 0) ≤ q ∧
      FixedHashQueryBound oracle (next answer) (q - (if input matches .inr _ then 1 else 0)) := by
  apply fixedHashQueryBound_bind oracle _ next q hbound (answer, if input matches .inr _ then 1 else 0)
  rw [← bind_pure (liftM (OracleWorld.query input)), countHashQueries_query_bind]
  simp only [countHashQueries_pure, map_pure, Nat.add_zero, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, support_map]
  exact ⟨answer, ha, by cases input <;> rfl⟩

theorem fixedBoundaryRun_count {α : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, result.2.hashCalls)) <$> fixedBoundaryRun parameter oracle computation =
      simulateQ (fixedHashWorld oracle) (countHashQueries computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [fixedBoundaryRun_pure, map_pure, countHashQueries_pure, simulateQ_pure]; rfl
  | query_bind input next ih =>
      simp only [fixedBoundaryRun, simulateQ_bind, WriterT.run_bind, simulateQ_spec_query,
        QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell,
        WriterT.run_map, map_pure, one_mul,
        bind_pure_comp, map_bind, bind_map_left, Functor.map_map]
      rw [countHashQueries_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, bind_pure_comp, simulateQ_map]
      apply bind_congr
      intro answer
      rw [← ih]
      simp only [fixedBoundaryRun, Functor.map_map, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq]
      cases input <;> rfl

theorem fixedBoundaryRun_bind_query_bound {α β : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β) (q : Nat)
    (hbound : FixedHashQueryBound oracle (computation >>= next) q)
    (result : α × SigningBoundaryTrace) (hresult : 𝒟[fixedBoundaryRun parameter oracle computation] result ≠ 0) :
    result.2.hashCalls ≤ q ∧ FixedHashQueryBound oracle (next result.1) (q - result.2.hashCalls) := by
  apply fixedHashQueryBound_bind oracle computation next q hbound (result.1, result.2.hashCalls)
  rw [← fixedBoundaryRun_count parameter oracle computation, support_map]
  exact ⟨result, (mem_support_iff _ _).mpr hresult, rfl⟩

end SphincsSecurity.Concrete
