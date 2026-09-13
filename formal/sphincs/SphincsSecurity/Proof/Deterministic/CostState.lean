import SphincsSecurity.Proof.Deterministic.TrialSampling
import SphincsSecurity.Proof.Reference.QueryBound

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev CostState := QueryCache HashSpec × Nat

noncomputable def costHash : QueryImpl HashSpec (StateT CostState ProbComp) := fun input state => do
  let result ← (randomOracle input).run state.1
  return (result.1, result.2, state.2 + 1)

def queryCost (input : OracleWorld.Domain) : Nat := if input matches .inr _ then 1 else 0

theorem run_costQuery (input : OracleWorld.Domain) (cache : QueryCache HashSpec) (cost : Nat) :
    ((worldHandler costHash) input).run (cache, cost) =
      (fun result => (result.1, result.2, cost + queryCost input)) <$> (romImpl input).run cache := by
  cases input with
  | inl input => rfl
  | inr input =>
      change (do
        let result ← (randomOracle input).run cache
        pure (result.1, result.2, cost + 1)) = _
      rw [bind_pure_comp]
      rfl

theorem run_costWorld {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (cost : Nat) :
    (simulateQ (worldHandler costHash) computation).run (cache, cost) =
      (fun result => (result.1.1, result.2, cost + result.1.2)) <$>
        (simulateQ romImpl (countHashQueries computation)).run cache := by
  induction computation using OracleComp.inductionOn generalizing cache cost with
  | pure value => simp only [simulateQ_pure, countHashQueries_pure, StateT.run_pure, map_pure, Nat.add_zero]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countHashQueries_query_bind,
        simulateQ_pure, StateT.run_pure, map_bind, run_costQuery, bind_map_left]
      apply bind_congr
      intro result
      rw [ih]
      simp only [map_pure, bind_pure_comp, queryCost, Nat.add_assoc]
      rfl

theorem hashQueryBound_iff_costState {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat) :
    HashQueryBound computation cache q ↔
      ∀ result ∈ support ((simulateQ (worldHandler costHash) computation).run (cache, 0)), result.2.2 ≤ q := by
  rw [hashQueryBound_iff_run, run_costWorld]
  simp only [Nat.zero_add, support_map, Set.forall_mem_image]

end SphincsSecurity.Seeded
