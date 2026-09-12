import SphincsSecurity.Proof.Base.QueryCapErasure
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (selected : Index → Prop) [DecidablePred selected]

theorem run_state_eq_counted (impl : QueryImpl spec (StateT Memory PMF))
    (computation : OracleComp spec Result) (budget : Nat) (memory : Memory) :
    ((simulateQ impl (run selected computation budget)).run memory).map Prod.fst =
      ((simulateQ impl (counted selected computation)).run memory).map (fun result => finish budget result.1) := by
  induction computation using OracleComp.inductionOn generalizing budget memory with
  | pure result =>
      simp only [run_pure, counted_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.map, PMF.pure_bind, Function.comp_def, finish, Nat.zero_le, if_true, Nat.sub_zero]
  | query_bind input next ih =>
      rw [run_query_bind, counted_query_bind]
      by_cases hs : selected input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map, PMF.bind_bind, PMF.pure_bind,
              Function.comp_def, finish, if_pos hs, Nat.add_comm 1, Nat.add_one_le_iff, Nat.not_lt_zero, if_false, PMF.bind_const]
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
              PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
            apply congrArg ((impl input).run memory).bind
            funext middle
            rw [ih middle.1 budget middle.2]
            simp only [PMF.map, PMF.pure_bind, Function.comp_def, finish, if_pos hs,
              Nat.add_comm 1, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
        apply congrArg ((impl input).run memory).bind
        funext middle
        rw [ih middle.1 budget middle.2]
        simp only [PMF.map, PMF.pure_bind, Function.comp_def, finish, Nat.zero_add]

theorem counted_state_le_of_cap_valid (impl : QueryImpl spec (StateT Memory PMF))
    (computation : OracleComp spec Result) (budget : Nat) (memory : Memory)
    (hvalid : ∀ result ∈ ((simulateQ impl (run selected computation budget)).run memory).support, result.1 ≠ none)
    (result : (Result × Nat) × Memory)
    (hresult : result ∈ ((simulateQ impl (counted selected computation)).run memory).support) : result.1.2 ≤ budget := by
  by_contra hlarge
  have hmap : finish budget result.1 ∈
      (((simulateQ impl (counted selected computation)).run memory).map (fun result => finish budget result.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [← run_state_eq_counted selected impl computation budget memory, PMF.mem_support_map_iff] at hmap
  obtain ⟨capped, hcapped, heq⟩ := hmap
  exact hvalid capped hcapped (heq.trans (if_neg hlarge))

end SphincsSecurity.QueryCap
