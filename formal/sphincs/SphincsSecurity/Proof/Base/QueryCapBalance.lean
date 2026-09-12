import SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
  (selected : Index → Prop) [DecidablePred selected]

theorem counted_run_balance (computation : OracleComp spec Result) (budget : Nat)
    (result : Option (Result × Nat) × Nat) (hresult : result ∈ support (counted selected (run selected computation budget))) :
    result.2 + result.1.elim 0 Prod.snd = budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      simp only [run_pure, counted_pure, mem_support_pure_iff] at hresult
      subst result
      simp only [Option.elim_some, Nat.zero_add]
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : selected input
      · rw [if_pos hs] at hresult
        cases budget with
        | zero =>
            rw [counted_pure, mem_support_pure_iff] at hresult
            subst result
            rfl
        | succ budget =>
            rw [counted_query_bind, mem_support_bind_iff] at hresult
            obtain ⟨answer, _, hresult⟩ := hresult
            rw [mem_support_bind_iff] at hresult
            obtain ⟨tail, htail, hresult⟩ := hresult
            rw [mem_support_pure_iff] at hresult
            subst result
            have h := ih answer budget tail htail
            simp only [if_pos hs]
            omega
      · rw [if_neg hs, counted_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        rw [mem_support_bind_iff] at hresult
        obtain ⟨tail, htail, hresult⟩ := hresult
        rw [mem_support_pure_iff] at hresult
        subst result
        simpa only [if_neg hs, Nat.zero_add] using ih answer budget tail htail

theorem counted_next_bound (impl : QueryImpl spec PMF) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected (liftM (spec.query input) >>= next))).support, result.2 ≤ budget)
    (answer : spec.Range input) (hanswer : answer ∈ (impl input).support)
    (tail : Result × Nat) (htail : tail ∈ (simulateQ impl (counted selected (next answer))).support) :
    (if selected input then 1 else 0) + tail.2 ≤ budget := by
  apply hbound (tail.1, (if selected input then 1 else 0) + tail.2)
  simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨answer, hanswer, tail, htail, rfl⟩

end SphincsSecurity.QueryCap
