import SphincsSecurity.Proof.Base.QueryCap
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}

theorem simulate_mem_support (impl : QueryImpl spec PMF) (computation : OracleComp spec Result)
    (result : Result) (hresult : result ∈ (simulateQ impl computation).support) : result ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
      exact (mem_support_pure_iff _ _).mpr hresult
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      refine (mem_support_bind_iff _ _ _).mpr ⟨answer, ?_, ih answer hresult⟩
      simp only [support_query, Set.mem_univ]

variable (selected : Index → Prop) [DecidablePred selected]

theorem counted_le_of_queryBound (computation : OracleComp spec Result) (budget : Nat)
    (hbound : computation.IsQueryBoundP selected budget) (result : Result × Nat)
    (hresult : result ∈ support (counted selected computation)) : result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      rw [counted_pure, mem_support_pure_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [counted_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [mem_support_bind_iff] at hresult
      obtain ⟨tail, htail, hresult⟩ := hresult
      rw [mem_support_pure_iff] at hresult
      subst result
      rw [isQueryBoundP_query_bind_iff] at hbound
      have htail := ih answer _ (hbound.2 answer) tail htail
      by_cases hselected : selected input
      · have hpos : 0 < budget := by simpa only [hselected, not_true_eq_false, false_or] using hbound.1
        simp only [if_pos hselected] at htail ⊢
        omega
      · simpa only [if_neg hselected, Nat.zero_add] using htail

theorem counted_writer_bind_le {Trace Next : Type} [Monoid Trace] (cost : Trace → Nat)
    (hcost : ∀ first second, cost (first * second) = cost first + cost second)
    (first : WriterT Trace (OracleComp spec) Result) (next : Result → WriterT Trace (OracleComp spec) Next)
    (hfirst : ∀ result ∈ support (counted selected first.run), result.2 ≤ cost result.1.2)
    (hnext : ∀ value result, result ∈ support (counted selected (next value).run) → result.2 ≤ cost result.1.2)
    (result : (Next × Trace) × Nat) (hresult : result ∈ support (counted selected (first >>= next).run)) :
    result.2 ≤ cost result.1.2 := by
  rw [WriterT.run_bind, counted_bind, mem_support_bind_iff] at hresult
  obtain ⟨middle, hmiddle, hresult⟩ := hresult
  rw [counted_map, mem_support_bind_iff] at hresult
  obtain ⟨last, hlast, hresult⟩ := hresult
  rw [support_map] at hlast
  obtain ⟨tail, htail, rfl⟩ := hlast
  rw [mem_support_pure_iff] at hresult
  subst result
  rw [hcost]
  exact Nat.add_le_add (hfirst middle hmiddle) (hnext middle.1.1 tail htail)

theorem counted_writer_simulate_le {SourceIndex Trace : Type} {source : OracleSpec SourceIndex} [Monoid Trace]
    (cost : Trace → Nat) (hcost : ∀ first second, cost (first * second) = cost first + cost second)
    (impl : QueryImpl source (WriterT Trace (OracleComp spec)))
    (hstep : ∀ input result, result ∈ support (counted selected (impl input).run) → result.2 ≤ cost result.1.2)
    (computation : OracleComp source Result) (result : (Result × Trace) × Nat)
    (hresult : result ∈ support (counted selected (simulateQ impl computation).run)) : result.2 ≤ cost result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, counted_pure, mem_support_pure_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query] at hresult
      exact counted_writer_bind_le selected cost hcost (impl input) (fun answer => simulateQ impl (next answer))
        (hstep input) ih result hresult

end SphincsSecurity.QueryCap
