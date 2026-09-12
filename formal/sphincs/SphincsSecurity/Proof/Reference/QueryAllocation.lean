import SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}

noncomputable def recorded (computation : OracleComp spec Result) : OracleComp spec (Result × List Index) :=
  OracleComp.construct (fun result => pure (result, []))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, input :: result.2)) computation

theorem recorded_pure (result : Result) : recorded (pure result : OracleComp spec Result) = pure (result, []) := rfl

theorem recorded_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) :
    recorded (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← recorded (next answer)
      pure (result.1, input :: result.2)) := rfl

def calls (selected : Index → Prop) [DecidablePred selected] (inputs : List Index) : Nat :=
  inputs.countP (fun input => decide (selected input))

theorem calls_nil (selected : Index → Prop) [DecidablePred selected] : calls selected [] = 0 := rfl

theorem calls_cons (selected : Index → Prop) [DecidablePred selected] (input : Index) (inputs : List Index) :
    calls selected (input :: inputs) = (if selected input then 1 else 0) + calls selected inputs := by
  simp [calls, List.countP_cons, Nat.add_comm]

theorem recorded_counted (selected : Index → Prop) [DecidablePred selected] (computation : OracleComp spec Result) :
    (fun result => (result.1, calls selected result.2)) <$> recorded computation = counted selected computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [recorded_pure, counted_pure, map_pure, calls_nil]
  | query_bind input next ih =>
      simp only [recorded_query_bind, counted_query_bind, map_bind, map_pure, calls_cons]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_map_left]

theorem recorded_forget (computation : OracleComp spec Result) : Prod.fst <$> recorded computation = computation := by
  have h := congrArg (Functor.map Prod.fst) (recorded_counted (fun _ => True) computation)
  simpa only [Functor.map_map, counted_forget] using h

theorem calls_sum_le {Address : Type} (addresses : Finset Address)
    (selected : Address → Index → Prop) [∀ address, DecidablePred (selected address)]
    (total : Index → Prop) [DecidablePred total]
    (hdisjoint : ∀ input, (∑ address ∈ addresses, if selected address input then 1 else 0) ≤ if total input then 1 else 0)
    (inputs : List Index) : (∑ address ∈ addresses, calls (selected address) inputs) ≤ calls total inputs := by
  induction inputs with
  | nil => simp only [calls_nil, Finset.sum_const_zero, le_refl]
  | cons input inputs ih =>
      simp only [calls_cons, Finset.sum_add_distrib]
      exact Nat.add_le_add (hdisjoint input) ih

theorem recorded_calls_le (selected : Index → Prop) [DecidablePred selected]
    (computation : OracleComp spec Result) (cost : Result → Nat)
    (hcounted : ∀ result ∈ support (counted selected computation), result.2 ≤ cost result.1)
    (result : Result × List Index) (hresult : result ∈ support (recorded computation)) :
    calls selected result.2 ≤ cost result.1 := by
  apply hcounted (result.1, calls selected result.2)
  rw [← recorded_counted, support_map]
  exact ⟨result, hresult, rfl⟩

theorem counted_query (selected : Index → Prop) [DecidablePred selected] (input : spec.Domain) :
    counted selected (liftM (spec.query input) : OracleComp spec _) =
      (fun answer => (answer, if selected input then 1 else 0)) <$> (liftM (spec.query input) : OracleComp spec _) := by
  have h := counted_query_bind selected input (fun answer => pure answer)
  simpa only [bind_pure, counted_pure, pure_bind, Nat.add_zero, bind_pure_comp, map_pure] using h

theorem simulate_counted {Target : Type} {target : OracleSpec Target} {m : Type → Type} [Monad m] [LawfulMonad m]
    (selected : Index → Prop) [DecidablePred selected] (selectedTarget : Target → Prop) [DecidablePred selectedTarget]
    (handler : QueryImpl spec (OracleComp target)) (targetImpl : QueryImpl target m) (sourceImpl : QueryImpl spec m)
    (hhandler : ∀ input, simulateQ targetImpl (counted selectedTarget (handler input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$> sourceImpl input)
    (computation : OracleComp spec Result) :
    simulateQ targetImpl (counted selectedTarget (simulateQ handler computation)) =
      simulateQ sourceImpl (counted selected computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, counted_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, counted_bind, counted_query, simulateQ_pure,
        hhandler, bind_map_left, ih]

theorem simulate_oracle_mem_support {Target : Type} {target : OracleSpec Target}
    (handler : QueryImpl spec (OracleComp target)) (computation : OracleComp spec Result)
    (result : Result) (hresult : result ∈ support (simulateQ handler computation)) : result ∈ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using hresult
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [mem_support_bind_iff]
      exact ⟨answer, by simp only [support_query, Set.mem_univ], ih answer hresult⟩

end SphincsSecurity.QueryCap
