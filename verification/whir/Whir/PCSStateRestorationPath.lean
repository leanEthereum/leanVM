import Whir.PCSStateRestorationCost

/-! Accepted-path restoration does not restrict arbitrary adversarial prequeries.
A final verifier path is ordered by source rounds, not by RO query time. Its
literal predecessor/after states must link, and each challenge node must be a
recorded first-capture certificate (including memoized repetitions). -/
namespace Whir.PCSStateRestoration.Adaptive
open TypedOracleCompiler TypedFiatShamirGame
open FiatShamirGame (average average_mono)

set_option autoImplicit false
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {Public : Type w}

/-- A finite source-round path through actually exposed certificate nodes.
Adjacency is literal equality of the previous after-state and next before-state.
The path need not follow query chronology: grinding can expose a child first. -/
inductive StatePath (cert : Certificate Key Answer Public) (history : History Key Answer Public) :
    Bool → Bool → Prop where
  | nil (state : Bool) : StatePath cert history state state
  | step (entry : Entry Key Answer Public) {final : Bool} (recorded : entry ∈ history)
      (rest : StatePath cert history (cert.after entry.1 entry.2.1 entry.2.2) final) :
      StatePath cert history (cert.before entry.1 entry.2.1) final

/-- A path starting in state zero and ending in state one necessarily contains
an actual zero-to-one transition, even with nonmonotone state restorations. -/
theorem path_has_transition (cert : Certificate Key Answer Public) (history : History Key Answer Public)
    (start finish : Bool) : StatePath cert history start finish → start = false → finish = true → Dirty cert history := by
  intro path
  induction path with
  | nil state =>
    intro initialState finalState
    have impossible : false = true := initialState.symm.trans finalState
    cases impossible
  | step entry member rest ih =>
    intro initialState finalState
    cases returned : cert.after entry.1 entry.2.1 entry.2.2 with
    | false => exact ih returned finalState
    | true => exact ⟨entry,member,initialState,returned⟩

section Probability
variable [DecidableEq Key] [Fintype Key]
variable [∀ key, Fintype (Answer key)] [∀ key, Nonempty (Answer key)]

/-- Accepted-path version of the fixed-prefix theorem. Unlike global `Causal`,
it allows every arbitrary adversarial key and hypothetical prefix; only the
successful final source-round path must connect initial zero to final one.
The local hazard and first-capture memo invariant, not a final bad probability,
derive the union bound. -/
theorem path_failure_probability (cert : Certificate Key Answer Public) (policy : Policy Key Answer Public)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard cert epsilon)
    (n cursor : Nat) (view : View Key Answer Public) (cache : Cache Key Answer)
    (recorded : Recorded view cache) (clean : ¬ Dirty cert view.history)
    (failure : View Key Answer Public → Prop)
    (acceptedPath : ∀ table : (key : Key) → Answer key,
      failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view)) →
      StatePath cert (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view)).history false true) :
    Soundness.uniformProb (Finset.univ.filter fun table : (key : Key) → Answer key =>
      failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))) ≤
      (n : ℚ)*epsilon := by
  classical
  have bound := memo_transition_bound cert policy epsilon nonnegative hazard n cursor view cache recorded clean
  have coupling := RawOracleCoupling.table_eq_memo (program policy n cursor view) cache
    (fun view => if Dirty cert view.history then (1 : ℚ) else 0)
  have tableBound := coupling.trans_le bound
  have covered : average (fun table : (key : Key) → Answer key =>
      if failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))
        then (1 : ℚ) else 0) ≤ (n : ℚ)*epsilon := by
    apply le_trans _ tableBound
    apply average_mono
    intro table
    by_cases bad : failure (Sampling.eval (RawOracleCoupling.overlay cache table) (program policy n cursor view))
    · have transition := path_has_transition cert _ false true (acceptedPath table bad) rfl rfl
      simp [bad,transition]
    · simp only [bad,↓reduceIte]; split <;> norm_num
  simpa only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero] using covered

/-- Main finite adaptive query theorem: Q adversarial hash-chain requests and
at most k final-verifier requests share one persistent memo cache and registry.
The only source-specific obligations are the conditional fresh-message hazard
and the literal accepted extraction-failure path from state zero to state one. -/
theorem accepted_path_failure_probability (cert : Certificate Key Answer Public)
    (adversary verifier : Policy Key Answer Public) (Q k : Nat)
    (epsilon : ℚ) (nonnegative : 0 ≤ epsilon) (hazard : ConditionalHazard cert epsilon)
    (failure : View Key Answer Public → Prop)
    (acceptedPath : ∀ table : (key : Key) → Answer key,
      failure (Sampling.eval table (program (phases Q adversary verifier) (Q+k) 0 initial)) →
      StatePath cert (Sampling.eval table (program (phases Q adversary verifier) (Q+k) 0 initial)).history false true) :
    Soundness.uniformProb (Finset.univ.filter fun table : (key : Key) → Answer key =>
      failure (Sampling.eval table (program (phases Q adversary verifier) (Q+k) 0 initial))) ≤
      ((Q+k : Nat) : ℚ)*epsilon := by
  exact path_failure_probability cert (phases Q adversary verifier) epsilon nonnegative hazard (Q+k) 0 initial
    (fun _ => none) (by intro key answer hit; cases hit) (by simp [initial,Dirty]) failure acceptedPath

end Probability

#print axioms path_has_transition
#print axioms path_failure_probability
#print axioms accepted_path_failure_probability
end Whir.PCSStateRestoration.Adaptive
