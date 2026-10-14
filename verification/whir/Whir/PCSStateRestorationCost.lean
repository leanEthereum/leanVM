import Whir.PCSStateRestorationAdaptive

/-! Actual query counts and persistent metadata of the finite restoration game. -/
namespace Whir.PCSStateRestoration.Adaptive
open TypedOracleCompiler TypedFiatShamirGame

set_option autoImplicit false

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {Public : Type w} [DecidableEq Key]

/-- First-registration metadata survives the complete execution, even if retries
and restoration decisions depend on every answer in the completed public view. -/
theorem registry_execution_preserves (policy : Policy Key Answer Public) (n cursor : Nat)
    (view : View Key Answer Public) (wanted : Key) (publicData : Public)
    (registered : view.registry wanted = some publicData) (table : (key : Key) → Answer key) :
    (Sampling.eval table (program policy n cursor view)).registry wanted = some publicData := by
  induction n generalizing cursor view with
  | zero => exact registered
  | succ n ih =>
    cases chosen : policy.choose cursor view.history with
    | none =>
      simp only [program,chosen,Sampling.eval_pad]
      exact ih _ _ registered
    | some key =>
      simp only [program,chosen,Sampling.eval]
      exact ih _ _ (registry_never_overwrites policy cursor view key wanted _ publicData registered)

@[simp] theorem phases_adversary (Q : Nat) (adversary verifier : Policy Key Answer Public)
    (cursor : Nat) (history : History Key Answer Public) (before : cursor < Q) :
    (phases Q adversary verifier).choose cursor history = adversary.choose cursor history := by
  simp [phases,before]

@[simp] theorem phases_verifier (Q : Nat) (adversary verifier : Policy Key Answer Public)
    (cursor : Nat) (history : History Key Answer Public) :
    (phases Q adversary verifier).choose (Q+cursor) history = verifier.choose cursor history := by
  simp [phases]

/-- Total requests include repeated and abandoned requests and final verification.
Their deterministic operation bound is Q+k, not the number of fresh samples. -/
theorem requests_le {Q k : Nat} (adversary verifier : Policy Key Answer Public)
    (view : View Key Answer Public) (trace : List (Sigma Answer)) (result : View Key Answer Public)
    (run : Sampling.Runs (program (phases Q adversary verifier) (Q+k) 0 view) trace result) :
    trace.length ≤ Q+k := run.length_le

/-- In contrast, the memo-interpreter trace counts distinct fresh exposures only.
Fixed-prefix cache entries and repeated challenges allocate no additional draw. -/
theorem fresh_exposure_accounting {Q k : Nat} (adversary verifier : Policy Key Answer Public)
    (view : View Key Answer Public) (cache : Cache Key Answer) (trace : List (Sigma Answer))
    (result : View Key Answer Public × Cache Key Answer)
    (run : Sampling.Runs
      (RawOracleCoupling.memo (program (phases Q adversary verifier) (Q+k) 0 view) cache)
      trace result) :
    trace.length ≤ Q+k ∧ (trace.map Sigma.fst).Nodup ∧
      ∀ entry ∈ trace, cache entry.1 = none := by
  obtain ⟨fresh,distinct⟩ := PCSStateRestoration.memo_runs_distinct _ cache trace result run
  exact ⟨run.length_le,distinct,fresh⟩

#print axioms registry_execution_preserves
#print axioms fresh_exposure_accounting
end Whir.PCSStateRestoration.Adaptive
