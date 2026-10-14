import Whir.RawOracleCoupling

/-! Exact full-answer trace provenance for the actual global memo interpreter.
Cache hits retain the first allocation's complete answer, including hidden bytes.
The result concerns operational executions, not a supplied allocation certificate. -/
set_option autoImplicit false
namespace Whir.PCSBCSAtomicTrace
open TypedOracleCompiler TypedFiatShamirGame RawOracleCoupling

universe u v w
variable {Key : Type u} {Answer : Key → Type v} {R : Type w}
variable [DecidableEq Key]

/-- Every cached answer has its literal dependent key/value in the allocated trace. -/
def Recorded (cache : Cache Key Answer) (trace : List (Sigma Answer)) : Prop :=
  ∀ key answer, cache key = some answer → (⟨key,answer⟩ : Sigma Answer) ∈ trace

omit [DecidableEq Key] in
theorem empty_recorded : Recorded (Answer := Answer) (fun _ : Key => none) [] := by
  intro key answer hit
  cases hit

theorem insert_recorded {cache : Cache Key Answer} {before : List (Sigma Answer)}
    (recorded : Recorded cache before) (key : Key) (answer : Answer key) :
    Recorded (put cache key answer) (before ++ [⟨key,answer⟩]) := by
  intro other value hit
  by_cases same : other = key
  · subst other
    rw [put_self] at hit
    cases Option.some.inj hit
    exact List.mem_append_right _ (by simp)
  · rw [put_other _ _ _ _ same] at hit
    exact List.mem_append_left _ (recorded other value hit)

/-- Every branch, including replay and early abort, preserves literal provenance. -/
theorem memo_recorded {n : Nat} (program : Sampling Key Answer R n)
    (cache : Cache Key Answer) {before trace : List (Sigma Answer)}
    {result : R × Cache Key Answer} (recorded : Recorded cache before)
    (run : Sampling.Runs (memo program cache) trace result) :
    Recorded result.2 (before ++ trace) := by
  induction program generalizing cache before trace result with
  | ret value =>
    cases run
    simpa only [List.append_nil] using recorded
  | draw key next ih =>
    cases hit : cache key with
    | some answer =>
      simp only [memo, hit, Sampling.runs_pad] at run
      exact ih answer cache recorded run
    | none =>
      simp only [memo, hit] at run
      cases run with
      | draw answer rest =>
        have extended := ih answer (put cache key answer)
          (insert_recorded recorded key answer) rest
        simpa only [List.append_assoc, List.singleton_append] using extended

/-- A returned cached packet is found in the actual trace even when its last
use was only a replay. No per-block exposure or scalar-cache premise is needed. -/
theorem cached_answer_allocated {n : Nat} (program : Sampling Key Answer R n)
    {trace : List (Sigma Answer)} {result : R × Cache Key Answer}
    (run : Sampling.Runs (memo program (fun _ => none)) trace result)
    (key : Key) (answer : Answer key) (hit : result.2 key = some answer) :
    (⟨key,answer⟩ : Sigma Answer) ∈ trace := by
  have recorded := memo_recorded program (fun _ => none) empty_recorded run
  simpa only [List.nil_append] using recorded key answer hit

#print axioms memo_recorded
#print axioms cached_answer_allocated
end Whir.PCSBCSAtomicTrace
