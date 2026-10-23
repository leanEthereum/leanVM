/-
# Generalizations of VCVio's fork lemmas (upstream candidates)

Lemmas that belong upstream in VCVio: the focused-answer collision bound of
`OracleComp/Constructions/Fork/Basic.lean` generalized from the collision predicate
(`ans₁ = ans₂`, bounded by `1/|Range|`) to an arbitrary predicate on the first
completion's output and the second completion's focused answer, bounded by any
pointwise bound `δ` on the predicate against a fresh uniform query. The proof
is the same three steps: rewrite the fork as a second completion, drop the
guard, and apply `prEvent_answer_completeOccurrence` (which is already fully
general in the predicate).

`prEvent_le_prEvent_pure_of_forall_mem_support` bounds an event computation by
a pure event that every reachable outcome implies; the proofs use it where the
removed discrete API compared a computation with a `pure` Boolean.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import VCVio.CryptoFoundations.ReplayFork
import VCVio.OracleComp.Constructions.Fork.Basic

open OracleSpec ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The second focused answer of a located fork satisfies a predicate
parameterized by the (fixed) first output with probability at most any bound
`δ` that holds for the predicate against one fresh uniform query. Any
additional guard on the first output only tightens the event.

Generalizes `prEvent_focusCollision_fork_le_of_uniform` (recovered with
`Q x a := (firstAnswer = a)` and `δ := (Fintype.card (spec.Range i))⁻¹`). -/
theorem prEvent_focusPredicate_ofFreeM_fork_le [AnswerMeasure spec]
    {main : OracleComp spec α} {i : ι} {n : Nat} {path : PFunctor.FreeM.Path main}
    (located : PFunctor.FreeM.Cursor.Located i main path n) (accept : α → Prop)
    (Q : α → spec.Range i → Prop) {δ : ℝ≥0∞}
    (hQ : ∀ x : α, Pr{let ans ← (query i : OracleComp spec (spec.Range i))}[Q x ans] ≤ δ) :
    Pr{let view ← OracleComp.ofFreeM located.fork}[
      Q (PFunctor.FreeM.output main view.firstPath) view.secondAnswer ∧
        accept (PFunctor.FreeM.output main view.firstPath)] ≤ δ := by
  rw [PFunctor.FreeM.Cursor.Located.fork_eq_map_complete, ofFreeM_map, prEvent_map]
  refine (prEvent_mono _ _ _ fun _ h => h.1).trans ?_
  exact (prEvent_answer_completeOccurrence located.occurrence
    (fun a => Q (PFunctor.FreeM.output main located.completion.path) a)).trans_le (hQ _)

/-- An event computation is bounded by a pure event that every reachable
outcome implies. -/
theorem prEvent_le_prEvent_pure_of_forall_mem_support [AnswerMeasure spec]
    {mx : OracleComp spec Prop} {P : Prop} (h : ∀ p ∈ support mx, p → P) :
    prEvent mx ≤ prEvent (pure P : OracleComp spec Prop) := by
  classical
  by_cases hP : P
  · rw [prEvent_pure_prop]
    simp [hP]
  · have h0 := prEvent_eq_zero_of_forall_mem_support mx (fun p => p)
      (fun p hp hpP => hP (h p hp hpP))
    simp only [id_map'] at h0
    rw [h0]
    exact zero_le

end OracleComp
