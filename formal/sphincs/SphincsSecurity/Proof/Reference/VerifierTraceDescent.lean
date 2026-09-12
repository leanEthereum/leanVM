import SphincsSecurity.Proof.Ots.OtsChainBackward
namespace SphincsSecurity.Concrete.OtsContactTrace

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable

noncomputable def recordedCache (f : QueryImpl HashSpec Id) (trace : Trace) : QueryCache HashSpec :=
  fun input => if (input, f input) ∈ trace.toList then some (f input) else none

theorem recordedCache_ne_none (f : QueryImpl HashSpec Id) (trace : Trace) (input : HashInput) :
    recordedCache f trace input ≠ none ↔ (input, f input) ∈ trace.toList := by
  by_cases h : (input, f input) ∈ trace.toList <;> simp only [recordedCache, h, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]

theorem recordedCache_run_iff {Result : Type} (f : QueryImpl HashSpec Id) (trace : Trace) (computation : OracleComp HashSpec Result) :
    CachedRun (recordedCache f trace) f computation ↔ ContainsRun f trace computation := by
  simp only [CachedRun, ContainsRun, recordedCache_ne_none]

theorem ContainsRun.cached {Result : Type} {f : QueryImpl HashSpec Id} {trace : Trace} {computation : OracleComp HashSpec Result}
    (h : ContainsRun f trace computation) : CachedRun (recordedCache f trace) f computation :=
  (recordedCache_run_iff f trace computation).mpr h

end SphincsSecurity.Concrete.OtsContactTrace
