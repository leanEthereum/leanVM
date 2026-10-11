import Whir.WHIRSourceChronology
import Whir.PrunedMerkleProgram

namespace Whir.WHIRSourceChronology
open FiatShamirGame DuplexModeGame
open PublicMerkleProgram (Runs)

/-- Append a trusted continuation without replacing or inventing source events. -/
def Source.bind : Source cap R → (R → Source cap S) → Source cap S
  | .done value, next => next value
  | .ask query cont, next => .ask query (fun answer => (cont answer).bind next)
  | .commit root cont, next => .commit root (cont.bind next)
  | .claims profile entry request cont, next => .claims profile entry request (cont.bind next)

def Source.map (source : Source cap R) (f : R → S) : Source cap S :=
  source.bind (fun value => .done (f value))

theorem Source.erase_bind (source : Source cap R) (next : R → Source cap S) :
    erase (source.bind next) = WHIRModeFinal.bind (erase source) (fun value => erase (next value)) := by
  induction source with
  | done => rfl
  | ask query cont ih =>
    simp only [Source.bind,erase,WHIRModeFinal.bind]
    congr 1
    funext answer
    exact ih answer
  | commit root cont ih => exact ih
  | claims profile entry request cont ih => exact ih

theorem Source.counts_mono {source : Source cap R} {a b : Nat}
    (counted : Counts a source) (bound : a ≤ b) : Counts b source :=
  (erase_counted source b).mp (WHIRModeFinal.counts_mono ((erase_counted source a).mpr counted) bound)

theorem Source.bind_counted (source : Source cap R) (next : R → Source cap S) (a b : Nat)
    (before : Counts a source) (after : ∀ value, Counts b (next value)) : Counts (a+b) (source.bind next) := by
  apply (erase_counted _ _).mp
  rw [Source.erase_bind]
  exact WHIRModeFinal.bind_counted _ _ a b ((erase_counted _ _).mpr before)
    (fun value => (erase_counted _ _).mpr (after value))

theorem Source.bind_prefix_counted (source : Source cap R) (next : R → Source cap S) (budget : Nat)
    (counted : Counts budget (source.bind next)) : Counts budget source := by
  apply (erase_counted _ _).mp
  apply WHIRModeFinal.bind_prefix_counted (erase source) (fun value => erase (next value)) budget
  rw [← Source.erase_bind]
  exact (erase_counted _ _).mpr counted

/-- A real branch of a counted bind inherits the same upper bound for its
trusted continuation; no bound on unreachable result values is required. -/
theorem Source.bind_suffix_counted (source : Source cap R) (next : R → Source cap S)
    (budget : Nat) (trace : List Observation) (value : R)
    (run : Runs (erase source) trace value) (counted : Counts budget (source.bind next)) :
    Counts budget (next value) := by
  induction source generalizing budget trace with
  | done result =>
    cases run
    exact counted
  | ask query cont ih =>
    cases run with
    | ask answer later =>
      exact Source.counts_mono (ih answer (budget-query.cost) _ later (counted.2 answer))
        (Nat.sub_le budget query.cost)
  | commit root cont ih => exact ih budget trace run counted
  | claims profile entry request cont ih => exact ih budget trace run counted

theorem observations_append (before after : List (Event cap)) :
    observations (before ++ after) = observations before ++ observations after := by
  induction before with
  | nil => rfl
  | cons event rest ih => cases event <;> simp only [List.cons_append,observations,ih]

theorem Source.map_counted (source : Source cap R) (f : R → S) (budget : Nat) :
    Counts budget (source.map f) ↔ Counts budget source := by
  constructor
  · exact Source.bind_prefix_counted source _ budget
  · intro counted
    exact Source.bind_counted source (fun value => .done (f value)) budget 0 counted (fun _ => trivial)

/-- An arbitrary prefix can choose inputs, but a successful continuation must
execute as a genuine suffix of the same public observation trace. -/
theorem Source.erased_bind_runs (source : Source cap R) (next : R → Source cap S)
    (trace : List Observation) (result : S) :
    Runs (erase (source.bind next)) trace result ↔
      ∃ before value after, trace = before ++ after ∧
        Runs (erase source) before value ∧ Runs (erase (next value)) after result := by
  rw [Source.erase_bind]
  exact Runs.bind_iff _ _

/-- The successful real continuation is also a literal compiler-owned source
event segment, including commitment announcements and claim-read events. -/
theorem Source.real_bind (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (next : R → Source cap S) :
    (runReal C iv (compile (source.bind next))).view.result =
      let before := (runReal C iv (compile source)).view.result
      let after := (runReal C iv (compile (next before.value))).view.result
      ⟨after.value,before.events ++ after.events⟩ := by
  induction source with
  | done => rfl
  | ask query cont ih =>
    simpa only [Source.bind,compile,runReal,map_real,mapExecution,DuplexModeGame.prepend,prepend,List.cons_append]
      using congrArg (prepend (.answer query (realAnswer C iv query))) (ih (realAnswer C iv query))
  | commit root cont ih =>
    simpa only [Source.bind,compile,map_real,mapExecution,prepend,List.cons_append]
      using congrArg (prepend (.commit root)) ih
  | claims profile entry request cont ih =>
    simpa only [Source.bind,compile,map_real,mapExecution,prepend,List.cons_append]
      using congrArg (prepend (.claims profile entry request)) ih

theorem Source.erased_map_runs (source : Source cap R) (f : R → S)
    (trace : List Observation) (result : S) :
    Runs (erase (source.map f)) trace result ↔
      ∃ value, Runs (erase source) trace value ∧ f value = result := by
  rw [Source.map,Source.erased_bind_runs]
  constructor
  · rintro ⟨before,value,after,equal,first,last⟩
    cases last
    simp only [List.append_nil] at equal
    subst trace
    exact ⟨value,first,rfl⟩
  · rintro ⟨value,first,rfl⟩
    exact ⟨trace,value,[],by simp,first,.done _⟩

theorem Source.real_map (C : PrimitiveOracle) (iv : Digest32)
    (source : Source cap R) (f : R → S) :
    (runReal C iv (compile (source.map f))).view.result =
      let before := (runReal C iv (compile source)).view.result
      ⟨f before.value,before.events⟩ := by
  rw [Source.map,Source.real_bind]
  simp only [compile,runReal,List.append_nil]

end Whir.WHIRSourceChronology
