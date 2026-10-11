import Whir.WHIRSourceResolver
import Whir.WHIRSourceRawProgram
import Whir.WHIRSourceBackfill

namespace Whir.WHIRObservableSource
open FiatShamirGame DuplexModeGame TypedOracleCompiler
open RawOracleCoupling.Concrete WHIRCallerRegistry WHIRSourceChronology
open WHIRSourceResolver WHIRPublicBackfill

variable {cap : Nat} {R : Type}

/-- Only compiler-owned public events supply source answers. Completion-only observations cannot advance the source cutoff. -/
def answers (registry : Public) (Q : Nat) (result : Result cap R) : List (RawKey Q × Digest32) :=
  DuplexPublicSimulator.replayAnswers Q registry.iv [] (sourceView result).observations

structure Observed (registry : Public) (Q cap : Nat) where
  cache : PublicCache (context registry) Q
  labels : List (Sigma (fun label : WHIRCausalRawROM.Label (context registry) rfl Q cap =>
    WHIRCausalRawROM.Answer label))
  state : CausalBindingState.State cap

/-- Reconstruction consumes only the actual public source result and physical completion records. It has no source-program, private-coin, or total-oracle parameter. -/
noncomputable def observe (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (output : Completed (context registry) Q (Result cap R)) : Option (Observed registry Q cap) :=
  (WHIRObservableAllocations.observe (context registry) Q (answers registry Q output.result)
    (select output.result.value) output.records).map fun reconstructed =>
      let labeled := (WHIRCausalRawROM.decorator (context registry) rfl Q cap
        (publicResolver registry Q output.result)).traceRecode (CausalBindingState.empty cap) reconstructed.2
      ⟨reconstructed.1,labeled.1,labeled.2⟩

def selection (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    Option (View (Result cap R)) → Option (RawWHIRKeys.Packet (context registry) Q) :=
  fun result => result.bind (fun view => select view.result.value)

def rawProgram (registry : Public) (Q : Nat) (seed : DuplexPublicSimulator.Seed)
    (source : Source cap R) (counted : Counts Q source) (A : Nat) (sourceCounted : Counts A source) :=
  WHIRSourceRawProgram.bounded Q registry.iv ((DuplexPublicSimulator.simulator Q).initial seed)
    (compile source) Q (Nat.le_refl Q) ((compile_counted source Q).mpr counted)
    A ((compile_counted source A).mpr sourceCounted)

def execution (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source) :=
  runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
    ((DuplexPublicSimulator.simulator Q).initial seed) (compile source) Q (Nat.le_refl Q)
    ((compile_counted source Q).mpr counted)

theorem rawProgram_eval (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source) :
    Sampling.eval ro (rawProgram registry Q seed source counted A sourceCounted) =
      some (execution registry Q ro seed source counted).view :=
  WHIRSourceRawProgram.bounded_eval ..

theorem rawProgram_answers (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source) :
    WHIRObservableAllocations.rawAnswers Q ro (rawProgram registry Q seed source counted A sourceCounted) =
      answers registry Q (execution registry Q ro seed source counted).view.result := by
  unfold rawProgram
  rw [WHIRSourceRawProgram.bounded_rawAnswers]
  unfold answers execution
  rw [sourceView_ideal (DuplexPublicSimulator.simulator Q) ro registry.iv
    ((DuplexPublicSimulator.simulator Q).initial seed) source Q (Nat.le_refl Q) counted]
  rfl

def tableOutput (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    Completed (context registry) Q (Result cap R) :=
  let result := (execution registry Q ro seed source counted).view.result
  ⟨result,idealRecords (context registry) Q ro
    (selections (context registry) Q ((answers registry Q result).map Prod.fst) (select result.value))⟩

def allocationTrace (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :=
  (Sampling.execute (WHIRObservableAllocations.allocationOracle (context registry) Q ro)
    (RawOracleCoupling.Concrete.compile (context registry) Q (selection registry Q select)
      (rawProgram registry Q seed source counted A sourceCounted))).2

theorem allocationTrace_agrees (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    TraceAgrees registry Q ro (allocationTrace registry Q ro seed source counted A sourceCounted select) := by
  intro entry member
  exact (WHIRObservableAllocations.execute_answers _ _ entry member).symm

noncomputable def tableObservation (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) : Observed registry Q cap :=
  let result := tableExecution (context registry) Q (selection registry Q select)
    (rawProgram registry Q seed source counted A sourceCounted) ro
  let labeled := (WHIRCausalRawROM.decorator (context registry) rfl Q cap
    (privateResolver registry Q seed source counted)).traceRecode (CausalBindingState.empty cap)
      (allocationTrace registry Q ro seed source counted A sourceCounted select)
  ⟨result.2,labeled.1,labeled.2⟩

/-- Every reconstructed allocation answer, chronological binding label, and final immutable catalog equals the actual causal experiment. Cache coverage and consistency are consequences of executed physical completion, not hypotheses. -/
theorem observe_table (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    observe registry Q select (tableOutput registry Q ro seed source counted select) =
      some (tableObservation registry Q ro seed source counted A sourceCounted select) := by
  have reconstruction := WHIRObservableAllocations.observe_tableExecution (context registry) Q ro
    (selection registry Q select) (rawProgram registry Q seed source counted A sourceCounted)
  rw [rawProgram_answers,rawProgram_eval] at reconstruction
  simp only [selection,Option.bind_some] at reconstruction
  unfold observe tableOutput
  rw [reconstruction]
  simp only [Option.map_some]
  have recoding := traceRecode_actual registry Q ro seed source counted (CausalBindingState.empty cap)
    (by intro entry member; cases member)
    (allocationTrace registry Q ro seed source counted A sourceCounted select)
    (allocationTrace_agrees registry Q ro seed source counted A sourceCounted select)
  exact congrArg (fun labeled => some
    (⟨(tableExecution (context registry) Q (selection registry Q select)
      (rawProgram registry Q seed source counted A sourceCounted) ro).2,labeled.1,labeled.2⟩ :
      Observed registry Q cap)) recoding

theorem tableObservation_state (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    (tableObservation registry Q ro seed source counted A sourceCounted select).state =
      WHIRCausalRawROM.stateOfResult (context registry) rfl Q cap
        (privateResolver registry Q seed source counted) (CausalBindingState.empty cap)
        (selection registry Q select) (rawProgram registry Q seed source counted A sourceCounted)
        (tableExecution (context registry) Q (selection registry Q select)
          (rawProgram registry Q seed source counted A sourceCounted) ro) := by
  have run := Sampling.execute_runs (WHIRObservableAllocations.allocationOracle (context registry) Q ro)
    (RawOracleCoupling.Concrete.compile (context registry) Q (selection registry Q select)
      (rawProgram registry Q seed source counted A sourceCounted))
  rw [WHIRObservableAllocations.compile_cache] at run
  have reconstruction := compile_reconstruct (context registry) Q (selection registry Q select)
    (rawProgram registry Q seed source counted A sourceCounted) run
  unfold WHIRCausalRawROM.stateOfResult
  rw [reconstruction]
  rfl

/-- The physical wrapper returns exactly the original source result and the actual completion suffix records. -/
theorem ideal_output (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (whole : DuplexModeGame.Counts Q (WHIRSourceBackfill.instrument (context registry) Q source select)) :
    (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (WHIRSourceBackfill.instrument (context registry) Q source select) Q (Nat.le_refl Q) whole).view.result =
      tableOutput registry Q ro seed source counted select := by
  change (runIdeal (DuplexPublicSimulator.simulator Q) ro (context registry).iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (WHIRSourceBackfill.instrument (context registry) Q source select) Q (Nat.le_refl Q) whole).view.result = _
  rw [WHIRSourceBackfill.ideal_result (context registry) Q (DuplexPublicSimulator.simulator Q)
    ro ((DuplexPublicSimulator.simulator Q).initial seed) source select Q (Nat.le_refl Q) whole]
  have same : WHIRSourceBackfill.requests (context registry) Q
      (execution registry Q ro seed source counted).view.result =
      (answers registry Q (execution registry Q ro seed source counted).view.result).map Prod.fst :=
    (DuplexPublicSimulator.replayAnswers_keys Q registry.iv []
      (sourceView (execution registry Q ro seed source counted).view.result).observations).symm
  change (⟨(execution registry Q ro seed source counted).view.result,
    idealRecords (context registry) Q ro (selections (context registry) Q
      (WHIRSourceBackfill.requests (context registry) Q
        (execution registry Q ro seed source counted).view.result)
      (select (execution registry Q ro seed source counted).view.result.value))⟩ :
    Completed (context registry) Q (Result cap R)) = _
  rw [same]
  rfl

/-- Every label and catalog in the public observer is coupled to the actual causal game on the physically executed wrapper. -/
theorem observe_ideal (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (whole : DuplexModeGame.Counts Q (WHIRSourceBackfill.instrument (context registry) Q source select)) :
    observe registry Q select (runIdeal (DuplexPublicSimulator.simulator Q) ro registry.iv
      ((DuplexPublicSimulator.simulator Q).initial seed)
      (WHIRSourceBackfill.instrument (context registry) Q source select) Q (Nat.le_refl Q) whole).view.result =
      some (tableObservation registry Q ro seed source counted A sourceCounted select) := by
  rw [ideal_output registry Q ro seed source counted select whole]
  exact observe_table registry Q ro seed source counted A sourceCounted select

/-- This event is determined by the public completed view alone. Missing or malformed completion data is not replaced by invented raw answers. -/
def Failure (registry : Public) (Q : Nat)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q))
    (output : Completed (context registry) Q (Result cap R)) : Prop :=
  ∃ observed, observe registry Q select output = some observed ∧
    WHIRRawROM.Failure (context registry) rfl Q cap observed.state.catalog
      (CausalBindingState.roots observed.state) (select output.result.value) observed.cache

theorem failure_table_iff (registry : Public) (Q : Nat) (ro : RawKey Q → Digest32)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    Failure registry Q select (tableOutput registry Q ro seed source counted select) ↔
      WHIRRawROM.Failure (context registry) rfl Q cap
        (tableObservation registry Q ro seed source counted A sourceCounted select).state.catalog
        (CausalBindingState.roots
          (tableObservation registry Q ro seed source counted A sourceCounted select).state)
        (select (execution registry Q ro seed source counted).view.result.value)
        (tableObservation registry Q ro seed source counted A sourceCounted select).cache := by
  unfold Failure
  rw [observe_table registry Q ro seed source counted A sourceCounted select]
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨observed,equal,bad⟩
    cases equal
    exact bad
  · intro bad
    exact ⟨_,rfl,bad⟩

private instance : Finite UInt64 :=
  Finite.of_injective ByteCodec.encodeK ByteCodec.encodeK_injective
private noncomputable instance : Fintype UInt64 := Fintype.ofFinite _

open Classical in
/-- A public reconstructed-view event has the original causal ROM bound, for every fixed simulator seed. The raw allocation charge uses source budget A, not the larger physical key-domain bound Q. -/
theorem public_table_list_binding (registry : Public) (Q : Nat)
    (seed : DuplexPublicSimulator.Seed) (source : Source cap R) (counted : Counts Q source)
    (A : Nat) (sourceCounted : Counts A source)
    (select : R → Option (RawWHIRKeys.Packet (context registry) Q)) :
    average (fun ro : RawKey Q → Digest32 =>
      if Failure registry Q select (tableOutput registry Q ro seed source counted select) then 1 else 0) ≤
      min 1 (((allocationBudget (context registry) * (A+1) : Nat) : ℚ) * WHIRRawROM.epsilon cap) := by
  have bound := WHIRCausalRawROM.raw_table_list_binding (context registry) rfl Q cap
    (privateResolver registry Q seed source counted) (CausalBindingState.empty cap)
    (selection registry Q select) (rawProgram registry Q seed source counted A sourceCounted)
  convert bound using 1
  apply congrArg average
  funext ro
  rw [failure_table_iff registry Q ro seed source counted A sourceCounted select,
    tableObservation_state]
  have selected : selection registry Q select
      (tableExecution (context registry) Q (selection registry Q select)
        (rawProgram registry Q seed source counted A sourceCounted) ro).1 =
      select (execution registry Q ro seed source counted).view.result.value := by
    rw [tableExecution_result,rawProgram_eval]
    rfl
  rw [← selected]
  rfl

end Whir.WHIRObservableSource
