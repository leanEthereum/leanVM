/-
  LeanVM.Prover.WitnessRun

  The executable run of a trace is its run: `stepsFrom` is `run` through the address indices,
  its steps are the run's skeletons, and `checkTrace` decides a valid execution within the
  committed-size cap.
-/

module

public import Statement.Prover.Columns
public import LeanVM.Arithmetization.Completeness.Theorem
public import LeanVM.Protocol.Extraction.Run
public import LeanVM.Protocol.EndToEnd.Front.LayoutStack
public import Statement.LeanVm

/-!
# The run of a trace

`stepsFrom_eq`: the run through the indices is `run`, its steps those of the states the run
passes through (`stepOf`). `runSteps_eq`: the run of a trace that ends in the final state gives the
steps of its first `t.steps` states, whose skeletons are the run's (`runSkels_eq_steps`), and
`opCount` counts them as `Execution.opcodeCount` does (`opCount_runSteps`). `checkTrace_iff`: the
check is a valid execution within the cap.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Extraction
open LeanVM.Protocol.Halting LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Front

@[expose] public section

variable {prog : LeanIsaProgram} {κ : ℕ}

/-- The skeleton of a step. -/
def Step.toSkel (st : Step) : Skel := ⟨st.pc, st.fp, st.ins⟩

/-- The step taken from the state `r`: its registers, the bytecode slot of its counter (`0` if
none) and the instruction fetched there (`skAt`'s default if none). -/
noncomputable def stepOf (prog : LeanIsaProgram) (r : Registers K) : Step :=
  ⟨r.pc, r.fp, ((addressIndex? prog.logSize r.pc).map Fin.val).getD 0,
    (prog.fetch r.pc).getD (.setConstant 0 0)⟩

/-- The run through the indices is `run`, the steps recorded those of the states it passes
through. -/
theorem stepsFrom_eq (hκ : κ < 64) (img : MemoryImage κ) :
    ∀ (n : ℕ) (r : Registers K) (acc : Array Step),
      stepsFrom (powIndex κ) (powIndex prog.logSize) prog (Vector.ofFn prog.instructions) img n
          r acc =
        (run prog img n r).map fun rf ↦
          (acc ++ ((List.range n).map fun k ↦
            stepOf prog ((run prog img k r).getD Registers.initial)).toArray, rf)
  | 0, r, acc => by simp [stepsFrom]
  | n + 1, r, acc => by
    by_cases hr : r = Registers.final prog
    · simp [stepsFrom, hr, run_succ_of_eq rfl]
    · rw [stepsFrom, ite_eq_right hr, run_succ_of_ne_final hr,
        gLogIn_powIndex (LeanVM.Protocol.Halting.logSize_lt prog)]
      have hread : readIn (powIndex κ) img = img.read := by
        funext a
        unfold readIn MemoryImage.read
        rw [gLogIn_powIndex hκ]
      cases hg : addressIndex? prog.logSize r.pc with
      | none =>
        simp [step, LeanIsaProgram.fetch, hg]
      | some i =>
        have hstep : step prog img r = execute img r (prog.instructions i) := by
          simp [step, LeanIsaProgram.fetch, hg]
        rw [hstep]
        have hci : (Vector.ofFn prog.instructions)[i] = prog.instructions i := by simp
        simp only [hread, hci]
        cases he : execute img r (prog.instructions i) with
        | none =>
          have he' : executeWith img.read r (prog.instructions i) = none := he
          simp [he']
        | some r' =>
          have he' : executeWith img.read r (prog.instructions i) = some r' := he
          simp only [he']
          rw [stepsFrom_eq hκ img n r' _]
          refine Option.map_congr fun rf _ ↦ ?_
          congr 1
          rw [List.range_succ_eq_map, List.map_cons, List.map_map]
          have h0 : stepOf prog ((run prog img 0 r).getD Registers.initial) =
              ⟨r.pc, r.fp, i.val, prog.instructions i⟩ := by
            simp [stepOf, hg, LeanIsaProgram.fetch]
          have hk : ∀ k, (run prog img (k + 1) r) = run prog img k r' := fun k ↦ by
            rw [run_succ_of_ne_final hr]
            simp [step, LeanIsaProgram.fetch, hg, execute, he']
          simp only [h0, Function.comp_def, hk]
          rw [List.toArray_cons, ← Array.append_assoc]
          rfl

/-- The steps of a trace: the steps taken from its first `t.steps` states. -/
noncomputable def traceSteps (t : Execution prog) : List Step :=
  (List.range t.stepCount).map fun k ↦ stepOf prog ((run prog t.memory k Registers.initial).getD
    Registers.initial)

/-- **The run of a trace** through the indices: its steps when it ends in the final state. -/
theorem runSteps_eq (t : Execution prog) (hκ : t.logMemorySize < 64) :
    runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t =
      if run prog t.memory t.stepCount Registers.initial = some (Registers.final prog) then
        some (traceSteps t).toArray
      else none := by
  unfold runSteps
  rw [stepsFrom_eq hκ]
  cases h : run prog t.memory t.stepCount Registers.initial with
  | none => simp
  | some rf =>
    by_cases hf : rf = Registers.final prog
    · subst hf; simp [traceSteps]
    · simp [hf]

/-- The skeletons of the steps of a valid run are the run's. -/
theorem runSkels_eq_steps {t : Execution prog}
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    (traceSteps t).map Step.toSkel = t.runSkels := by
  rw [runSkels_eq hv, traceSteps, List.map_map]
  rfl

/-- A step of a valid run: its slot is its counter's, it fetches its instruction there, and the
instruction executes. -/
def StepOk (prog : LeanIsaProgram) {κ : ℕ} (img : MemoryImage κ) (st : Step) : Prop :=
  ∃ h : st.slot < 2 ^ prog.logSize, st.pc = Parameters.addressOfIndex st.slot ∧
    prog.instructions ⟨st.slot, h⟩ = st.ins ∧ ∃ next, execute img st.toSkel.regs st.ins = some next

/-- Every step of a valid run is sound. -/
theorem stepOk_traceSteps {t : Execution prog}
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) :
    ∀ st ∈ traceSteps t, StepOk prog t.memory st := by
  intro st hst
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hst
  have hk' := List.mem_range.mp hk
  obtain ⟨ins, hf, hex⟩ := stateAt_exec hv hk'
  obtain ⟨i, hi, hci⟩ := (LeanIsaProgram.fetch_eq_some_iff prog).mp hf
  have hg : addressIndex? prog.logSize (stateAt t k).pc = some i :=
    (gLog?_spec (LeanVM.Protocol.Halting.logSize_lt prog)).mpr hi
  have hs : stateAt t k = (run prog t.memory k Registers.initial).getD Registers.initial := rfl
  rw [← hs]
  have hslot : (stepOf prog (stateAt t k)).slot = i := by simp [stepOf, hg]
  refine ⟨by rw [hslot]; exact i.isLt, ?_, ?_, ⟨stateAt t (k + 1), ?_⟩⟩
  · simpa [stepOf, hg] using hi
  · simp [stepOf, hg, hf, hci]
  · simpa [stepOf, Step.toSkel, Skel.regs, hf] using hex

/-- The counts of the steps of a valid run are `Execution.opcodeCount`. -/
theorem opCount_traceSteps {t : Execution prog}
    (hv : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)) (op :
        Opcode) :
    opCount (traceSteps t).toArray op = t.opcodeCount op := by
  rw [Execution.count_eq_runRows hv, ← Execution.count_runSkels, ← runSkels_eq_steps hv]
  unfold opCount Skel.count Skel.onTable
  rw [List.countP_toArray, List.countP_eq_length_filter, List.filter_map, List.length_map]
  rfl

/-- The executable committed size is `Execution.committedSize` at the trace's counts. -/
theorem committedSizeOf_eq (t : Execution prog) {count : Opcode → ℕ}
    (h : ∀ op, count op = t.opcodeCount op) :
    committedSizeOf prog.logSize t.logMemorySize count = t.committedSize := by
  simp only [committedSizeOf, Execution.committedSize, log2Ceil_eq_clog, h]

/-- **The check of a trace**: it has the public boundary of `input`, its run ends in the final
state, and its committed size is at most `2^28`; one run through the address indices. -/
def checkTrace (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) : Bool :=
  boundaryOK input t &&
    match runSteps (powIndex t.logMemorySize) (powIndex prog.logSize) prog t with
    | some steps =>
      decide (committedSizeOf prog.logSize t.logMemorySize (opCount steps) ≤ maxCommitted)
    | none => false

/-- **The check of a trace decides a valid execution within the cap.** -/
theorem checkTrace_iff (input : PublicInput) (t : Execution prog) :
    checkTrace prog input t = true ↔ ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 := by
  unfold checkTrace
  by_cases hb : boundaryOK input t = true
  · have hB := (boundaryOK_iff input t).mp hb
    have hκ : t.logMemorySize < 64 := by have := hB.2.1; unfold maxLogMem at this; omega
    rw [hb, Bool.true_and, runSteps_eq t hκ]
    by_cases hr : run prog t.memory t.stepCount Registers.initial = some (Registers.final prog)
    · rw [ite_eq_left hr]
      simp only [decide_eq_true_eq]
      rw [committedSizeOf_eq t (opCount_traceSteps hr)]
      exact ⟨fun h ↦ ⟨⟨hB, hr⟩, h⟩, fun h ↦ h.2⟩
    · rw [ite_eq_right hr]
      simp only [Bool.false_eq_true, false_iff, not_and]
      exact fun hv ↦ absurd hv.2 hr
  · simp only [Bool.not_eq_true] at hb
    rw [hb, Bool.false_and]
    simp only [Bool.false_eq_true, false_iff, not_and]
    exact fun hv ↦ absurd ((boundaryOK_iff input t).mpr hv.1) (by rw [hb]; simp)

end

end LeanVM.Prover
