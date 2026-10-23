/-
  LeanVM.Arithmetization.Completeness.Skeletons

  The skeletons of a run: one per step, the state stepped from and the instruction fetched there,
  and the number of rows each table gets from them.
-/

module

public import LeanVM.Semantics.Lemmas

@[expose] public section

/-!
# The skeletons of a run

A row of an arithmetization table is a state and the instruction fetched at it. `Skel` is that pair,
before any column is built from it: the witness of `Completeness.Witness` builds each table's rows
from the skeletons of its opcode. The skeletons of a run are its states stepped from, the final
state dropped (`Trace.runSkels`), and a table's rows are those of its opcode (`Skel.count`,
`Trace.runRows`). The witness has no other rows: the rows of a table past its count are the
protocol's padding rows, which are not on the bus (`doc/leanvm` §`sec:e2e-pad`).
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

/-- The skeleton of a table row: the program counter and frame pointer it is stepped from, and the
instruction fetched there. -/
structure Skel where
  /-- The program counter of the state. -/
  pc : K
  /-- The frame pointer of the state. -/
  fp : K
  /-- The instruction fetched at `pc`. -/
  ins : Instr

/-- The state a skeleton is stepped from. -/
def Skel.regs (s : Skel) : Regs K := ⟨s.pc, s.fp⟩

/-- The skeletons of the run: the states stepped from, the final state dropped, each with the
instruction fetched there. -/
noncomputable def Trace.runSkels {prog : Program} (t : Trace prog) : List Skel :=
  t.regs.dropLast.filterMap fun r ↦ (prog.fetch r.pc).map fun ins ↦ ⟨r.pc, r.fp, ins⟩

/-- The rows of table `op` among the skeletons: those whose instruction has its opcode. -/
def Skel.onTable (op : Opcode) (l : List Skel) : List Skel :=
  l.filter fun s ↦ s.ins.opcode = op

/-- The number of rows of table `op` among the skeletons. -/
def Skel.count (op : Opcode) (l : List Skel) : ℕ := (Skel.onTable op l).length

/-- The rows of opcode `op` in the run of `t`: the states stepped from, whose fetched instruction
has that opcode. The final state is not stepped from, so it is dropped. -/
noncomputable def Trace.runRows {prog : Program} (t : Trace prog) (op : Opcode) : ℕ :=
  (t.regs.dropLast.filter fun r ↦ (prog.fetch r.pc).map Instr.opcode = some op).length

/-- The run's skeletons on a table are the run's rows of it. -/
theorem Trace.count_runSkels {prog : Program} (t : Trace prog) (op : Opcode) :
    Skel.count op t.runSkels = t.runRows op := by
  unfold Skel.count Skel.onTable Trace.runSkels Trace.runRows
  generalize t.regs.dropLast = l
  induction l with
  | nil => rfl
  | cons r l ih =>
    cases hf : prog.fetch r.pc with
    | none => simpa [List.filterMap_cons, List.filter_cons, hf] using ih
    | some ins =>
      by_cases ho : ins.opcode = op <;> simp [hf, ho, ih]

/-- No table has more rows than the run has steps. -/
theorem Trace.runRows_le_steps {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    t.runRows op ≤ t.steps := by
  unfold Trace.runRows
  refine (List.length_filter_le _ _).trans ?_
  rw [List.length_dropLast, Trace.regs_length h]
  simp

/-- Along a run that succeeds, `runCount` counts the states stepped from whose fetched instruction
has opcode `op`. -/
theorem runCount_eq_length {κ : ℕ} {prog : Program} {L : MemImage κ} (op : Opcode) {n : ℕ}
    {r rf : Regs K} (h : run prog L n r = some rf) :
    runCount prog L op n r = (((List.range n).filterMap fun m ↦ run prog L m r).filter
      fun r₁ ↦ (prog.fetch r₁.pc).map Instr.opcode = some op).length := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    have hpc := pc_ne_finalPc_of_run_succ h
    rw [run_succ_of_ne hpc] at h
    obtain ⟨r', hs, hr'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ins, hf⟩ : ∃ ins, prog.fetch r.pc = some ins := by
      cases hf : prog.fetch r.pc with
      | none => rw [step_eq_none_of_fetch_eq_none hf] at hs; exact absurd hs (by simp)
      | some ins => exact ⟨ins, rfl⟩
    have htail : ((List.range n).map Nat.succ).filterMap (fun m ↦ run prog L m r) =
        (List.range n).filterMap fun m ↦ run prog L m r' := by
      rw [List.filterMap_map]
      congr 1
      funext m
      simp only [Function.comp, run_succ_of_ne hpc, hs, Option.bind_eq_bind, Option.bind_some]
    rw [List.range_succ_eq_map, List.filterMap_cons, run_zero, htail]
    simp only [runCount, hf, hs, ih hr']
    by_cases ho : ins.opcode = op <;> simp [hf, ho, Nat.add_comm]

/-- The instructions of an opcode an execution executes are the rows of its table. -/
theorem Trace.count_eq_runRows {prog : Program} {t : Trace prog} {rf : Regs K}
    (h : run prog t.image t.steps Regs.initial = some rf) (op : Opcode) :
    t.count op = t.runRows op := by
  unfold Trace.count Trace.runRows Trace.regs
  rw [List.range_succ, List.filterMap_append]
  simp only [List.filterMap_cons, List.filterMap_nil, h, List.dropLast_concat]
  exact runCount_eq_length op h

end LeanVM.Semantics

namespace LeanVM.Arithmetization

open LeanVM.Parameters

/-- The six opcode tables in the ensemble's order, the order of their bus codes. -/
def tableOpcodes : List Opcode := [.xor, .mulNative, .setConstant, .deref, .jump, .blake2s]

/-- Every opcode has a table. -/
theorem mem_tableOpcodes (o : Opcode) : o ∈ tableOpcodes := by
  cases o <;> decide

/-- The opcode of table `j`, in the ensemble's order. -/
def tableOpcode (j : Fin 6) : Opcode := tableOpcodes.getD j .xor

end LeanVM.Arithmetization
