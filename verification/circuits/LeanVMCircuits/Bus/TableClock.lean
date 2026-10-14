module

public import LeanVMCircuits.ClockExport
public import LeanVMCircuits.Bus.Tables

@[expose] public section

/-!
# The instruction tables with their clock circuits

Every instruction table's clock circuit is one of the five exported artifacts of `LeanVMCircuits.ClockExport`, picked
by its slot list (`clockArtifact`), and any assignment satisfying its rows spells ports with `Clock.Holds`
(`clock_sound`). So `tables_correct` holds with `TableRow.Valid` replaced by the clock circuit itself being satisfied,
its ports bound to the clock, previous-timestamp and step columns (`tables_correct_of_clock`).
-/

namespace LeanVMCircuits.Bus.ClassTable

open LeanVMCircuits LeanVMCircuits.Flock LeanVMCircuits.Rec

/-- A table's exported clock circuit, by its slot list. -/
def clockArtifact (s : Spec) : Artifact :=
  if s.slots = [0, 1, 3] then Flock.Clock.Registers.artifact
  else if s.slots = [0, 3, 2] then Flock.Clock.Load.artifact
  else if s.slots = [0, 1, 2] then Flock.Clock.Store.artifact
  else if s.slots = List.range 18 then Flock.Clock.Hash.artifact
  else Flock.Clock.Ext.artifact

theorem clockArtifact_registers {s : Spec} (h : s.slots = [0, 1, 3]) :
    clockArtifact s = Flock.Clock.Registers.artifact := by
  unfold clockArtifact
  rw [if_pos h]

theorem clockArtifact_load {s : Spec} (h : s.slots = [0, 3, 2]) : clockArtifact s = Flock.Clock.Load.artifact := by
  unfold clockArtifact
  rw [if_neg (by rw [h]; decide), if_pos h]

theorem clockArtifact_store {s : Spec} (h : s.slots = [0, 1, 2]) : clockArtifact s = Flock.Clock.Store.artifact := by
  unfold clockArtifact
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem clockArtifact_hash {s : Spec} (h : s.slots = List.range 18) :
    clockArtifact s = Flock.Clock.Hash.artifact := by
  unfold clockArtifact
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_pos h]

theorem clockArtifact_ext {s : Spec} (h : s.slots = [0, 1, 3] ++ List.range' 4 9) :
    clockArtifact s = Flock.Clock.Ext.artifact := by
  unfold clockArtifact
  rw [if_neg (by rw [h]; decide), if_neg (by rw [h]; decide), if_neg (by rw [h]; decide),
    if_neg (by rw [h]; decide)]

/-- Every instruction table's clock circuit, satisfied, spells ports with `Clock.Holds` on the table's slots. -/
theorem clock_sound {s : Spec} (hs : s ∈ all) (env : Environment Bit)
    (hrows : (clockArtifact s).rows.Forall (Row.Holds env.get)) :
    LeanVMCircuits.Clock.Holds s.slots (Flock.Clock.prevNums s.slots.length env.get) (Flock.Clock.tsNum env.get)
      (Flock.Clock.stepNum (clockArtifact s) env.get) := by
  have mem := List.mem_map_of_mem (f := Spec.slots) hs
  rw [all_slots] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (rw [clockArtifact_registers h] at hrows ⊢; rw [h]; exact Flock.Clock.Registers.soundness env hrows)
    | (rw [clockArtifact_load h] at hrows ⊢; rw [h]; exact Flock.Clock.Load.soundness env hrows)
    | (rw [clockArtifact_store h] at hrows ⊢; rw [h]; exact Flock.Clock.Store.soundness env hrows)
    | (rw [clockArtifact_hash h] at hrows ⊢; rw [h, show List.range 18 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
        13, 14, 15, 16, 17] from rfl]; exact Flock.Clock.Hash.soundness env hrows)
    | (rw [clockArtifact_ext h] at hrows ⊢; rw [h, show [0, 1, 3] ++ List.range' 4 9 = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10,
        11, 12] from rfl]; exact Flock.Clock.Ext.soundness env hrows)

/-- A table row whose clock circuit is satisfied by an assignment whose ports are the row's clock, previous-timestamp
and step columns, read as words, and whose extension-field flag bit is Boolean. -/
def TableRow.ClockValid (tr : TableRow) : Prop :=
  tr.1 ∈ all ∧ tr.1.BaseBit tr.2 ∧ ∃ env : Environment Bit, (clockArtifact tr.1).rows.Forall (Row.Holds env.get) ∧
    tr.2 tr.1.layout.ts = ofWord (Flock.Clock.tsNum env.get) ∧
    (∀ i (hi : i < (Flock.Clock.prevNums tr.1.slots.length env.get).length),
      tr.2 (tr.1.layout.prev + i) = ofWord (Flock.Clock.prevNums tr.1.slots.length env.get)[i]) ∧
    tr.2 tr.1.layout.step = ofWord (Flock.Clock.stepNum (clockArtifact tr.1) env.get)

theorem TableRow.ClockValid.valid {tr : TableRow} (h : tr.ClockValid) : tr.Valid := by
  obtain ⟨ hs, base, env, hrows, ts_col, prev_col, step_col ⟩ := h
  exact ⟨ hs, base, _, _, _, clock_sound hs env hrows, ts_col, prev_col, step_col ⟩

/--
The end-to-end bus theorem for the instruction tables with their clock circuits: if every table row's clock circuit
is satisfied, its ports bound to the row's columns, and the tables' bus balances, then `Machine.Correct` holds for the
rows as machine rows, and every row's `pc` is an instruction address whose decoded entry is the one the row reads.
-/
theorem tables_correct_of_clock (m : Machine) (mult : Fin (2 ^ m.kbc) → ℕ) (trs : List TableRow)
    (valid : ∀ tr ∈ trs, tr.ClockValid) (balance : (tableBus m mult trs).Balanced) :
    m.Correct mult (trs.map fun tr => tr.1.row tr.2) ∧
      ∀ tr ∈ trs, ∃ i : Fin (2 ^ m.kbc), tr.2 tr.1.layout.pc = ofWord (m.tbase + 4 * i) ∧
        tr.1.decoded tr.2 = m.decoded i :=
  tables_correct m mult trs (fun tr htr => (valid tr htr).valid) balance

end LeanVMCircuits.Bus.ClassTable
