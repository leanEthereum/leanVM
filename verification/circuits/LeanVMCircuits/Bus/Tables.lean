module

public import LeanVMCircuits.Bus.TableRows

@[expose] public section

/-!
# The bus of the instruction tables

`machine_correct` for the instruction-table rows: the bus made of each row's exported source flushes (`ClassTable.Spec.flushes`), the state boundary, the seeds and finalizations and the bytecode producer. When every row's clock circuit ports hold words satisfying `Clock.Holds` and the extension-field flag bit is Boolean, balance gives `Machine.Correct` for the rows as machine rows, and every row's bytecode read is the decoded instruction at its `pc` (`tables_correct`).
-/

namespace LeanVMCircuits.Bus.ClassTable

open LeanVMCircuits.Rec

/-- A row of an instruction table: its table's specification and its column values. -/
abbrev TableRow := Spec × (ℕ → K)

/-- A table row is valid: its table is an instruction table, its extension-field flag bit is Boolean, and its clock
circuit's ports hold words satisfying `Clock.Holds`, bound to its clock, previous-timestamp and step columns. -/
def TableRow.Valid (tr : TableRow) : Prop :=
  tr.1 ∈ all ∧ tr.1.BaseBit tr.2 ∧ ∃ ts step : ℕ, ∃ prev : List ℕ, Clock.Holds tr.1.slots prev ts step ∧
    tr.2 tr.1.layout.ts = ofWord ts ∧ (∀ i (hi : i < prev.length), tr.2 (tr.1.layout.prev + i) = ofWord prev[i]) ∧
    tr.2 tr.1.layout.step = ofWord step

/-- The rows' source flushes, together. -/
noncomputable def tableRowFlushes (trs : List TableRow) : Flushes where
  pushes := trs.flatMap fun tr => (tr.1.flushes tr.2).pushes
  pulls := trs.flatMap fun tr => (tr.1.flushes tr.2).pulls

/-- The bus of the instruction tables: the rows' flushes, the state boundary, the seeds and finalizations of the
registers, RAM and the advice, and the bytecode producer pushing entry `i` with multiplicity `mult i`. -/
noncomputable def tableBus (m : Machine) (mult : Fin (2 ^ m.kbc) → ℕ) (trs : List TableRow) : Flushes :=
  tableRowFlushes trs ++ m.boundary ++ m.reg.flushes [] ++ m.ram.flushes [] ++ m.adv.flushes [] ++
    m.lut.flushes mult []

theorem tableRowFlushes_pushed (trs : List TableRow)
    (h : ∀ tr ∈ trs, ((tr.1.flushes tr.2).pushes : Multiset Tuple) = (tr.1.row tr.2).flushes.pushes) :
    (tableRowFlushes trs).pushed = (rowFlushes (trs.map fun tr => tr.1.row tr.2)).pushed := by
  induction trs with
  | nil => rfl
  | cons tr trs ih =>
    have ih' := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [tableRowFlushes, rowFlushes, Flushes.pushed, List.map_cons, List.flatMap_cons, ← Multiset.coe_add,
      List.map_nil, List.sum_nil, add_zero] at ih' ⊢
    rw [h tr (List.mem_cons_self ..), ih']

theorem tableRowFlushes_pulled (trs : List TableRow)
    (h : ∀ tr ∈ trs, ((tr.1.flushes tr.2).pulls : Multiset Tuple) = (tr.1.row tr.2).flushes.pulls) :
    (tableRowFlushes trs).pulled = (rowFlushes (trs.map fun tr => tr.1.row tr.2)).pulled := by
  induction trs with
  | nil => rfl
  | cons tr trs ih =>
    have ih' := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [tableRowFlushes, rowFlushes, Flushes.pulled, List.map_cons, List.flatMap_cons,
      ← Multiset.coe_add] at ih' ⊢
    rw [h tr (List.mem_cons_self ..), ih']

/--
The end-to-end bus theorem for the instruction tables. If every table row is valid and the tables' bus balances,
then `Machine.Correct` holds for the rows as machine rows (correct bytecode reads, one walk of the live rows in clock
order, consistent registers and RAM with the advice), and every row's `pc` is an instruction address `tbase + 4 i`
whose decoded entry is the one the row reads.
-/
theorem tables_correct (m : Machine) (mult : Fin (2 ^ m.kbc) → ℕ) (trs : List TableRow)
    (valid : ∀ tr ∈ trs, tr.Valid) (balance : (tableBus m mult trs).Balanced) :
    m.Correct mult (trs.map fun tr => tr.1.row tr.2) ∧
      ∀ tr ∈ trs, ∃ i : Fin (2 ^ m.kbc), tr.2 tr.1.layout.pc = ofWord (m.tbase + 4 * i) ∧
        tr.1.decoded tr.2 = m.decoded i := by
  have facts : ∀ tr ∈ trs, ((tr.1.flushes tr.2).pushes : Multiset Tuple) = (tr.1.row tr.2).flushes.pushes ∧
      ((tr.1.flushes tr.2).pulls : Multiset Tuple) = (tr.1.row tr.2).flushes.pulls ∧
      (tr.1.row tr.2).C1 ∧ (tr.1.row tr.2).C2 ∧ (tr.1.row tr.2).C3 := by
    intro tr htr
    obtain ⟨ hs, base, ts, step, prev, holds, ts_col, prev_col, step_col ⟩ := valid tr htr
    exact row_correct hs tr.2 holds ts_col prev_col step_col base
  have c1 : ∀ r ∈ trs.map (fun tr => tr.1.row tr.2), r.C1 := by
    intro r hr
    obtain ⟨ tr, htr, rfl ⟩ := List.mem_map.mp hr
    exact (facts tr htr).2.2.1
  have c2 : ∀ r ∈ trs.map (fun tr => tr.1.row tr.2), r.C2 := by
    intro r hr
    obtain ⟨ tr, htr, rfl ⟩ := List.mem_map.mp hr
    exact (facts tr htr).2.2.2.1
  have c3 : ∀ r ∈ trs.map (fun tr => tr.1.row tr.2), r.C3 := by
    intro r hr
    obtain ⟨ tr, htr, rfl ⟩ := List.mem_map.mp hr
    exact (facts tr htr).2.2.2.2
  have bal : (m.flushes mult (trs.map fun tr => tr.1.row tr.2)).Balanced := by
    refine Flushes.balanced_of_eq ?_ ?_ balance
    · simp only [tableBus, Machine.flushes, Machine.tableFlushes, Flushes.pushed_append,
        tableRowFlushes_pushed trs (fun tr h => (facts tr h).1)]
    · simp only [tableBus, Machine.flushes, Machine.tableFlushes, Flushes.pulled_append,
        tableRowFlushes_pulled trs (fun tr h => (facts tr h).2.1)]
  refine ⟨ machine_correct m _ mult c1 c2 c3 bal, fun tr htr => ?_ ⟩
  exact machine_reads_at_pc m _ mult (fun r => (r.reads.headD (0, Vector.replicate 10 0)).2)
    (fun r hr => by
      obtain ⟨ tr, -, rfl ⟩ := List.mem_map.mp hr
      rfl)
    c1 c2 c3 bal (tr.1.row tr.2) (List.mem_map_of_mem htr)

end LeanVMCircuits.Bus.ClassTable
