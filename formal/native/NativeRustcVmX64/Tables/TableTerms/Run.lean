module

public import NativeRustcVmX64.Tables.TableTerms.State

/-!
# `table_terms`: the model's fold, table by table

The rows (`rowsL_length`, `rowsL_get`), the fold over the first `i + 1` rows from the first `i`
(`preRun_succ`), one table (`stp_run`), the whole run from the fold over the six rows
(`run_full`).
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeVm.Model NativeRustcVm.Tables

public section

variable {heights : Array Nat} {forms : Array (Array FormW)} {m0 : MachineData}

theorem wts_size : (wts m0).size = 6 := by simp [wts, NativeRustcVm.ewsOf, nTables]

theorem rowsL_length (hh : heights.size = 6) (hf : forms.size = 6) :
    (rowsL heights forms m0).length = 6 :=
  NativeVm.Math.Tables.rows_length hh hf wts_size

theorem rowsL_get (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat}
    (hi : i < (rowsL heights forms m0).length) :
    (rowsL heights forms m0)[i] = (tb i, heights.getD i 0, forms.getD i #[], (wts m0).getD i 0) :=
  NativeVm.Math.Tables.rows_get hh hf wts_size hi

/-- **The fold over the first `i + 1` rows.** -/
theorem preRun_succ (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat} (hi : i < 6)
    (s : TState) :
    preRun heights forms m0 (i + 1) s = (preRun heights forms m0 i s).bind fun p ↦
      (stp m0 p.1 (tb i, heights.getD i 0, forms.getD i #[], (wts m0).getD i 0)).run p.2 := by
  have hl : i < (rowsL heights forms m0).length := by rw [rowsL_length hh hf]; exact hi
  unfold preRun
  rw [foldlM_take_succ _ _ _ hl, StateT.run_bind, rowsL_get hh hf hl]
  rfl

/-- **One table**: its evaluations read, then the sum, the cursor and the entry. -/
theorem stp_run (c : Nat) (f : EW) (o : Array (Array EW × Array EW)) (t : TableW) (h : Nat)
    (fs : Array FormW) (w : EW) (si : TState) :
    (stp m0 (c, f, o) (t, h, fs, w)).run si = ((readScalars t.width).run si).map fun p ↦
      ((c + t.nConstraints, f + w * (dot ((cpw m0).extract c (c + t.nConstraints))
        (constraintsW t.opcode p.1) + dot (fpw m0) (fs.map (·.evaluate p.1))),
        o.push ((ptw m0).extract 0 h, p.1)), p.2) := by
  rw [stp, NativeVm.Math.Tables.tableTermsStep_eq, StateT.run_bind]
  cases (readScalars t.width).run si <;> rfl

/-- **The whole run** from the fold over the six rows. -/
theorem run_full (hh : heights.size = 6) (hf : forms.size = 6) (s : TState) :
    (tableTerms (cpw m0) (fpw m0) (ptw m0) (tableRows heights forms (wts m0))).run s =
      (preRun heights forms m0 6 s).map fun p ↦ ((p.1.2.1, p.1.2.2), p.2) := by
  rw [NativeVm.Math.Tables.tableTerms_eq, StateT.run_bind, preRun,
    List.take_of_length_le (by rw [rowsL_length hh hf])]
  unfold rowsL stp
  cases (List.foldlM (tableTermsStep (cpw m0) (fpw m0) (ptw m0)) (0, 0, #[])
    (tableRows heights forms (wts m0)).toList).run s <;> rfl

/-- The model's result from the fold over the six rows. -/
theorem R_eq (hh : heights.size = 6) (hf : forms.size = 6) (s : TState) :
    R heights forms m0 s = (preRun heights forms m0 6 s).map fun p ↦ ((p.1.2.1, p.1.2.2), p.2) :=
  run_full hh hf s

/-- A failed prefix: the whole fold fails. -/
theorem preRun_none (hh : heights.size = 6) (hf : forms.size = 6) {i : Nat} {s : TState}
    (h : preRun heights forms m0 i s = none) : preRun heights forms m0 6 s = none := by
  unfold preRun at h ⊢
  rw [List.take_of_length_le (by rw [rowsL_length hh hf]), foldlM_take_drop _ _ _ i,
    StateT.run_bind, h]
  rfl

end

end NativeRustcVmX64.Tables.TableTerms
