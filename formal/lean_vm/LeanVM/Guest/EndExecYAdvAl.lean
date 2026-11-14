/-
  LeanVM.Guest.EndExecYAdvAl

  The deployed alignment's advice by function is the advice's own, decided by the kernel.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Mode.Hints

/-!
# The alignment's advice

`adviceOf_fns`: compiled function `j`'s advice in the alignment check (`Bridge.adviceOf j`) is the
`j`-th of the advice's functions, of its code's length.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest

public section

/-- The check of function `j`, its advice `d`. -/
noncomputable def advFnOk (p : (ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) × ℕ) : Bool :=
  decide (p.1 = Bridge.adviceOf p.2) && Nat.beq p.1.2.1 (fnOf p.2).code.length

theorem advFnOk_all : Data.adviceFns.zipIdx.all advFnOk = true ∧ nFns ≤ Data.adviceFns.length := by
  decide +kernel

theorem adviceOf_fns {j : ℕ} (hj : j < nFns) :
    Data.adviceFns[j]? = some (Bridge.adviceOf j) ∧ (Bridge.adviceOf j).2.1 = (fnOf j).code.length := by
  have hl : j < Data.adviceFns.length := lt_of_lt_of_le hj advFnOk_all.2
  have := List.all_eq_true.mp advFnOk_all.1 (Data.adviceFns[j], j)
    (List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hl]))
  simp only [advFnOk, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at this
  rw [List.getElem?_eq_getElem hl, this.1]
  exact ⟨rfl, this.1 ▸ this.2⟩

end

end LeanVM.Guest.EndExec
