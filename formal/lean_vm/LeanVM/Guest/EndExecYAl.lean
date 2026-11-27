/-
  LeanVM.Guest.EndExecYAl

  The deployed alignment reads the executor's hints: `AdvAl alignA`.
-/

module

public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.EndExecYAdvAl
public import LeanVM.Guest.Bridge.ProgAl
public import LeanVM.Guest.Mode.HintsData
import all LeanVM.Guest.Data.Functions
import all Statement.Data.AdviceHints

/-!
# The deployed alignment's advice

`advAl_alignA`: at each offset of a function's code, the hints the alignment check reads are the
advice's at that pc, since the check's advice is the advice's own for the function (`adviceOf_fns`),
whose entries lie in its pcs (`Mode.hintsAt_fns`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Bridge
open LeanVM.Prover.Exec (Hint)

public section

theorem lookup_getD (x : ℕ) : ∀ l : List (ℕ × List Hint), (l.lookup x).getD [] = Mode.hintsAt l x
  | [] => rfl
  | (k, v) :: l => by
    unfold Mode.hintsAt
    rw [List.lookup_cons, List.find?_cons]
    by_cases h : x = k
    · subst h; simp
    · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
      exact lookup_getD x l

/-- **The deployed alignment reads the executor's hints.** -/
theorem advAl_alignA : AdvAl alignA := by
  intro f fn hf off ins hins
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨-, -, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx hj
  have hok := progAl.ok f fn hf
  rw [alignA_of hj] at hins hok ⊢
  rw [alignOk, AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  obtain ⟨hd, hlen⟩ := adviceOf_fns h2
  have hoff : off < (fnOf j).code.length := (List.getElem?_eq_some_iff.mp hins).1
  show ((adviceOf j).2.2.lookup ((ctxOf j).entry + off)).getD [] = _
  have he : (adviceOf j).1 = (ctxOf j).entry := hok.1.1.1.2
  rw [lookup_getD]
  exact (Mode.hintsAt_fns (d := adviceOf j) Mode.adviceFns_ok (List.mem_of_getElem? hd) (by omega)
    (by omega)).symm

end

end LeanVM.Guest.EndExec
