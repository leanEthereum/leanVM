/-
  LeanVM.Guest.ExecC

  The executor's input read past whole code chunks, for the kernel.
-/

module

public import LeanVM.Guest.CheckView
public import LeanVM.Guest.Glob
public import LeanVM.Guest.FunctionTable

/-!
# A window's code, by chunks, for the guest's functions

`execWin` reads a window's code as `f.code.drop a`, a structural walk over the whole flattened
code before the window, which the kernel pays for at every evaluation. `execWinC` (`CheckView.lean`)
skips whole chunks first (`codeFrom`); for every guest function the two agree (`execWinC_eq`, the
functions being well chunked).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Check LeanVM.Guest.Exec

@[expose] public section

private theorem nth_past {α : Type} : ∀ {l : List α} {n : ℕ} {d : α}, l.length ≤ n →
    listElementOrDefault l n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, h => absurd h (by simp)
  | _ :: as, n + 1, _, h => nth_past (l := as) (by simpa using h)

theorem fnOf_wellChunked (j : ℕ) : chunked chunkSize (fnOf j).chunks (fnOf j).instructionCount =
    true := by
  by_cases h : j < Data.functions.length
  · unfold fnOf
    rw [show listElementOrDefault Data.functions j default = Data.functions[j] from
      Option.some.inj ((nth_eq_getElem? default h).symm.trans (List.getElem?_eq_getElem h))]
    exact List.all_eq_true.mp functions_wellChunked _ (List.getElem_mem h)
  · unfold fnOf
    rw [nth_past (by omega)]
    rfl

theorem execWinC_eq (j : ℕ) (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (b : ℕ) :
    execWinC F (fnOf j) a env b = execWin F (fnOf j) a env b :=
  execWinC_eq_of (fnOf_wellChunked j) F a env b

theorem execWinCS_eq (j : ℕ) (F : Facts) (a : ℕ) (env : List (ℕ × Sym)) (seeds : List ℕ) (b : ℕ) :
    execWinCS F (fnOf j) a env seeds b = execWinS F (fnOf j) a env seeds b :=
  execWinCS_eq_of (fnOf_wellChunked j) F a env seeds b

end
end LeanVM.Guest.B2C
