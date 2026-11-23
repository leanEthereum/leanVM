/-
  LeanVM.Guest.CoreMode.FnReg

  The registries of each function's own routing facts and families: what the generated `Gen/FnData`,
  `Gen/FnFams` and `Gen/FnSound` concatenate.
-/

module

/-!
# Each function's own facts and families

A function's own routing data, families and their soundness are its own modules, `CoreMode/Fn/<f>/Data.lean`,
`Fam.lean` and `Sound.lean` (namespace `CoreMode.Own.<f>`), each defining lists by kind (`expFacts`, `stLoops`,
`fams`, …) and proving each entry of them sound (`expFacts_ok`, …). `scripts/core-mode/fnreg.py` concatenates them
into the registries (`FnReg.expFacts`, …, `Gen/FnData.lean`, `Gen/FnFams.lean`) and their soundness
(`FnReg.expFacts_ok`, …, `Gen/FnSound.lean`, by `all_append`). The shared checks and theorems read only the
registries, so no shared file names a function: a guest edit to one function changes its own modules at most.
-/

namespace LeanVM.Guest.CoreMode.FnReg

public section

theorem all_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := by simp

theorem all_append {α : Type} {P : α → Prop} {l r : List α} (h1 : ∀ x ∈ l, P x) (h2 : ∀ x ∈ r, P x) :
    ∀ x ∈ l ++ r, P x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h1 x h
  · exact h2 x h

end

end LeanVM.Guest.CoreMode.FnReg
