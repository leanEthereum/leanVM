/-
  LeanVM.Guest.Bridge.PairLink

  The computed hints' data check of compiled function `j` over the deployed alignment (`Bridge.ctxOf`), and its advice the advice's by function, from its pack's.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.PairDefs

/-!
# The data check by index

`AdvJ j`: compiled function `j`'s advice `adviceOf j` is entry `j` of `Data.adviceFns`, of its code's length. `PairJ j`: it passes the computed hints' data check (`pairChk`) over its hint-only cells `extraOf j`, certificate cells and frame size, and `AdvJ j`. The generated checks (`Bridge/PairChk/`, by `scripts/bridge-cert/pair.py`) state the check over each function's pack data; `pairJ_of` equates the two by the `Checked` and `ProgAl` link equations, as `fnAlOk_of` does for the alignment. `AdvJ` stands apart (`PairChk/Adv*`, `advJ_all`), so the advice's facts do not wait on the data check.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Compiled function `j`'s advice is the advice's `j`-th function**, of its code's length. -/
def AdvJ (j : ℕ) : Prop := Data.adviceFns[j]? = some (adviceOf j) ∧ (adviceOf j).2.1 = (fnOf j).instructionCount

/-- **Compiled function `j`'s computed hints pass the data check, its advice the advice's.** -/
def PairJ (j : ℕ) : Prop :=
  pairChk (extraOf j) (certOf j).locs (B2C.fsN j) (coreOf j).body = true ∧ AdvJ j

end

public section

/-- **A function's advice facts from its table entry.** -/
theorem advJ_of {j : ℕ} {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (ha : Data.adviceFns[j]? = some d)
    (hl : d.2.1 = (fnOf j).instructionCount) : AdvJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨-, -, hd⟩ := ht
  exact ⟨by rw [hd]; exact ha, by rw [hd]; exact hl⟩

/-- **A function's data check from its pack's**, by its core IR, certificate, tables and frame size. -/
theorem pairJ_of {j : ℕ} {cf : Core.Fn} {C : Check.Cert}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    {n : ℕ} (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hn : B2C.fsN j = n)
    (h : pairChk ex C.locs n cf.body = true) (ha : AdvJ j) : PairJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, -, -⟩ := ht
  have hlc : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  refine ⟨?_, ha⟩
  rw [hlc, hex, hcf, hn]
  exact h

end

end LeanVM.Guest.Bridge
