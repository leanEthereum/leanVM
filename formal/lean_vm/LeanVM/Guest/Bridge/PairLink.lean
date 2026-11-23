/-
  LeanVM.Guest.Bridge.PairLink

  The computed hints' data check of compiled function `j` over the deployed alignment (`Bridge.ctxOf`), and its advice the advice's by function, from its pack's.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.PairDefs

/-!
# The data check by index

`PairJ j`: compiled function `j` passes the computed hints' data check (`pairChk`) over its hint-only cells `extraOf j`, certificate cells and frame size, its advice `adviceOf j` is entry `j` of `Data.adviceFns`, of its code's length. The generated checks (`Bridge/PairChk/`, by `scripts/bridge-cert/pair.py`) state the check over each function's pack data; `pairJ_of` equates the two by the `Checked` and `ProgAl` link equations, as `fnAlOk_of` does for the alignment; the alignment's cell map is the certificate's but at the hint-only cells (`locAt_ofData`), so the check reads the certificate's cells.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Compiled function `j`'s computed hints pass the data check, its advice the advice's.** -/
def PairJ (j : ℕ) : Prop :=
  pairChk (extraOf j) (certOf j).locs (B2C.fsN j) (coreOf j).body = true ∧
    Data.adviceFns[j]? = some (adviceOf j) ∧ (adviceOf j).2.1 = (fnOf j).instructionCount

end

public section

/-- **A function's data check from its pack's**, by its code, core IR, certificate, tables and frame
size. -/
theorem pairJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    {n : ℕ} (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hn : B2C.fsN j = n)
    (h : pairChk ex C.locs n cf.body = true)
    (ha : Data.adviceFns[j]? = some d) (hl : d.2.1 = f.instructionCount) : PairJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hlc : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  refine ⟨?_, by rw [hd]; exact ha, by rw [hd, hf]; exact hl⟩
  rw [hlc, hex, hcf, hn]
  exact h

end

end LeanVM.Guest.Bridge
