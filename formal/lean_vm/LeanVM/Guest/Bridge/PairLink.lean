/-
  LeanVM.Guest.Bridge.PairLink

  The computed hints' data check of compiled function `j` over the deployed alignment (`Bridge.ctxOf`), and its advice the advice's by function, from its pack's.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.PairDefs
import LeanVM.Guest.Bridge.JumpCellsPack
import all Statement.Data.AdviceHints
meta import LeanVM.Guest.KernelLit

/-!
# The data check by index

`PairJ j`: compiled function `j` passes the computed hints' data check (`pairChk`) over its hint-only cells `extraOf j`, certificate cells and frame size, its advice `adviceOf j` is entry `j` of `Data.adviceFns`, of its code's length. The generated checks (`Bridge/PairChk/`, by `scripts/bridge-cert/pair.py`) state the check over each function's pack data; `pairJ_of` equates the two by the `Checked` and `ProgAl` link equations, as `fnAlOk_of` does for the alignment, and reads the
advice's entry off the trie by index `alignAdvice`, which the kernel checks once is the advice's list
(`adviceFns_getElem?`); the alignment's cell map is the certificate's but at the hint-only cells (`locAt_ofData`), so the check reads the certificate's cells.
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

/-- The advice by function as a trie by index. -/
private kernel_rfl alignAdvice_eq : buildT 11 Data.adviceFns = alignAdvice

private theorem advice_bounds : nFns ≤ Data.adviceFns.length ∧ nFns + 1 < 2 ^ 11 := by decide +kernel

/-- **Entry `j` of the advice by function is `adviceOf j`**, for every compiled function `j`. -/
theorem adviceFns_getElem? {j : ℕ} (hj : j < nFns) : Data.adviceFns[j]? = some (adviceOf j) := by
  obtain ⟨hl, h2⟩ := advice_bounds
  rw [adviceOf, ← alignAdvice_eq, getF_buildT 11 _ _ (by omega),
    List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- **A function's data check from its pack's**, by its code, core IR, certificate, tables and frame
size. -/
theorem pairJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)}
    {n : ℕ} (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hn : B2C.fsN j = n)
    (h : pairChk ex C.locs n cf.body = true)
    (hj : j < nFns) (hl : d.2.1 = f.instructionCount) : PairJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hlc : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  refine ⟨?_, adviceFns_getElem? hj, by rw [hd, hf]; exact hl⟩
  rw [hlc, hex, hcf, hn]
  exact h

end

end LeanVM.Guest.Bridge
