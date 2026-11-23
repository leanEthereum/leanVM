/-
  LeanVM.Guest.Bridge.ProgAlDefs

  The deployed guest's alignment by name (`alignA`): each function's alignment check's context, body, code and advice, read off the compiled program by index.
-/

module

public import LeanVM.Guest.Bridge.StepRule
public import LeanVM.Guest.Bridge.ProgAlData
public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.CoreMode.GlueG

/-!
# The deployed guest's alignment

`alignA f` is `fnAl j` for the compiled index `j` of `f` (`idxOf`), `fnAl 0` (`__jump_tables`, whose check nothing reads) for a name not in the program. `fnAl j`: the check's context `ctxOf j`, the body `(coreOf j).body`, the code `(fnOf j).code` and the advice `Data.adviceFn{j}` (`alignAdvice`). `ctxOf j` is `AlignCtx.ofData` of the function's own data: its certificate's cells (`certOf j`), its hint-only cells (`extraOf j`, the generated `alignExtras`; the tables are tries, read in a few steps), its entry, whether it is `main` (`j = 1`), its plumbing (`plumbOf j`), the program's powers of `g` and jump table, its callees with their entries (`entsOf j`: the generated `alignCallees`, by index), the halting pc (`CoreMode.haltPc`) and its length. The generated checks (`Bridge/Align*/`) state each function's context by its pack's data; `fnAlOk_of` equates the two.

`FnAlOk j`: function `j` passes its check; `ProgAl/All.lean` proves it of every function.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The halting pc, the last slot (`CoreMode.haltPc`). -/
def alignHalt : ℕ := CoreMode.haltPc

/-- The hint-only cells of compiled function `j`. -/
noncomputable def extraOf (j : ℕ) : List (ℕ × ℕ) := (Check.getF alignExtras j).getD []

/-- The callees of compiled function `j` its check names, by index. -/
noncomputable def calleesOf (j : ℕ) : List ℕ := (Check.getF alignCallees j).getD []

/-- The callees of compiled function `j` its check names, with their entries. -/
noncomputable def entsOf (j : ℕ) : List (String × ℕ) :=
  (calleesOf j).map fun c ↦ ((coreOf c).name, (fnOf c).entryPc)

/-- **The alignment check's context of compiled function `j`.** -/
noncomputable def ctxOf (j : ℕ) : AlignCtx :=
  AlignCtx.ofData (certOf j).locs (extraOf j) (fnOf j).entryPc (j == 1) (B2C.plumbOf j) Data.powTree Data.jtTrie
    (entsOf j) alignHalt (fnOf j).instructionCount

/-- The advice of compiled function `j`. -/
noncomputable def adviceOf (j : ℕ) : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint) :=
  (Check.getF alignAdvice j).getD (0, 0, [])

/-- What the step rule reads of compiled function `j`. -/
noncomputable def fnAl (j : ℕ) : FnAl := ⟨ctxOf j, (coreOf j).body, (fnOf j).code, adviceOf j⟩

/-- **The deployed guest's alignment, by name.** -/
noncomputable def alignA (f : String) : FnAl := fnAl ((B2C.idxOf f).getD 0)

/-- Compiled function `j` passes its alignment check. -/
def FnAlOk (j : ℕ) : Prop := alignOk (ctxOf j) (coreOf j).body (fnOf j).code (adviceOf j) = true

end

public section

theorem alignA_of {f : String} {j : ℕ} (h : B2C.idxOf f = some j) : alignA f = fnAl j := by
  simp [alignA, h]

/-- **A function's check from its pack's**, by its code, core IR, certificate, plumbing and tables. -/
theorem fnAlOk_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main)
    (h : alignOk (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      cf.body f.code d = true) : FnAlOk j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [FnAlOk, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm]
  exact h

end

end LeanVM.Guest.Bridge
