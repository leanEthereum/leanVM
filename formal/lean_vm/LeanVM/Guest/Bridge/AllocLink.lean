/-
  LeanVM.Guest.Bridge.AllocLink

  The allocation hints' check of compiled function `j` over the deployed alignment, from its pack's.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.AllocDefs

/-!
# The allocation check by index

`AllocJ j`: compiled function `j` passes the allocation hints' check (`allocChk`) over its alignment
context, frame size, plumbing, body, code and advice; `CurJ j`: its part behind the bump pointer's
moves (`curChk`), which every function passes. The generated checks (`Bridge/AllocChk/`, by
`scripts/bridge-cert/alloc.py`) state it over each function's pack data; `allocJ_of` equates the two
by the `Checked` and `ProgAl` link equations, as `fnAlOk_of` does for the alignment; `curJ_of` likewise.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Compiled function `j` passes the allocation hints' check.** -/
def AllocJ (j : ℕ) : Prop :=
  allocChk (ctxOf j) (B2C.fsN j) (B2C.plumbOf j) (coreOf j).body (fnOf j).code (adviceOf j) = true

/-- **Compiled function `j` passes the bump pointer's check** (`curChk`). -/
def CurJ (j : ℕ) : Prop :=
  curChk (ctxOf j) (B2C.plumbOf j) (coreOf j).body (fnOf j).code (adviceOf j) = true

end

public section

/-- **A function's allocation check from its pack's**, by its code, core IR, certificate, plumbing
and tables. -/
theorem allocJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main) {n : ℕ}
    (hn : B2C.fsN j = n)
    (hs : allocShape cf.body = true)
    (hb : curBody (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      P cf.body f.code d = true)
    (h : allocRest (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      n P cf.body f.code d = true) : AllocJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [AllocJ, allocChk, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm, hn, hs, hb, h]
  rfl

/-- The bump pointer's check from the allocation check. -/
theorem curJ_of_allocJ {j : ℕ} (h : AllocJ j) : CurJ j := by
  simp only [AllocJ, allocChk, allocRest, Bool.and_eq_true] at h
  simp only [CurJ, curChk, Bool.and_eq_true]
  exact ⟨h.2.2, h.1.2⟩

/-- **A function's bump pointer check from its pack's**, as `allocJ_of`. -/
theorem curJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main)
    (hb : curBody (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      P cf.body f.code d = true)
    (h : curCode (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt f.instructionCount)
      P f.code d = true) : CurJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [CurJ, curChk, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm, hb, h]
  rfl

end

end LeanVM.Guest.Bridge
