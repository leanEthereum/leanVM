/-
  LeanVM.Guest.Bridge.AllocFnLink

  The allocation track's check of compiled function `j` over the deployed alignment, from its pack's,
  and the check by name at `alignA`.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.CurChk
public import LeanVM.Guest.B2C.Cells

/-!
# The allocation track's check by index

`AllocFnJ j`: compiled function `j` passes `allocFnChk` over its alignment context (`ctxOf j`), core
function, code and advice. The generated checks (`Bridge/AllocChk/`, by `scripts/bridge-cert/alloc.py`)
state it over each function's pack data; `allocFnJ_of` equates the two by the `Checked` and `ProgAl`
link equations, as `fnAlOk_of` does for the alignment (the bus era's `curJ_of`). `allocFnChk_alignA`:
every function by name passes it at `alignA`, from every index's.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Compiled function `j` passes the allocation track's check.** -/
def AllocFnJ (j : ℕ) : Prop := allocFnChk (ctxOf j) (coreOf j) (fnOf j).code (adviceOf j) = true

end

public section

/-- **A function's allocation track check from its pack's**, by its code, core IR, certificate,
plumbing and tables. -/
theorem allocFnJ_of {j : ℕ} {f : CompiledFunction} {cf : Core.Fn} {C : Check.Cert} {P : B2C.Plumb}
    {ex : List (ℕ × ℕ)} {en : List (String × ℕ)} {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} {main : Bool}
    (hf : fnOf j = f) (hcf : coreOf j = cf) (hC : certOf j = C.withPows Data.powTree) (hP : B2C.plumbOf j = P)
    (ht : (extraOf j, entsOf j, adviceOf j) = (ex, en, d)) (hm : (j == 1) = main)
    (h : allocFnChk (AlignCtx.ofData C.locs ex f.entryPc main P Data.powTree Data.jtTrie en alignHalt
      f.instructionCount) cf f.code d = true) : AllocFnJ j := by
  simp only [Prod.mk.injEq] at ht
  obtain ⟨hex, hen, hd⟩ := ht
  have hl : (certOf j).locs = C.locs := by rw [hC]; cases C; rfl
  rw [AllocFnJ, ctxOf, hl, hex, hen, hd, hf, hcf, hP, hm]
  exact h

/-- A core function's name has a compiled index. -/
theorem idxOf_of_find' {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) : ∃ j, B2C.idxOf f = some j := by
  have h' : List.find? (fun g ↦ g.name == f) coreProgram = some fn := h
  have hany : coreProgram.any (fun g ↦ g.name == f) = true :=
    List.any_eq_true.mpr ⟨fn, List.mem_of_find?_eq_some h', List.find?_some (p := fun g : Fn ↦ g.name == f) h'⟩
  rw [← List.findIdx?_isSome] at hany
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hany
  exact ⟨i + 1, by unfold B2C.idxOf Core.Program.indexOf?; rw [hi]; rfl⟩

/-- **Every core function passes the allocation track's check at the deployed alignment**, from
every compiled index's. -/
theorem allocFnChk_alignA (hall : ∀ j, 1 ≤ j → j < nFns → AllocFnJ j) :
    ∀ f fn, coreProgram.find? f = some fn → allocFnChk (alignA f).X fn (alignA f).code (alignA f).d = true := by
  intro f fn hfn
  obtain ⟨j, hj⟩ := idxOf_of_find' hfn
  obtain ⟨i, rfl, hi, -, hfind, hcore, -, -, h1, h2⟩ := B2C.fn_of_idx hj
  rw [hfn] at hfind
  cases hfind
  have h := hall (i + 1) h1 h2
  rw [AllocFnJ, hcore] at h
  rw [alignA_of hj]
  exact h

end

end LeanVM.Guest.Bridge
