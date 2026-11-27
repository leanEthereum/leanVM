/-
  LeanVM.Guest.Bridge.ProgAl

  The deployed guest's functions align: `ProgAl guestProgram coreProgram alignA`, with `main` entered at `mainEntry`, a premise of the tree track's trace on the program.
-/

module

public import LeanVM.Guest.Bridge.ProgAl.All
public import LeanVM.Guest.Bridge.ProgAlKeys
public import LeanVM.Guest.B2C.FrameAll
public import LeanVM.Guest.B2C.CplWalk
public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.B2C.Cells
public import LeanVM.Guest.CheckSplit
public import LeanVM.Guest.Exec
public import LeanVM.Guest.JumpTable
import all LeanVM.Guest.Data.Functions
import all Statement.Data.AdviceHints

/-!
# The deployed guest's alignment

`progAl`: every function of `coreProgram`, of compiled index `j` (`fn_of_idx`), passes its check (`ProgAl.fnAlOk_all`) on its body, its code is fetched at its entry (`guest_fetches`), its halting pc is the last slot. A callee a check names by entry (`AlignCtx.entOk`) is in its table of callees (`trieOf_mem`), a compiled function `c` (`calleesOk`) named `(coreOf c).name`, so `alignA` reads it at index `c` (`idxOf_coreOf`) with that entry. `alignA_main`: `main` is entered at `mainEntry`.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Guest.Exec (Trie)
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.End (mainEntry)

public section

/-- **A callee a check names by entry is entered there.** -/
theorem alignA_ent {f g : String} {t : ℕ} (h : (alignA f).X.entOk t g = true) : (alignA g).X.entry = t := by
  generalize hj : (B2C.idxOf f).getD 0 = j at h
  simp only [alignA, hj, fnAl, ctxOf, AlignCtx.ofData, AlignCtx.entOk] at h
  have hb : ∀ p ∈ (entsOf j).map (fun e ↦ (e.2, e.1)), p.1 + 1 < 2 ^ Exec.indexDepth := by
    intro p hp
    simp only [entsOf, List.map_map, List.mem_map, Function.comp_apply] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    exact entry_key (calleesOf_mem hc).2
  split at h
  · rename_i g' hg
    have hgg : g' = g := nameEq_iff.mp h
    subst hgg
    have hm := trieOf_mem hb hg
    simp only [entsOf, List.map_map, List.mem_map, Function.comp_apply, Prod.mk.injEq] at hm
    obtain ⟨c, hc, rfl, rfl⟩ := hm
    obtain ⟨h1, h2⟩ := calleesOf_mem hc
    rw [alignA_of (B2C.idxOf_coreOf h1 h2)]
    rfl
  · cases h

theorem alignA_halt : regs alignHalt 0 = Registers.final guestProgram := by
  simp only [regs, Registers.final, LeanIsaProgram.pcFinal, guest_logSize, Exec.gpow_zero', alignHalt, CoreMode.haltPc]
  rfl

private theorem idxOf_main : B2C.idxOf "main" = some 1 := by decide +kernel

/-- **`main` is entered at `mainEntry`.** -/
theorem alignA_main : entOf alignA "main" = mainEntry := by
  rw [entOf, alignA_of idxOf_main]
  decide +kernel

/-- **The deployed guest's functions align.** -/
theorem progAl : ProgAl guestProgram coreProgram alignA where
  ok f fn hf := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨-, -, -, -, -, -, -, -, h1, h2⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj]
    exact ProgAl.fnAlOk_all j h1 (by have : nFns = fn_count% := rfl; omega)
  body f fn hf := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨i, -, hi, -, hfi, hc, -⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj, fnAl, hc, ← Option.some.inj (hfi.symm.trans hf)]
  fetch f fn hf off ins h := by
    obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
    obtain ⟨-, -, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx hj
    rw [alignA_of hj] at h ⊢
    exact (Exec.guest_fetches (B2C.fnOf_memC h2) off ins h).1
  ent f fn t g _ h := alignA_ent h
  halt f fn _ _ := alignA_halt

end

end LeanVM.Guest.Bridge
