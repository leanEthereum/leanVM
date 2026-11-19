/-
  LeanVM.Compiler.Sound.Hints

  Hints are not constraints: the assembled program and its layout are the same with every hint
  dropped.
-/

module

public import LeanVM.Compiler.Sound.Lowered

/-!
# Hints are prover advice

An instruction's hints (`LInstr.hints`) fire before it in the provers' executors: allocations and
computed advice, which write memory cells and assert nothing. Assembly resolves them into
`Assembled.hints`, which the program the statement reads (`Assembled.program`, from the code and
the function ranges) never consults, and the layout (`layoutOf`) reads only names, frame sizes and
code lengths. So dropping every hint changes neither (`assemble_dropHints`, `layoutOf_dropHints`):
every theorem about a compiled program's bytecode (`World.prog`, `World.layout`), soundness among
them, holds whatever its hints are, the selected allocation of a dispatch's frame
(`LHint.allocFrameSel`) included.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Core

@[expose] public section

/-- A function with every hint dropped. -/
def Lowered.dropHints (f : Lowered) : Lowered :=
  { f with code := f.code.map fun i => { i with hints := [] } }

theorem withTables_dropHints (fns : List Lowered) (slots : Array KVal) :
    withTables (fns.map Lowered.dropHints) slots =
      ((withTables fns slots).1.map Lowered.dropHints, (withTables fns slots).2) := by
  cases fns with
  | nil => rfl
  | cons main rest =>
      by_cases hs : slots.isEmpty
      · simp [withTables, hs, Lowered.dropHints]
      · simp [withTables, hs, Lowered.dropHints, Array.map_map, Function.comp_def]

theorem layout_dropHints (fns : List Lowered) (tb : ℕ) :
    layout (fns.map Lowered.dropHints) tb = layout fns tb := by
  simp [layout, List.foldl_map, Lowered.dropHints]

theorem resolvedFrom_dropHints (l : Layout) : ∀ (fns : List Lowered) (pc : ℕ),
    resolvedFrom l (fns.map Lowered.dropHints) pc = resolvedFrom l fns pc
  | [], _ => rfl
  | f :: fs, pc => by
      simp [resolvedFrom, resolvedFn, Lowered.dropHints, resolvedFrom_dropHints l fs]

theorem rangesFrom_dropHints : ∀ (fns : List Lowered) (pc : ℕ),
    rangesFrom (fns.map Lowered.dropHints) pc = rangesFrom fns pc
  | [], _ => rfl
  | f :: fs, pc => by
      simp [rangesFrom, Lowered.dropHints, rangesFrom_dropHints fs]

theorem assembleAt_toFunctions_dropHints (l : Layout) (size : ℕ) (fns : List Lowered) :
    (assembleAt l size (fns.map Lowered.dropHints)).toFunctions =
      (assembleAt l size fns).toFunctions := by
  have hc : (assembleAt l size (fns.map Lowered.dropHints)).code = (assembleAt l size fns).code := by
    apply Array.toList_inj.mp
    rw [assembleAt_code, assembleAt_code, resolvedFrom_dropHints]
  have hf : (assembleAt l size (fns.map Lowered.dropHints)).fns = (assembleAt l size fns).fns := by
    apply Array.toList_inj.mp
    rw [assembleAt_fns, assembleAt_fns, rangesFrom_dropHints]
  unfold Assembled.toFunctions
  rw [hc, hf]

/-- **The layout does not read the hints.** -/
theorem layoutOf_dropHints (fns : List Lowered) (slots : Array KVal) :
    layoutOf (fns.map Lowered.dropHints) slots = layoutOf fns slots := by
  simp only [layoutOf, withTables_dropHints, layout_dropHints]

/-- **The assembled program does not read the hints**: its padded size and the program the
statement reads are those of the functions with every hint dropped. -/
theorem assemble_dropHints (fns : List Lowered) (slots : Array KVal) :
    (assemble (fns.map Lowered.dropHints) slots).size = (assemble fns slots).size ∧
      ∀ (logSize : ℕ) (hl : logSize ≤ maxLogBytecode),
        (assemble (fns.map Lowered.dropHints) slots).program logSize hl =
          (assemble fns slots).program logSize hl := by
  simp only [assemble_def, withTables_dropHints, layout_dropHints]
  refine ⟨rfl, fun logSize hl => ?_⟩
  simp only [Assembled.program, assembleAt_toFunctions_dropHints]

end
end LeanVM.Compiler
