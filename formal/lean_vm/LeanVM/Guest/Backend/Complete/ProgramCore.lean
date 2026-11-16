/-
  LeanVM.Guest.Backend.Complete.ProgramCore
  Whole-program completeness of the back end from a run of the core IR: no hypothesis about the
  back end's frame words, cells or headers; the range checks' temporaries re-chosen.
-/

module

public import LeanVM.Guest.Backend.Complete.Program
public import LeanVM.Guest.Memory.Discharge

/-!
# Whole-program completeness from a core run

`ProgramCompleteStmt` takes `Memory.HonestAt` at the back end's data, three of whose parts speak
of the back end's own words: the cells fit and agree (`CellsOk` of `World.cellsB`), the frame words
agree with the memory equations where they meet (`cross`), and the equations agree among
themselves on the honest memory. `ProgramCompleteCoreStmt` asks none of them.

**The run of the core IR** is a call tree `T` of `main`, valid on a memory `M` of `2^logMem` words
for the words it allocates, with:

* its `HeapBuf`s those of its paths (`Tree.BufsOk`);
* its free values where the back end puts them (`Tree.Placed` at `World.fsB`, `World.cellB`): every
  `HeapBuf` pointer the bump allocator's base, every `frameAddr` the address of its run's first
  cell;
* its loads in its own data (its `HeapBuf`s, its `frameAddr` runs, its callers') or in `main`'s
  header words `0`, `1` (`Tree.LoadsIn`), which hold the public input `hdr`;
* at most `2^30` words, and its equations at addresses of the memory.

**The re-choice.** A range check or a touch reads an arbitrary word, possibly a frame cell, and its
temporaries hold what it reads; the bytecode reads the frame's word there. So the conclusion is
about the tree `T.retemp ν` whose temporaries `ν` are re-chosen to read the honest memory, all its
other values `T`'s.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Whole-program completeness from a core run**: for a compiled program whose every function
passes the per-function conditions, for every run `T` of `main` on a memory `M`, its free values
where the back end puts them, loading from its own data or the public input `hdr`, of at most
`2^30` words and its equations in the memory, its temporaries re-chosen, the emitted bytecode runs
on the honest memory from `main`'s entry at frame `g^0` to the final registers within the budget. -/
def ProgramCompleteCoreStmt : Prop :=
  ∀ {κ₀ : ℕ} (W : World κ₀), W.Compiled → (∀ tf ∈ W.p, FnConds W tf) →
    ∀ (keyed : String → Bool) (hdr : E × E) (T : Tree)
      (M : MemoryImage (logMem (T.total W.fsB))), T.name = "main" →
      T.Valid W.core M.read [] [] → T.BufsOk W.core →
      T.Placed W.core W.fsB W.cellB 0 → T.LoadsIn W.core W.fsB W.cellB (fun i => i < 2) 0 →
      M.read (addressOfIndex 0) = some hdr.1 → M.read (addressOfIndex 1) = some hdr.2 →
      T.total W.fsB ≤ 2 ^ 30 →
      (∀ q ∈ T.eqns W.core, ∃ i : Fin (2 ^ logMem (T.total W.fsB)), q.1 = addressOfIndex i) →
      ∃ ν : ℕ → String → Val → V → E, ∃ c : Opcode → ℕ,
        RunC W.prog (W.honestB hdr (T.retemp W.core W.fsB ν 0))
          ⟨addressOfIndex (W.ent "main"), 1⟩ (Registers.final W.prog) c ∧
        ∀ op, c op ≤ W.progCost keyed (T.retemp W.core W.fsB ν 0) op

end
end LeanVM.Guest.Backend.Complete
