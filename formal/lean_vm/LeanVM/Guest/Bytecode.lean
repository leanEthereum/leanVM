/-
  LeanVM.Guest.Bytecode

  The compiled aggregation guest as a `Program`, and the fetch lemma at every pc of its
  functions.
-/

module

public import LeanVM.Guest.Data.Functions
import all LeanVM.Guest.Data.Functions
import all Statement.Data.Bytecode
meta import LeanVM.Guest.KernelLit
public import LeanVM.Guest.Code
public import LeanVM.Guest.FunctionTable
public import Statement.LeanVmGuest

/-!
# The guest bytecode

`guestProgram` is `aggregation::unified_guest()`'s bytecode: the statement reads it as one list
of instructions (`Statement.Data.blocks`), and the proofs as the compiled functions of
`LeanVM.Guest.Data.functions` laid out from pc `0` and padded with `SET fp[0] = 0` to `2^19`
instructions (`guestProgram_eq`); `scripts/guest-export` writes both from leanVM's sources, the
blocks being the functions' chunks in layout order (`blocks_eq`), and its `--check` fails when
they are stale. A run starts at `(g^0, 1)` in `__jump_tables`, the
function at pc `0`, which falls through into `main`.

The layout and the chunking are decided once here, over the function table only (`consecutive`,
`chunked`); `guest_fetch` then gives the instruction at pc `entry + i` of any function by
evaluating that one instruction, never the program.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

theorem guest_logSize : guestProgram.logSize = 19 := rfl

/-- `guest` with its slots computed once (`assembleArray`), for compiled code reading them all. -/
def guestArray : LeanIsaProgram := assembleArray Data.functions 19 (by decide)

/-- The functions lie one after another from pc `0` to `codeLen`. -/
theorem functions_consecutive : consecutive 0 Data.functions Data.codeLen = true := by
  decide +kernel

/-- The statement's blocks are the function table's chunks, in layout order (by the kernel alone: the
elaborator's unifier recurses once per block). -/
kernel_rfl blocks_eq : Data.blocks = Data.functions.flatMap (·.chunks)

private theorem toArray_getD {α : Type} (l : List α) (n : ℕ) (d : α) : l.toArray.getD n d = l.getD n d := by
  simp [Array.getD, List.getD_eq_getElem?_getD]
  split <;> simp_all

/-- **The statement's guest is the function table's assembly**: the statement's instruction at
slot `i`, entry `i` of the blocks joined, is the functions' (`getD_flatten_chunks`). -/
theorem guestProgram_eq : guestProgram = assemble Data.functions 19 (by decide) := by
  simp only [guestProgram, assemble, LeanIsaProgram.mk.injEq, heq_eq_eq, true_and]
  funext i
  rw [guestCode, toArray_getD, blocks_eq,
    getD_flatten_chunks functions_consecutive functions_wellChunked]

theorem guestArray_eq : guestArray = guestProgram :=
  (assembleArray_eq _ _ _).trans guestProgram_eq.symm

theorem codeLen_lt : Data.codeLen < 2 ^ 19 - 1 := by decide

theorem CompiledFunction.wellChunked_of_mem {f : CompiledFunction} (hf : f ∈ Data.functions) :
    f.WellChunked :=
  List.all_eq_true.mp functions_wellChunked f hf

/-- **The fetch lemma**: pc `entry + i` of a guest function holds its instruction `i`. -/
theorem guest_fetch {f : CompiledFunction} (hf : f ∈ Data.functions) {i : ℕ} (hi : i <
    f.instructionCount) :
    guestProgram.fetch (addressOfIndex (f.entryPc + i)) = some (f.instructionAt
        i).toLeanIsaInstruction :=
  guestProgram_eq ▸ assemble_fetch functions_consecutive (by have := codeLen_lt; omega) hf hi

/-- `guest_fetch` at a pc and an instruction given as literals: each side condition is one
small evaluation (`decide +kernel`). -/
theorem guest_fetch_of {f : CompiledFunction} (hf : f ∈ Data.functions) {i pc : ℕ} {ins :
    OffsetInstruction}
    (hi : i < f.instructionCount) (hpc : f.entryPc + i = pc) (hins : f.instructionAt i = ins) :
    guestProgram.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction :=
  guestProgram_eq ▸ assemble_fetch_of functions_consecutive (by have := codeLen_lt; omega) hf hi hpc hins

/-- Function `j` of the table is a guest function. -/
theorem mem_functions {j : ℕ} {f : CompiledFunction} (h : Data.functions[j]? = some f) :
    f ∈ Data.functions :=
  List.mem_of_getElem? h

/-- Every pc of a guest function is before the last slot. -/
theorem guest_pc_lt {f : CompiledFunction} (hf : f ∈ Data.functions) {i : ℕ} (hi : i <
    f.instructionCount) :
    f.entryPc + i < 2 ^ guestProgram.logSize - 1 :=
  Nat.lt_of_lt_of_le (lookup_of_mem functions_consecutive hf hi).2.2 (Nat.le_of_lt codeLen_lt)

/-- Past the functions, the guest holds the padding. -/
theorem guest_fetch_pad {pc : ℕ} (hpc : Data.codeLen ≤ pc) (hpc' : pc < 2 ^ 19) :
    guestProgram.fetch (addressOfIndex pc) = some OffsetInstruction.padding.toLeanIsaInstruction :=
  guestProgram_eq ▸ assemble_fetch_pad functions_consecutive hpc hpc'

end
end LeanVM.Guest
