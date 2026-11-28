/-
  LeanVM.Prover.Complete.Link.BalanceArrays

  The index side's targets on the honest witness: the memory's address table and words, and the
  program side's targets at an instruction.
-/

module

public import LeanVM.Prover.Complete.Link.BalanceSum
public import LeanVM.Prover.Complete.Link.Steps

/-!
# The targets on the honest witness

At a cell `j` of the memory, the address table `Y` is `γ_addr·g^j + γ_word·M(j) + γ_pres` and the
words are `M(j)` (`idxAt_Y`, `idxAt_words`); at an instruction `σ`, `X_ω` and `P_fp` are its slots
under its opcode's table's weights (`idxAt_X`, `idxAt_P`).
-/

@[expose] public section

namespace LeanVM.Prover.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Prover

theorem idxAt_three (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    idxAt W ch 3 j = (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦
      if j.val < 2 ^ W.layout.logMemory then
        ch.gammaMem.getD 0 0 * ((powers gen (2 ^ W.chunks.width)).toArray.getD j 0) +
          ch.gammaMem.getD 1 0 * ofK ((W.cols.getD memory0 #[]).getD j 0) +
          ch.gammaMem.getD 2 0 * ofK ((W.cols.getD memory1 #[]).getD j 0) + ch.gammaMem.getD 3 0
      else ch.gammaMem.getD 0 0 * ((powers gen (2 ^ W.chunks.width)).toArray.getD j 0)).getD j 0 :=
  rfl

theorem idxAt_ten (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    idxAt W ch 10 j = (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦
      if j.val < 2 ^ W.layout.logMemory then
        ofK ((W.cols.getD memory0 #[]).getD j 0) + eY * ofK ((W.cols.getD memory1 #[]).getD j 0)
      else 0).getD j 0 :=
  rfl

/-- The program's instruction count, as the index side reads it. -/
def bcN (W : Witness) : ℕ := W.layout.bytecode.toArray.size >>> bytecodeSlotBits

/-- Slot `s` of instruction `j`, as the index side reads it. -/
def bcSlot (W : Witness) (s j : ℕ) : K := W.layout.bytecode.toArray.getD (s * bcN W + j) 0

/-- `g^j`, as the index side reads it. -/
def gjAt (W : Witness) (j : ℕ) : E := (powers gen (2 ^ W.chunks.width)).toArray.getD j 0

/-- The program side's weights. -/
def wts (ch : LinkChallenges) : SlotWeights :=
  slotWeights tables ch.slot (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0) ch.mu ch.etaMem ch.etaBc

theorem idxAt_five (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    idxAt W ch 5 j = (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦
      if j.val < bcN W then
        ch.etaBc * ch.slot.getD 1 0 * gjAt W j + ch.etaBc * ch.slot.getD 2 0 +
          sumE ((List.range (2 ^ bytecodeSlotBits - 3)).map fun i ↦
            ((wts ch).omega.getD (opcodeOf (bcSlot W 3 j)) []).getD (i + 3) 0 * ofK (bcSlot W (i + 3) j) +
            ((wts ch).pc.getD (opcodeOf (bcSlot W 3 j)) []).getD (i + 3) 0 *
              (gjAt W j * ofK (bcSlot W (i + 3) j)))
      else ch.etaBc * ch.slot.getD 1 0 * gjAt W j).getD j 0 :=
  rfl

theorem idxAt_twelve (W : Witness) (ch : LinkChallenges) (j : ℕ) :
    idxAt W ch 12 j = (Array.ofFn (n := 2 ^ W.chunks.width) fun j ↦
      if j.val < bcN W then
        sumE ((List.range (2 ^ bytecodeSlotBits - 4)).map fun i ↦
          ((wts ch).frame.getD (opcodeOf (bcSlot W 3 j)) []).getD (i + 4) 0 * ofK (bcSlot W (i + 4) j))
      else 0).getD j 0 :=
  rfl

end LeanVM.Prover.Complete

end
