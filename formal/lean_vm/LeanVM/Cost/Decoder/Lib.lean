module

public import LeanVM.Cost.AS.Top
public import LeanVM.Protocol.Extraction.Fast.Address
public import LeanVM.Guest.Core

/-!
# The guest decoder's data, for the compiler

The decoder's compiled chain follows the knowledge extractor's (`Cost/AS/Top.lean`, its last
compiled module): the compiler allocates function indices from what a module imports, so the two
chains share their library functions and never allocate one index twice. This module registers what
the decoder needs beyond the extractor's encodings and rewrites (`Cost/FastLib.lean`,
`Cost/Extractor/Top.lean`), after the extractor's bodies are compiled, so it changes none of them:
the encodings of the machine's registers and of the guest's value names, the rewrites of three
decided propositions of the machine's step, and the measure of the address tables' search.
-/

namespace LeanVM.Cost.FastLib

open LeanVM.Cost LeanVM.Extraction.Fast LeanVM.Parameters

@[expose] public section

cost_enc LeanVM.Semantics.Registers
-- the guest's value names, for the guest decoder's readers (a `Seg.i` names its callee by a string)
cost_enc LeanVM.Guest.Core.Seg
cost_enc LeanVM.Guest.Core.V

/-- Equality of registers: of both fields. -/
theorem decideEqRegisters {F : Type} [DecidableEq F] (x y : LeanVM.Semantics.Registers F)
    {inst : Decidable (x = y)} : @decide (x = y) inst = (decide (x.pc = y.pc) && decide (x.fp = y.fp)) := by
  obtain ⟨_, _⟩ := x; obtain ⟨_, _⟩ := y; simp

cost_rewrite decideEqRegisters

/-- Membership in `K`: the upper limb zero. -/
theorem decideIsInK (x : E) {inst : Decidable (IsInK x)} :
    @decide (IsInK x) inst = decide (x.limb 1 = 0) :=
  decide_eq_decide.2 Iff.rfl

cost_rewrite decideIsInK

open LeanVM.Semantics in
/-- The Keccak relation: each cell past those written, or the permuted state's. -/
theorem decideKeccakCells (input : Fin 13 → E) (inOdd : Bool) (output : Fin 13 → E) (outOdd : Bool)
    (outCells : KeccakOutputCells)
    {inst : Decidable (KeccakCellsRelation input inOdd output outOdd outCells)} :
    @decide (KeccakCellsRelation input inOdd output outOdd outCells) inst =
      decide (∀ c : Fin 13, outCells.cellCount ≤ c.val ∨
          output c = cellsOfState (keccakF1600 (stateOfCells input inOdd)) outOdd c) :=
  decide_eq_decide.2 (forall_congr' fun _ ↦ by rw [imp_iff_not_or, Nat.not_lt])

cost_rewrite decideKeccakCells

cost_measure findLane := fun _ _ lo hi ↦ hi - lo

end

end LeanVM.Cost.FastLib
