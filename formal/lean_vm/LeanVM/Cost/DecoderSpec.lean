module

public import LeanVM.Cost.DecoderSize
public import LeanVM.Cost.Decoder.TopEq
public import LeanVM.Guest.DecoderProgram

/-!
# The guest decoder program and its specification

`compiledGuestWitnessDecoder`: the entry (`decoderEntryBody`, `Cost/DecoderProgram.lean`), then the compiled
top's bodies (`decTopC`, `Decoder/Top.lean`). On every valid execution `t` of the guest, its
output is the encoding of the deployed decoder's decoding `End.decode t.memory`: the entry runs
the top on the program, `κ` and the memory vector (`outputWithin_decoderEntry`), the top's spec
gives its value (`decTopC.costSpec`), which is `End.decode` (`decTop_eq`). Its size is within
`guestWitnessDecoderSizeBound` (`Cost/DecoderSize.lean`).

Its price within the budget (`DecoderPriceWithinBudget`, `guestWitnessDecoderBudget`) is a hypothesis
here, so that this module does not import the cost bounds; `Cost/Bounds/Guest/Budget.lean` proves
it (`LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget`), and `LeanVM.lean` composes the two.
-/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Cost.Decoder LeanVM.Node

public section

/-- **The guest decoder program**: the entry at `0`, then the compiled top's bodies. -/
@[expose] def compiledGuestWitnessDecoder : MachineProgram := decoderProgramOf decTopC.costIdx
    decTopC.costDeps

/-- The program holds the top's bodies. -/
theorem decoderProgram_includes : Includes compiledGuestWitnessDecoder decTopC.costDeps :=
  decoderProgramOf_includes decoderProgram_indices_increasing

/-- The program's function `0` is the entry. -/
theorem decoderProgram_entry : compiledGuestWitnessDecoder[0]? = some (decoderEntryBody
    decTopC.costIdx) :=
  decoderProgramOf_entry decoderProgram_indices_increasing

/-- **The program's size** is within `guestWitnessDecoderSizeBound`. -/
theorem decoderProgram_size_le : compiledGuestWitnessDecoder.size ≤ guestWitnessDecoderSizeBound :=
  decoderProgram_size_le_measured.trans (by unfold guestWitnessDecoderSizeBound; decide +kernel)

/-- **The program's price** on an execution: the top's on the program, `κ` and the memory vector,
and the entry's `13`. -/
@[expose] noncomputable def decoderProgramPrice (prog : LeanIsaProgram) (t : Execution prog) : ℕ :=
  machineCost compiledGuestWitnessDecoder decTopC.costIdx
    [encodeValue prog, encodeValue t.logMemorySize, encodeValue (memoryVector t.memory)] + 13

/-- **The deployed decoder, on executions**: `End.decode` of the memory. A constant, so that the
specification's field reads `memoryDecoder t` as stated here (the kernel, matching
`encodeValue ((fun t ↦ …) t)` with `encodeValue (End.decode t.memory)`, would unfold the
encoding, then the decoder, before reducing the redex). -/
noncomputable def memoryDecoder (t : Execution LeanVM.Guest.guestProgram) : SeedStatementAndWitness :=
  LeanVM.Guest.End.decode t.memory

/-- **The program computes the deployed decoder**, within any budget covering its price. -/
theorem outputWithin_decoderProgram (t : Execution LeanVM.Guest.guestProgram) {b : ℕ}
    (hb : decoderProgramPrice LeanVM.Guest.guestProgram t ≤ b) :
    outputWithin compiledGuestWitnessDecoder guestWitnessDecoderSizeBound b
        (encodeGuestWitnessDecoderInput LeanVM.Guest.guestProgram t) =
      some (encodeValue (memoryDecoder t)) := by
  have h : memoryDecoder t = decTop LeanVM.Guest.guestProgram t.logMemorySize (memoryVector t.memory) :=
    (decTop_eq t.memory).symm
  rw [h]
  exact outputWithin_decoderEntry decoderProgram_size_le decoderProgram_entry LeanVM.Guest.guestProgram t
    (decTopC.costSpec compiledGuestWitnessDecoder decoderProgram_includes LeanVM.Guest.guestProgram t.logMemorySize
      (memoryVector t.memory)) hb

/-- **The decoder program's price is within its budget** on every valid execution of the guest
(`guestWitnessDecoderBudget`, `Statement/LeanVmGuest.lean`): the fact the decoder's specification takes,
proved by `LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget` (`Cost/Bounds/Guest/Budget.lean`). -/
@[expose] def DecoderPriceWithinBudget : Prop :=
  ∀ input (t : Execution LeanVM.Guest.guestProgram), ValidExecution LeanVM.Guest.guestProgram input t →
    decoderProgramPrice LeanVM.Guest.guestProgram t ≤ guestWitnessDecoderBudget t

/-- The specification for `memoryDecoder`. -/
theorem decoderProgram_spec_memoryDecoder (hprice : DecoderPriceWithinBudget) :
    LeanVM.Guest.End.DecoderProgramSpec compiledGuestWitnessDecoder memoryDecoder :=
  ⟨decoderProgram_size_le, fun input t hv ↦ outputWithin_decoderProgram t (hprice input t hv)⟩

/-- **The decoder program's specification**, its price within the budget given
(`DecoderPriceWithinBudget`, proved in `Cost/Bounds/Guest/Budget.lean`). -/
theorem decoderProgram_spec (hprice : DecoderPriceWithinBudget) :
    LeanVM.Guest.End.DecoderProgramSpec compiledGuestWitnessDecoder fun t ↦ LeanVM.Guest.End.decode
        t.memory :=
  (show memoryDecoder = fun t ↦ LeanVM.Guest.End.decode t.memory from rfl) ▸
    decoderProgram_spec_memoryDecoder hprice

end

end LeanVM.Cost
