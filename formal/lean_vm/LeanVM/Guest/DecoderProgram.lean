module

public import LeanVM.Guest.EndFinal
public import Statement.Theorems

/-!
# The guest decoder as a program: from its specification to `GuestKnowledgeSoundness`

`GuestKnowledgeSoundness D` (`Statement/LeanVmGuest.lean`) takes the decoder as a cost-machine
program `D`, run within `guestWitnessDecoderBudget` on the encoded execution, its output the encoding of
a decoding. The proofs read a decoding off an execution (`decoder : Execution guest → SeedStatementAndWitness`;
`guest_knowledge` for `decode`, which reads it off the memory). Two facts relate them:

* **`DecoderProgramSpec D decoder`**: `D`'s size is within `guestWitnessDecoderSizeBound`, and on
  every valid execution `D` outputs, within its budget, the encoding of `decoder`'s decoding;
* **`DecoderExplains decoder`**: on every valid execution, `decoder`'s decoding explains the public
  input (`ExplainsPublicInput`); for `decode` it is `guest_knowledge` (`decoderExplains_decode`).

From them, **`guestKnowledge_of_spec : GuestKnowledgeSoundness D`**, the decoding `decoder t`.
For the compiled decoder `LeanVM.Cost.compiledGuestWitnessDecoder` and `decode`, both are proved
(`Cost/DecoderSpec.lean`'s `decoderProgram_spec` with `Cost/Bounds/Guest/Budget.lean`'s
`decoderPriceWithinBudget`; `decoderExplains_decode`), given the walks' obligations
(`EndPending`), which `LeanVM.theorems_hold` takes until their ports land.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Cost

@[expose] public section

/-- **What the guest decoder program must satisfy**, for a decoder of executions
`decoder`: its size is within `guestWitnessDecoderSizeBound`, and on every valid execution of the guest
it outputs, within its budget, the encoding of `decoder`'s decoding. -/
structure DecoderProgramSpec (decoderProgram : Cost.MachineProgram) (decoder : Execution guestProgram → SeedStatementAndWitness) :
    Prop where
  /-- The size bound. -/
  size : decoderProgram.size ≤ guestWitnessDecoderSizeBound
  /-- The program computes `decoder` within its budget on every valid execution. -/
  computes : ∀ input (t : Execution guestProgram), ValidExecution guestProgram input t →
    outputWithin decoderProgram guestWitnessDecoderSizeBound (guestWitnessDecoderBudget t)
        (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue (decoder t))

/-- **The decoder's decodings explain the public input**: on every valid execution of the guest
on a public input, `decoder`'s decoding explains it (`ExplainsPublicInput`). -/
def DecoderExplains (decoder : Execution guestProgram → SeedStatementAndWitness) : Prop :=
  ∀ input (t : Execution guestProgram), ValidExecution guestProgram input t → ExplainsPublicInput guestProgram input (decoder t)

/-- `decode`, read off the memory, explains the public input: `guest_knowledge`. -/
theorem decoderExplains_decode (hP : EndPending) : DecoderExplains fun t ↦ decode t.memory :=
  guest_knowledge hP

/-- **`GuestKnowledgeSoundness` of the decoder program**, from its spec and its decoder's decodings
explaining the input. -/
theorem guestKnowledge_of_spec {decoderProgram : Cost.MachineProgram}
    {decoder : Execution guestProgram → SeedStatementAndWitness} (h : DecoderProgramSpec decoderProgram decoder)
    (hx : DecoderExplains decoder) : GuestKnowledgeSoundness decoderProgram :=
  fun input t hv ↦ ⟨decoder t, h.computes input t hv, hx input t hv⟩

/-- **`GuestKnowledgeSoundness` of a program that computes `decode`**: its spec alone. -/
theorem guestKnowledge_of_decode (hP : EndPending) {decoderProgram : Cost.MachineProgram}
    (h : DecoderProgramSpec decoderProgram fun t ↦ decode t.memory) :
    GuestKnowledgeSoundness decoderProgram :=
  guestKnowledge_of_spec h (decoderExplains_decode hP)

end

end LeanVM.Guest.End
