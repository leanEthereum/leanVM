module

public import Statement.LeanVmGuest

/-!
# The guest decoder as a program: from its specification to `GuestKnowledgeSoundness`

`GuestKnowledgeSoundness D` (`Statement/LeanVmGuest.lean`) takes the decoder as a cost-machine
program `D`, run within `guestWitnessDecoderBudget` on the encoded execution, its output the
encoding of a decoding. The proofs read a decoding off an execution's memory (`MemoryDecoder`;
`MemoryGuestKnowledge guest decode`: every valid execution's memory decodes to a decoding that
explains the public input). Two facts relate them:

* **`DecoderProgramSpec D decoder`**: `D`'s size is within `guestWitnessDecoderSizeBound`, and on
  every valid execution `D` outputs, within its budget, the encoding of `decoder`'s decoding;
* **`DecoderExplains decoder`**: on every valid execution, `decoder`'s decoding explains the public
  input (`ExplainsPublicInput`); for a decoder of memories it is `MemoryGuestKnowledge`.

From them, **`guestKnowledge_of_spec : GuestKnowledgeSoundness D`**, and
**`guestKnowledge_of_memory`** for a program computing a decoder of memories.
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **A decoder of memories**: from a memory, a seed, a statement and a witness. The statement's
decoder is a cost-machine program (`GuestKnowledgeSoundness`, `Statement/LeanVmGuest.lean`); this is
the proofs' form, which `DecoderProgramSpec` relates to it. -/
abbrev MemoryDecoder : Type := ∀ {κ : ℕ}, MemoryImage κ → SeedStatementAndWitness

/-- **Knowledge soundness of the guest program, for a decoder of memories**: from the memory of
every valid execution of `guest` on a public input, `decode` reads a seed, the node statement the
input commits to under that seed, and a witness proving it (`ExplainsPublicInput`). -/
def MemoryGuestKnowledge (guest : LeanIsaProgram) (decode : MemoryDecoder) : Prop :=
  ∀ input (t : Execution guest), ValidExecution guest input t →
    ExplainsPublicInput guest input (decode t.memory)

end

end LeanVM.Node

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Cost

@[expose] public section

/-- **What the guest decoder program must satisfy**, for a decoder of executions `decoder`: its
size is within `guestWitnessDecoderSizeBound`, and on every valid execution of the guest it
outputs, within its budget, the encoding of `decoder`'s decoding. -/
structure DecoderProgramSpec (decoderProgram : Cost.MachineProgram)
    (decoder : Execution guestProgram → SeedStatementAndWitness) : Prop where
  /-- The size bound. -/
  size : decoderProgram.size ≤ guestWitnessDecoderSizeBound
  /-- The program computes `decoder` within its budget on every valid execution. -/
  computes : ∀ input (t : Execution guestProgram), ValidExecution guestProgram input t →
    outputWithin decoderProgram guestWitnessDecoderSizeBound (guestWitnessDecoderBudget t)
        (encodeGuestWitnessDecoderInput guestProgram t) = some (encodeValue (decoder t))

/-- **The decoder's decodings explain the public input**: on every valid execution of the guest
on a public input, `decoder`'s decoding explains it (`ExplainsPublicInput`). -/
def DecoderExplains (decoder : Execution guestProgram → SeedStatementAndWitness) : Prop :=
  ∀ input (t : Execution guestProgram), ValidExecution guestProgram input t →
    ExplainsPublicInput guestProgram input (decoder t)

/-- **`GuestKnowledgeSoundness` of the decoder program**, from its spec and its decoder's decodings
explaining the input. -/
theorem guestKnowledge_of_spec {decoderProgram : Cost.MachineProgram}
    {decoder : Execution guestProgram → SeedStatementAndWitness}
    (h : DecoderProgramSpec decoderProgram decoder) (hx : DecoderExplains decoder) :
    GuestKnowledgeSoundness decoderProgram :=
  fun input t hv ↦ ⟨decoder t, h.computes input t hv, hx input t hv⟩

/-- **`GuestKnowledgeSoundness` of a program that computes a decoder of memories** that explains
every valid execution. -/
theorem guestKnowledge_of_memory {decoderProgram : Cost.MachineProgram} {decode : MemoryDecoder}
    (h : DecoderProgramSpec decoderProgram fun t ↦ decode t.memory)
    (hx : MemoryGuestKnowledge guestProgram decode) : GuestKnowledgeSoundness decoderProgram :=
  guestKnowledge_of_spec h hx

end

end LeanVM.Guest.End
