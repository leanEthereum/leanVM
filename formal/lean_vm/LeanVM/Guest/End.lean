/-
  LeanVM.Guest.End

  The guest's bytecode and the start of a valid execution's memory: the public input's cells as
  `main` loads them.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Guest.Core
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.B1.Main.Interface

/-!
# The bytecode and the public input

* `bytecode`: the guest's stacked bytecode, as the verifier and `NodeRelation` read it;
  `bytecode_length`: `2^(19 + BYTECODE_SLOT_BITS)` words, the length `B1.Main.SubSoundW` asks.
* `pub_loads`: a valid execution's memory holds the two cells of the public input's digest at
  `g^0`, `g^1`, as `main` loads them through the pointer `1` (`LoadHolds rd 1 0`,
  `LoadHolds rd 1 1`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

@[expose] public section

/-- The guest's bytecode, as the verifier and `NodeRelation` read it. Noncomputable: compiled, it
would be evaluated when a program importing it starts. -/
noncomputable abbrev bytecode : List K := bytecodeWords guestProgram

/-- The guest's bytecode has `2^(19 + BYTECODE_SLOT_BITS)` words, sixteen slots of `2^19`
instructions. -/
theorem bytecode_length : bytecode.length = 2 ^ (B1.Main.bytecodeLog + bytecodeSlotBits) := by
  have h : bytecode.length = 16 * 2 ^ guestProgram.logSize := by
    simp [bytecode, bytecodeWords, List.length_flatMap]
    omega
  rw [h, guest_logSize]
  decide +kernel

theorem one_eq_ofK : (1 : E) = ofK 1 := rfl

/-- A word of the memory at `g^i` is a load through the pointer `1` at offset `i`. -/
theorem loadHolds_one {rd : Reader} {i : ℕ} {d : E} (h : rd (addressOfIndex i) = some d) :
    LoadHolds rd 1 i d := by
  refine ⟨(isInK_iff 1).mpr ⟨1, one_eq_ofK⟩, ?_⟩
  rw [one_eq_ofK, limb_ofK]
  simpa using h

/-- The digest's halves are the public input's two memory words. -/
theorem digestHalves_publicInputDigest (input : PublicInput) :
    digestHalves (publicInputDigest input) = (input.word0, input.word1) := by
  simp [digestHalves, publicInputDigest, PublicInput.word0, PublicInput.word1, K.ofLane_lane]

/-- **The public input's cells**: a valid execution's memory holds the two cells of the public
input's digest at `g^0` and `g^1`. -/
theorem pub_loads {input : PublicInput} {t : Execution guestProgram}
    (hv : ValidExecution guestProgram input t) :
    LoadHolds t.memory.read 1 0 (digestHalves (publicInputDigest input)).1 ∧
      LoadHolds t.memory.read 1 1 (digestHalves (publicInputDigest input)).2 := by
  obtain ⟨⟨-, -, h0, h1⟩, -⟩ := hv
  rw [digestHalves_publicInputDigest input]
  exact ⟨loadHolds_one h0, loadHolds_one h1⟩

end
end LeanVM.Guest.End
