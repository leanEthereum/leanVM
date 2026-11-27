module

public import NativeRustcArm.SphincsVerify.Parse.Prologue
public import NativeRustcArm.SphincsVerify.Parse.Open

/-!
# The parse's head: from the entry to `b7` (`parseHead_spec : ParseHeadSpec`)

Composed from the prologue (`prologue_spec`, reaching `AtOpen 0` at `b3`) and the openings' loop
(`open_loop`, reaching `AtOpen 24` at `b7`), giving `AtParse7` at `b7`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Parse

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

/-- **The parse's head** (`b0 .. b6`): from the entry, the machine inevitably reaches `b7` with
the key, the randomizer and the FORS openings in the frame. -/
public theorem parseHead_spec [ElfHost] : ParseHeadSpec := by
  intro r hp hc hpre m hm
  subst hm
  refine Eventually.bind_elf (prologue_spec r hp hpre) fun st h ↦ ?_
  refine Eventually.mono_elf (open_loop r hp hc hpre h) fun st ⟨hpc, hF, hM, hR⟩ ↦ ?_
  refine ⟨hpc, hF, hM.1, ?_, hM.2.1, hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1⟩
  rw [openings_eq]
  exact hM.2.2

end NativeRustcArm.SphincsVerifyProof.Parse
