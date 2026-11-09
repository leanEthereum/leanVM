/-
  LeanVM.Guest.B1.VerifySub.Sound

  **`verify_sub` is sound**: a run of its body gives a child proof, read off its valuation,
  the memory and the frame map, that the deferring verifier accepts.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundOf
public import LeanVM.Guest.B1.Tables.Vt.VerifyTables

/-!
# `verify_sub` is sound

`verify_sub_sound_w`: `verify_sub_sound_w_of` with `verify_tables`' soundness
(`Tables.verify_tables_holds`): for a bytecode of `2^23` words, on a memory image of at most
`2^32` words, under any call relation below `coreProgram.Rel` that unfolds at the frame map `V`, a
run of `verify_sub`'s body with the exponent table at its argument `4` returns nothing, and the
deferring verifier accepts the child proof `vsPiOf L.read σ V` for the statement at its
arguments: `Main.SubSoundW bytecode vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- **`verify_sub` is sound**, its child proof read off its valuation, the memory and the frame
map. -/
theorem verify_sub_sound_w (bytecode : List K) : Main.SubSoundW bytecode vsPiOf :=
  verify_sub_sound_w_of bytecode fun hbl _ hκ L ↦ Tables.verify_tables_holds hκ L bytecode hbl

end
end LeanVM.Guest.B1.VerifySub
