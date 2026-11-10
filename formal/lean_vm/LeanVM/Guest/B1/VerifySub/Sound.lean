/-
  LeanVM.Guest.B1.VerifySub.Sound

  **`verify_sub` is sound**: a run of its body gives a child proof, read off its valuation,
  the memory and the frame map, that the deferring verifier accepts.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundOf
public import LeanVM.Guest.B1.Whir.Sound
public import LeanVM.Guest.B1.Main.SoundVX

/-!
# `verify_sub` is sound

`verify_sub_sound_w`: `verify_sub_sound_of` with `open_stacked`'s soundness
(`Whir.open_stacked_sound_w`): for a bytecode of `2^23` words, on a memory image of at most `2^32`
words, under any call relation below `coreProgram.Rel` that unfolds at the frame map `V`, a run of
`verify_sub`'s body under `VerifySubPre` returns nothing, and the deferring verifier accepts the
child proof `vsPiOf L.read σ V` for the statement at its arguments: `Main.SubSoundW bytecode
vsPiOf`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1

@[expose] public section

/-- **`verify_sub` is sound**, its child proof read off its valuation, the memory and the frame
map. -/
theorem verify_sub_sound_w (bytecode : List K) : Main.SubSoundW bytecode vsPiOf :=
  fun hbl _ L hκ C V hU hLe σ rets hb hpre ↦
    verify_sub_sound_of Whir.open_stacked_sound_w bytecode hbl L hκ C V hU hLe σ rets hb hpre

end
end LeanVM.Guest.B1.VerifySub
