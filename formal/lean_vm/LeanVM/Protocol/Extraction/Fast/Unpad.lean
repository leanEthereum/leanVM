module

public import LeanVM.Protocol.Extraction.Extractor
import LeanVM.Protocol.Rpm.Paths
import Common.Sponge
public import Common.Defs
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-!
# Unpadding in one pass

The statement's `keccakUnpadded bs` tries the `136` prefixes of `bs` short of `1` to `136` bytes,
padding each and comparing with `bs`: about `3·136·|bs|` byte operations. `keccakUnpaddedFast`
strips the padding once (`Common.stripPad`: the trailing zeros and the padding's two bytes), pads
the result and compares: about `3·|bs|`.

* **`keccakUnpaddedFast_eq`**: `keccakUnpaddedFast bs = keccakUnpadded bs`, on every input, from
  the statement's decoder (`Rpm.unpad_eq_some_iff`, `Protocol/Rpm/Paths.lean`).
-/

namespace LeanVM.Extraction.Fast

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile Common

public section

/-- **`keccakUnpadded`, in one pass**: strip the padding, pad the result back, compare. -/
@[expose] def keccakUnpaddedFast (bs : Bytes) : Option Bytes :=
  let m := stripPad bs
  if keccakPadded m = bs then some m else none

/-- Stripping the padding of `keccakPadded m` gives `m`. -/
theorem stripPad_keccakPadded (m : Bytes) : stripPad (keccakPadded m) = m := by
  rw [← Rpm.keccakPadBytes_eq_padded, stripPad_keccakPadBytes]

/-- **One pass unpads as the statement does.** -/
theorem keccakUnpaddedFast_eq (bs : Bytes) : keccakUnpaddedFast bs = keccakUnpadded bs := by
  rw [keccakUnpaddedFast]
  split <;> rename_i h
  · exact ((Rpm.unpad_eq_some_iff _ _).mpr h).symm
  · -- no message pads to `bs`: if one did, stripping `bs` would give it.
    refine (Option.eq_none_iff_forall_ne_some.mpr fun m hm ↦ h ?_).symm
    rw [← (Rpm.unpad_eq_some_iff _ _).mp hm, stripPad_keccakPadded]

theorem keccakUnpaddedFast_eq_fun : keccakUnpaddedFast = keccakUnpadded :=
  funext keccakUnpaddedFast_eq

end

end LeanVM.Extraction.Fast
