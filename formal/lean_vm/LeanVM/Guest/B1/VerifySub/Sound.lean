/-
  LeanVM.Guest.B1.VerifySub.Sound

  `verify_sub` is sound, from its phases: the ones proved, and the ones still open as hypotheses.
-/

module

public import LeanVM.Guest.B1.VerifySub.Chain
public import LeanVM.Guest.B1.VerifySub.Export
public import LeanVM.Guest.B1.VerifySub.Keccak

/-!
# `verify_sub` is sound, given its open phases

`subSoundW_of`: `Main.SubSoundW bytecode vsPiOf`, from the out-of-domain sample's phase (`PhOod`),
the link's (`PhLink`), the ring switch's (`PhRing`) and the stacked opening's (`PhOpen`); the seed,
the sizes, the root, the Keccak reduction and the export are proved (`phSeed`, `phSizes`,
`phRoot`, `phKeccak`, `phExport`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`verify_sub` is sound**, given the phases still open. -/
theorem subSoundW_of (hOod : PhOod) (hLink : PhLink) (hRing : PhRing) (hOpen : PhOpen)
    (bytecode : List K) : Main.SubSoundW bytecode vsPiOf :=
  subSoundW_of_phases phSeed phSizes phRoot hOod hLink phKeccak hRing hOpen phExport bytecode

end
end LeanVM.Guest.B1.VerifySub
