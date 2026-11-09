import LeanVM.Cost.Extractor.PMLane

/-!
# Tests: the additive NTT, as compiled on the chain

`novelFwd` and `novelInv` (`Protocol/Extraction/Extractor.lean` §4) are compiled on demand in
`Cost/Extractor/PMLane.lean` (`laneEncodedWith pmSolver`): `novelFwd.c228` (its stages
`novelFwdStage.c230`, twiddles `novelTwiddles.c205`), and `novelInv` inlined into
`toNovelFast.c667` (its fold's closure `fastStacksFastC.lam1.lam0`, stages `novelInvStage.c204`);
bounded in `Cost/Bounds/FastPath.lean`
(`novelFwd_cost`, `novelInv_cost`). Here: their values on small inputs.
-/

namespace LeanVMTests.Cost.Ntt

open LeanVM.Cost LeanVM.Cost.Library LeanVM.Parameters LeanVM.Extraction

def run (deps : List (ℕ × Term)) (i : ℕ) (args : List MachineValue) : Option (MachineValue × ℕ) :=
  evaluateFunctionBody (MachineProgram.ofList deps) 1000000 i args

def coeffs (κ : ℕ) : Array K := Array.ofFn fun v : Fin (2 ^ κ) ↦ K.ofBits (v.val * 2654435761 % 1000003)

#guard (run Auto.LeanVM.Extraction.novelFwd.c228.costDeps Auto.LeanVM.Extraction.novelFwd.c228.costIdx
    [MachineEncoding.encodeValue (4 : ℕ), MachineEncoding.encodeValue (1 : ℕ),
      MachineEncoding.encodeValue (coeffs 4)]).map (·.1) ==
  some (MachineEncoding.encodeValue (novelFwd 4 1 (coeffs 4)))

#guard (run (LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costDeps ++ listFoldl.costDeps) listFoldl.costIdx
    [.closure LeanVM.Cost.Extractor.fastStacksFastC.lam1.lam0.costIdx [MachineEncoding.encodeValue (4 : ℕ)],
      MachineEncoding.encodeValue (coeffs 4), MachineEncoding.encodeValue (List.range 4)]).map (·.1) ==
  some (MachineEncoding.encodeValue (novelInv 4 (coeffs 4)))

end LeanVMTests.Cost.Ntt
