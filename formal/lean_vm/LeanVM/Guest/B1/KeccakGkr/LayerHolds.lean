/-
  LeanVM.Guest.B1.KeccakGkr.LayerHolds

  `keccak_layer`'s two specializations meet `MeaningKeccakLayer`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerProof
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight0
public import LeanVM.Guest.B1.KeccakGkr.LayerBody264
public import LeanVM.Guest.B1.KeccakGkr.LayerBody265

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem find_layer264 : coreProgram.find? "keccak_layer__L1" = some Data.core263 :=
  Program.find?_of_indexOf? (j := 263) (by decide +kernel) rfl
theorem find_layer265 : coreProgram.find? "keccak_layer__L0" = some Data.core264 :=
  Program.find?_of_indexOf? (j := 264) (by decide +kernel) rfl

/-- **`keccak_layer`**, given the later claims' weight section. -/
theorem keccak_layer_holds_of (hW0 : WeightOk 0) : keccak_layer_Spec := by
  intro first hf rd args rets h
  interval_cases first
  · exact layer_sound (first := 0) (by decide) hW0 find_layer265 layer_body265 rfl rd args rets h
  · exact layer_sound (first := 1) (by decide) weightOk_one find_layer264 layer_body264 rfl rd args
      rets h

/-- **`keccak_layer`** (G:2694-2875; TRIAGE #60): its two specializations compute their
meanings. -/
theorem keccak_layer_holds : keccak_layer_Spec := keccak_layer_holds_of weightOk_zero

end
end LeanVM.Guest.B1.VerifySub
