/-
  LeanVM.Guest.B1.KeccakGkr.LayerHolds

  `keccak_layer`'s two specializations meet `MeaningKeccakLayer`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerProof
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight0
public import LeanVM.Guest.B1.KeccakGkr.LayerBody264
public import LeanVM.Guest.B1.KeccakGkr.LayerBody265
public import LeanVM.Guest.B1.Bits.Meaning

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem find_layer264 : coreProgram.find? "keccak_layer__L1" = some fn% «keccak_layer__L1» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L1») rfl
theorem find_layer265 : coreProgram.find? "keccak_layer__L0" = some fn% «keccak_layer__L0» :=
  coreProgram_find?_at (j := idx% «keccak_layer__L0») rfl

/-- **`keccak_layer`** on a reader where the inlined `grind_check` of `3` bits is sound. -/
theorem keccak_layer_holds_of (rd : Reader) (hgr : GcSoundOn rd 3) : keccak_layer_Spec rd := by
  intro first hf args rets h
  interval_cases first
  · exact layer_sound (first := 0) (by decide) (weightOk_zero _) find_layer265 layer_body265 rfl rd
      hgr args rets h
  · exact layer_sound (first := 1) (by decide) (weightOk_one _) find_layer264 layer_body264 rfl rd
      hgr args rets h

/-- **`keccak_layer`** (TRIAGE #60): its two specializations compute their meanings
on a memory image. -/
theorem keccak_layer_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ' : winTabBits ≤ κ) (L : MemoryImage κ) :
    keccak_layer_Spec L.read :=
  keccak_layer_holds_of L.read (gcSoundOn_image hκ (le_trans (by decide) hκ') L (by decide))

end
end LeanVM.Guest.B1.VerifySub
