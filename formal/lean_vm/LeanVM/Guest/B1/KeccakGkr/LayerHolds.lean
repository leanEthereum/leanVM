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

theorem find_layer264 : coreProgram.find? "keccak_layer__L1" = some Data.core264 :=
  Program.find?_of_indexOf? (j := 264) (by decide +kernel) rfl
theorem find_layer265 : coreProgram.find? "keccak_layer__L0" = some Data.core265 :=
  Program.find?_of_indexOf? (j := 265) (by decide +kernel) rfl

/-- **`keccak_layer`** on a reader where `grind_check` of `3` bits has its meaning on the window
table. -/
theorem keccak_layer_holds_of (rd : Reader)
    (hgr : ∀ w tabs : E, WinTabs rd tabs → coreProgram.Rel rd (grindCheckName 3) [w, tabs] [] →
      (w.limb 0).lane.toNat % 2 ^ 3 = 0) : keccak_layer_Spec rd := by
  intro first hf args rets h
  interval_cases first
  · exact layer_sound (first := 0) (by decide) (weightOk_zero _) find_layer265 layer_body265 rfl rd
      hgr args rets h
  · exact layer_sound (first := 1) (by decide) (weightOk_one _) find_layer264 layer_body264 rfl rd
      hgr args rets h

/-- **`keccak_layer`** (G:2671-2852; TRIAGE #60): its two specializations compute their meanings
on a memory image, given `grind_check`'s meaning at `3` bits. -/
theorem keccak_layer_holds {κ : ℕ} (hκ : κ ≤ 32) (hκ' : winTabBits ≤ κ) (L : MemoryImage κ)
    (hg : grind_check_Spec 3) : keccak_layer_Spec L.read :=
  keccak_layer_holds_of L.read fun w tabs ht hr ↦ ((hg hκ hκ' L w tabs ht []).mp hr).2

end
end LeanVM.Guest.B1.VerifySub
