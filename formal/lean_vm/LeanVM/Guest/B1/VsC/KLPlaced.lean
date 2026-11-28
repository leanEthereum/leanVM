/-
  LeanVM.Guest.B1.VsC.KLPlaced

  **`keccak_layer` completes placed** on a layer's honest data.
-/

module

public import LeanVM.Guest.B1.VsC.KLPlacedA
public import LeanVM.Guest.B1.VsC.KRoundsAll
public import LeanVM.Guest.B1.VsC.RoundsC1
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds
public import LeanVM.Guest.B1.Bits.GrindWin
public import LeanVM.Guest.Complete.ComposeRd
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# `keccak_layer`, placed

`layer_placed`: `keccak_layer__L{first}` at frame `fp`, its cursor `cb = fp + fs name` right past
its frame, on a layer's honest data. Its node is `callAtA_nodeRd`'s: the valuation on each memory
the forward evaluation `layerσ` with the oracle `layerW` (its `HeapBuf`s at `cb`, `cb + y`,
`cb + y + 11`, `cb + y + 36`, the dispatches' honest returns, the honest windows); before the memory
`σ0`, the empty memory's patched with the honest values the dispatches read. Its two dispatches
enter `layer_rounds__L{16⌊y/16⌋}` and `__L{y mod 16}` (`layer_rounds_placed`) one after the other
past its `HeapBuf`s; its events hold by `layer_body_complete` (`walk_sat`), its `grind_check`'s
hints are exact (`gcInline_exact_of_shape`), every load is in the caller's arrays or its buffers.
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Addresses -/

theorem addr_gen (p : E) (m t : ℕ) :
    (p * gen ^ m).limb 0 * addressOfIndex t = p.limb 0 * addressOfIndex (m + t) := by
  rw [gen_pow_eq_ofK, limb0_mul_ofK, mul_assoc]
  congr 1
  simp only [Parameters.addressOfIndex, pow_add]

theorem ptr_addr (a t : ℕ) : (VsC.ptrAtV a).limb 0 * addressOfIndex t = addressOfIndex (a + t) := by
  simp [VsC.ptrAtV, addressOfIndex, pow_add]

theorem reg_of {arrs : List (E × ℕ)} {fp : ℕ} {R : ℕ → Prop} (hpb : VsC.PtrsBelow arrs fp)
    (hR : ∀ i, VsC.ptrRegion arrs i → R i) {q : E × ℕ} (hq : q ∈ arrs) {t : ℕ} (ht : t < q.2) :
    ∃ i, q.1.limb 0 * addressOfIndex t = addressOfIndex i ∧ R i := by
  obtain ⟨i, -, hi⟩ := hpb q hq t ht
  exact ⟨i, hi, hR i ⟨q, hq, t, ht, hi⟩⟩

/-! ## The function and its straight body -/

theorem layer_fn {first : ℕ} (hf : first < 2) : ∃ fn, coreProgram.find? (layerName first) = some fn ∧
    fn.body = layerT first ∧ fn.params = (List.range 15).map V.n := by
  interval_cases first
  · exact ⟨_, find_layer265, layer_body265, rfl⟩
  · exact ⟨_, find_layer264, layer_body264, rfl⟩

theorem isAtom_aoc {s : Stmt} (h : isAtom s = true) : VsC.atomOrCall s = true := by
  cases s <;> simp_all [isAtom, VsC.atomOrCall]

theorem lPre_aoc {first : ℕ} (hf : first < 2) (j1 j2 : ℕ) :
    (lPre first j1 j2).all VsC.atomOrCall = true := by
  have h := layer_atoms1 hf
  simp only [lAtoms, List.all_append, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [lPre, List.all_append, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨fun s hs ↦ isAtom_aoc (h1 s hs), ?_⟩, fun s hs ↦ isAtom_aoc (h2 s hs)⟩, ?_⟩,
    fun s hs ↦ isAtom_aoc (h3 s hs)⟩ <;> simp [VsC.atomOrCall]

theorem lPre_filterMap {α : Type} {f : Stmt → Option α} (hf : ∀ g a r, f (.call g a r) = none)
    (first j1 j2 : ℕ) : (lPre first j1 j2).filterMap f = (lAtoms first).filterMap f := by
  simp [lPre, lAtoms, List.filterMap_append, hf]

theorem lPre_calls {first : ℕ} (hf : first < 2) (j1 j2 : ℕ) :
    (lPre first j1 j2).filterMap Stmt.callS =
      [(none, stepNames.getD j1 "", lA1 (preOff first), lR1 (preOff first)),
        (none, remNames.getD j2 "", lA2 (preOff first), lR2 (preOff first))] := by
  obtain ⟨-, -, h⟩ := layer_atoms5 hf
  simp only [lAtoms, List.filterMap_append, List.append_eq_nil_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp [lPre, List.filterMap_append, h1, h2, h3, Stmt.callS]

theorem stepNames_lr {j : ℕ} (hj : j < 2) : stepNames.getD j "" = lrNames.getD (krStep * j) "" := by
  interval_cases j <;> rfl

theorem remNames_lr {j : ℕ} (hj : j < 16) : remNames.getD j "" = lrNames.getD j "" := by
  interval_cases j <;> rfl

end
end LeanVM.Guest.B1.VerifySub.KL
