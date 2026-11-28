/-
  LeanVM.Guest.B1.VsC.VkPI

  `verify_keccak` placed: each layer completes where it is placed (`lp_spec`), from
  `KeccakLayerCompleteA`.
-/

module

public import LeanVM.Guest.B1.VsC.VkPH
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The layers, placed

`lp_exists`: layer `s` completes at any frame (`KeccakLayerCompleteA` on `VkData.layer s`, its
arrays in `verify_keccak`'s buffers, the stream, the window table and the previous layer's
buffers); `lp_spec`: at its chosen position.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

namespace VkData

variable {D : VkData} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
variable {c curE chiE olE zvE slE tbE : ℕ}

theorem firstOf_lt (s : ℕ) : firstOf s < 2 := by unfold firstOf; split <;> omega

theorem cap_eq (h : D.Ok) {s : ℕ} (hs : s < 12) :
    (D.layer s).cap = [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0, (D.layer s).cap.getD 2 0,
      (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0] := by
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := five_of_length' (D.layer_cap h hs)
  rw [hf]; rfl

theorem lcur_le (h : D.Ok) {s : ℕ} (hs : s < 12) :
    D.lcur s + (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length ≤
      D.xs.length := by
  have hl : (VsC.klXs (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2).length =
      48 + 2 * (D.τ - 3) + 36 := ltXs_length h hs
  rw [hl, xs_len h]
  simp only [lcur]
  have : s * (48 + 2 * (D.τ - 3) + 36) + (48 + 2 * (D.τ - 3) + 36) ≤ 12 * (48 + 2 * (D.τ - 3) + 36) := by
    nlinarith
  omega

theorem inRegion_ptr {arrs : List (E × ℕ)} {R : ℕ → Prop}
    (h : ∀ q ∈ arrs, ∃ a, q.1 = VsC.ptrAtV a ∧ ∀ t < q.2, R (a + t)) : VsC.InRegion arrs R := by
  intro q hq t ht
  obtain ⟨a, ha, hb⟩ := h q hq
  exact ⟨a + t, by rw [ha]; exact ptr_addr a t, hb t ht⟩

set_option maxRecDepth 20000 in
/-- **Layer `s` completes at any frame `fp`.** -/
theorem lp_exists (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok) {s : ℕ} (hs : s < 12)
    (cbp fp : ℕ) : ∃ e, D.LP fs al cert k c curE tbE s cbp fp e := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  obtain ⟨hpl, hg, hpm, hlm, hproj, hfin⟩ := D.layer_facts h hs
  have hy := D.layer_y h hs.le
  have hcap := cap_eq h hs
  have hs0 : (D.layer s).s0 (firstOf s) = plainStart (firstOf s) [(D.layer s).cap.getD 0 0,
      (D.layer s).cap.getD 1 0, (D.layer s).cap.getD 2 0, (D.layer s).cap.getD 3 0,
      (D.layer s).cap.getD 4 0] D.committed := by
    rw [LayerData.s0, ← hcap]; rfl
  rw [hs0] at hg hfin
  have hlc := lcur_le h hs
  have hτ3 : D.τ - 3 + 3 = D.τ := by omega
  have hpt : (D.layer s).c.point.length = D.τ - 3 := hy
  have hreg : VsC.InRegion (D.lArr c curE tbE s cbp) (D.lR c curE tbE s cbp) := by
    apply inRegion_ptr
    intro q hq
    simp only [lArr, VsC.klArrays, recPtrs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · simp only [↓reduceIte] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨_, rfl, fun t ht ↦ ?_⟩
      all_goals simp only [lR, o201, o274, kcSize, keccakLocalBits, lcur] at ht hlc ⊢
      all_goals omega
    · simp only [show s ≠ 0 by omega, ↓reduceIte] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals refine ⟨_, rfl, fun t ht ↦ ?_⟩
      all_goals simp only [lR, o201, kcSize, keccakLocalBits, lcur] at ht hlc ⊢
      all_goals omega
  have hc0 : firstOf s = 1 → ((D.cells s).1, (D.cells s).2) = Keccak.scalarCells D.committed dsObserve :=
    fun h1 ↦ by
      have : s = 0 := by unfold firstOf at h1; split at h1 <;> omega
      subst this
      rw [show D.cells 0 = Keccak.scalarCells D.committed dsObserve by simp [cells]]
  have hnext : (D.layer s).next (firstOf s) = layerClaim (D.layer s).c (plainStart (firstOf s)
      [(D.layer s).cap.getD 0 0, (D.layer s).cap.getD 1 0, (D.layer s).cap.getD 2 0,
        (D.layer s).cap.getD 3 0, (D.layer s).cap.getD 4 0] D.committed)
      (D.T s).1 (D.T s).2.1 (D.T s).2.2.1 (D.T s).2.2.2.1 (D.T s).2.2.2.2 := by
    rw [LayerData.next, hs0]; rfl
  obtain ⟨e, he, hb, hc⟩ := hL (firstOf s) (firstOf_lt s) ((D.layer s).cap.getD 0 0) ((D.layer s).cap.getD 1 0)
    ((D.layer s).cap.getD 2 0) ((D.layer s).cap.getD 3 0) ((D.layer s).cap.getD 4 0) (D.cells s).1
    (D.cells s).2 (VsC.ptrAtV (curE + D.lcur s)) (VsC.ptrAtV (c + D.o201 + 22 * s))
    (VsC.ptrAtV (c + D.o201 + 22 * (s + 1))) (keccakIota D.τ s (D.layer s).c) (VsC.ptrAtV tbE)
    D.committed (D.recPtrs c s cbp).1 (D.recPtrs c s cbp).2.1 (D.recPtrs c s cbp).2.2.1
    (D.recPtrs c s cbp).2.2.2 (D.τ - 3) s (D.layer s).c (D.T s).1 (D.T s).2.1 (D.T s).2.2.1
    (D.T s).2.2.2.1 (D.T s).2.2.2.2 (D.lR c curE tbE s cbp) fp (by omega) (by omega)
    hpl (hpm.trans hy) hlm hg (by rw [hτ3]; exact hproj) hfin hc0 (by rw [hτ3]) hpt hreg
  refine ⟨e, ?_⟩
  unfold LP
  rw [hnext]
  exact ⟨he, hb, hc⟩

/-- **Each layer completes at its own position.** -/
theorem lp_spec (hL : VsC.KeccakLayerCompleteA fs al cert k) (h : D.Ok) {s : ℕ} (hs : s < 12) :
    D.LP fs al cert k c curE tbE s (D.posP fs al cert k c curE tbE s).2
      (D.lfp fs al cert k c curE tbE s) (D.posP fs al cert k c curE tbE (s + 1)).1 :=
  Classical.epsilon_spec (lp_exists hL h hs _ _)

/-- The previous layer's buffers are layer `s - 1`'s. -/
theorem posP_snd (s : ℕ) :
    (D.posP fs al cert k c curE tbE (s + 1)).2 = D.lsP fs al cert k c curE tbE s := rfl

end VkData

end
end LeanVM.Guest.B1.VerifySub
