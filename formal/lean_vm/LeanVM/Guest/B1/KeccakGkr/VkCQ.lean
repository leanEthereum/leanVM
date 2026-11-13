/-
  LeanVM.Guest.B1.KeccakGkr.VkCQ

  The pointers `verify_keccak` loads through, on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCP

/-!
# The pointers, on the layout

`step_ptrs`: step `s` loads its claim's point's segment coordinate through `stepB s + 1` and, for a
later claim, its flips through each flip's first value; `fin_ptrs`: the inputs' check loads the last claim's
point, local point and lanes through `2250`, `2484`, `3647`. Each is a pointer into the claim's
buffers (`CL`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

/-- Word `k` of claim `s`'s record, through the claim records' pointer. -/
theorem rec_word (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (h201 : σ (.n 161) = ptr (B + D.o201)) {s : ℕ} (hs : s < 12) {k : ℕ} (hk : k < 22) :
    LoadHolds rd (σ (.n 161)) (22 * s + k) ((D.CL B ls s).cw.getD k 0) := by
  have hcw := memL_entry (CL_mem h hm hs) (b := (D.CL B ls s).bclaim) (ws := (D.CL B ls s).cw)
    (by simp [ClaimLay.L])
  have hbc : (D.CL B ls s).bclaim = B + D.o201 + 22 * s := by cases s <;> rfl
  rw [hbc, ← ptr_mul_gen, ← h201] at hcw
  have := ClaimLay.getD_load hcw (k := k) (by rw [(D.CL_ok h B ls hs.le).1]; exact hk)
  exact (loadHolds_mul_gen_pow rd _ _ _ _).1 this

/-- **Step `s`'s pointers.** -/
theorem step_ptrs (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n 18) = gen ^ (D.τ - 4)) (h201 : σ (.n 161) = ptr (B + D.o201)) :
    σ (.n (stepB s + 1)) = ptr (D.CL B ls s).bpp * gen ^ (D.τ - 4) ∧
    (s ≠ 0 → ∀ j < (iotaUsed s).length, σ (.n (stepB s + 6 + 2 * j)) = ptr (D.CL B ls s).bfl) := by
  have hg : ∀ st ∈ stepCore s (stepB s), GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    refine val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_steps s hs st ?_)))))
    rw [stepT_split]; exact List.mem_append_left _ hst
  have gA : ∀ a, Stmt.atom a ∈ stepCore s (stepB s) → Good rd vkSt (D.w B curE) σ a :=
    fun a h ↦ hg _ h
  have mA : ∀ a ∈ [Atom.load (.n (stepB s)) (.n 161) (22 * s + 2),
      .mul (.n (stepB s + 1)) (.n (stepB s)) (.n 18)], Stmt.atom a ∈ stepCore s (stepB s) := by
    intro a ha
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp
  obtain ⟨k1, -, -, k5, -⟩ := step_ker s hs
  obtain ⟨-, -, -, -, -, h2, -, -, -, hw⟩ := D.CL_ok h B ls hs.le
  obtain ⟨-, hbB, -⟩ := step_bounds s hs
  have e0 : σ (.n (stepB s)) = ptr (D.CL B ls s).bpp := by
    have := rec_word h hm h201 hs (k := 2) (by norm_num)
    rw [h2] at this
    exact load_val (gA _ (mA _ (by simp))) (not_mem_of_noneIn k1 _ (by simp)) this
  have m1 := mulG (by omega) (by omega) (gA _ (mA (.mul (.n (stepB s + 1)) (.n (stepB s)) (.n 18))
    (by simp)))
  refine ⟨by rw [m1, e0, h17], fun hs0 j hj ↦ ?_⟩
  have hf0 : firstOf s = 0 := by unfold firstOf; split <;> omega
  simp only [hf0, show (0 : ℕ) = 1 ↔ False by decide, ↓reduceIte] at hw
  obtain ⟨-, h5, -, -⟩ := hw
  have m0 : Stmt.atom (.load (.n (stepB s + 6 + 2 * j)) (.n 161) (22 * s + 5)) ∈
      flipsT s (stepB s + 6) := by
    simp only [flipsT, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [flipT, hs0, flipSz]⟩
  have l5 := rec_word h hm h201 hs (k := 5) (by norm_num)
  rw [h5] at l5
  exact load_val (w := D.w B curE) (hg _ (mem_stepCoreF m0))
    (not_mem_of_noneIn k5 _ (load_mem_resid m0)) l5

/-- **The inputs' check's pointers.** -/
theorem fin_ptrs (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (h17 : σ (.n 18) = gen ^ (D.τ - 4))
    (h201 : σ (.n 161) = ptr (B + D.o201)) :
    σ (.n 1746) = ptr (ls 11) * gen ^ (D.τ - 4) ∧
      σ (.n 1980) = ptr (ls 11 + (D.layer 11).y + 128) ∧
      σ (.n 3143) = ptr (ls 11 + (D.layer 11).y + 139) := by
  have hg : ∀ st ∈ vkFinT, GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_right _ hst)
  have gA : ∀ a, Stmt.atom a ∈ vkFinT → Good rd vkSt (D.w B curE) σ a := fun a h ↦ hg _ h
  have k1 := vkFin_ker.1
  have hrec := last_rec h hm
  rw [outWs_last h, ← h201] at hrec
  have e4977 : σ (.n 1745) = ptr (ls 11) :=
    load_val (gA (.load (.n 1745) (.n 161) 266) (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp))
      (by simpa using hrec 2 (by norm_num))
  have m4978 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 1746) (.n 1745) (.n 18)) (by simp [vkFinT]))
  refine ⟨by rw [m4978, e4977, h17], ?_, ?_⟩
  · exact load_val (gA (.load (.n 1980) (.n 161) 268) (by simp [vkFinT]))
      (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 4 (by norm_num))
  · exact load_val (gA (.load (.n 3143) (.n 161) 267) (by simp [vkFinT]))
      (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 3 (by norm_num))

end VkData

end
end LeanVM.Guest.B1.VerifySub
