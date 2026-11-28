/-
  LeanVM.Guest.B1.VsC.VkPF

  `verify_keccak` placed: the body whole on the layout, its buffers, and its layers' calls (the
  archive's `VkCT`).
-/

module

public import LeanVM.Guest.B1.VsC.VkPE
public import LeanVM.Guest.B1.VsC.KLMain
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The body, whole

`body_holds`: on the layout, the honest valuation satisfies the whole body and returns the
capacity after the slices, the cursor past the words read and the word. `body_sizes`,
`body_bases`: the buffers' sizes and bases are the layout's. `layer_call`: layer `s`'s call's
name, arguments and returns.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

namespace VkData

variable {D : VkData} {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

set_option maxRecDepth 20000 in
/-- **The body, on the layout.** -/
theorem body_holds (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkT False
      (fun r ↦ r = capOf D.sF.perm ++ [VsC.ptrAtV curE * gen ^ D.xs.length, D.word]) := by
  obtain ⟨-, -, p6, -, -, p9, p10, h17, -, -, a58, -, -, -, -, -, -, -, -, -, a201, -,
    a274, -, HF⟩ := head_first h hm hσd
  obtain ⟨-, -, -, -, -, eO, e3701, -, -, -, -, HO⟩ := out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n (val% «verify_keccak» "cursor@14")) = VsC.ptrAtV (curE + D.lcur 12 + 12) := by
    rw [show (val% «verify_keccak» "cursor@14") = (val% «verify_keccak» "fs0@14") + 5 from rfl,
      eO 5 (by norm_num), oRets_cur h]
  obtain ⟨-, -, e1251, -, e4104, e4107, -, -, e4110, -, hcp, HI⟩ :=
    in_on h hm hσd p6 p9 p10 a201 e3699
  have e4115 : σ (.n (val% «verify_keccak» "cursor@16")) = VsC.ptrAtV (curE + D.lcur 12 + 33) := by
    rw [show (val% «verify_keccak» "cursor@16") = (val% «verify_keccak» "fs0@16") + 5 from rfl,
      e4110 5 (by norm_num), sRets, List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
  have e4116 : σ (.n (val% «verify_keccak» "in_value")) = D.S.2.1 := by
    rw [show (val% «verify_keccak» "in_value") = (val% «verify_keccak» "fs0@16") + 6 from rfl,
      e4110 6 (by norm_num), sRets, List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]; norm_num),
      (S_ok h).2]
    rfl
  obtain ⟨-, -, -, -, HFn⟩ := fin_on h hm hσd p9 p10 h17 a201 e4104 e4107 e4116 e1251
  rw [vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append]
  refine HF (steps_holds h hm hσd h17 a201 a274 (HO (HI (HFn ?_))))
  rw [hcp, e4115, e3701, ptr_mul_gen, ptr_mul_gen, xs_len h,
    show curE + D.lcur 12 + 33 + 64 = curE + (D.lcur 12 + 97) by omega]
  rfl

theorem val_57 (h : D.Ok) {σ : Val} (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4)) :
    σ (.n (val% «verify_keccak» "point~1")) = gen ^ (D.τ - 3) := by
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w c curE) σ s := by
    subst hσd; exact (val_good h).2.1
  have gA : ∀ a, Stmt.atom a ∈ vkT → pinB (.atom a) = false → Good rd vkSt (D.w c curE) σ a :=
    fun a h hp ↦ hG _ h hp
  have c56 : σ (.n (val% «verify_keccak» "point~0")) = Guest.word 2 0 :=
    gA (.const (.n (val% «verify_keccak» "point~0")) (Guest.word 2 0)) (by simp [vkT, vkHeadT, vkPointT]) rfl
  have m57 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "point~1")) (.n (val% «verify_keccak» "pack_g"))
      (.n (val% «verify_keccak» "point~0"))) (by simp [vkT, vkHeadT, vkPointT]) rfl)
  rw [m57, h17, c56, word_gen, ← pow_succ]
  congr 1
  have := h.1
  omega

/-- **The buffers' sizes.** -/
theorem body_sizes (h : D.Ok) {σ : Val} (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4)) :
    (vkPre.filterMap Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) = D.sizes := by
  have hτ := h.2.1
  rw [vkPre_kernel.2.2.1]
  simp only [vkAllocs, sizes, List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id]
  rw [val_57 h hσd h17, gen_pow_eq_ofK, logG_spec (by omega)]

/-- **The buffers' bases.** -/
theorem body_bases (h : D.Ok) {σ : Val} (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) :
    ((vkPre.filterMap Stmt.allocSz).map Prod.fst).map σ =
      (bases c D.sizes).map (fun b ↦ ofK (Parameters.addressOfIndex b)) := by
  have ha : ∀ x ∈ vkAllocs, σ x.1 = D.w c curE x.1.idx := by subst hσd; exact val_alloc h
  have e : vkAllocs.map (σ ∘ Prod.fst) = vkAllocs.map (fun x ↦ D.w c curE x.1.idx) :=
    List.map_congr_left (fun x hx ↦ ha x hx)
  rw [vkPre_kernel.2.2.1, List.map_map, e, bases_eq D c (by have := h.1; omega)]
  simp only [vkAllocs, List.map_cons, List.map_nil]
  rfl

theorem stepE_succ : ∀ s < 11, stepE s = stepB (s + 1) := by decide +kernel

theorem stepT0_lt : ∀ s < 12, 6 ≤ stepT0 s (stepB s) := by decide +kernel

/-- Layer `s`'s honest arguments. -/
def layArgs (D : VkData) (c curE tbE : ℕ) (s : ℕ) : List E :=
  layerArgs (D.layer s) (D.cells s).1 (D.cells s).2 (VsC.ptrAtV (curE + D.lcur s))
    (VsC.ptrAtV (c + D.o201 + 22 * s)) (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
    (keccakIota D.τ s (D.layer s).c) (VsC.ptrAtV tbE)

set_option maxRecDepth 20000 in
/-- **Layer `s`'s call**: its name, arguments and returns. -/
theorem layer_call (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12) :
    (stepCall s).2.1 = layerName (firstOf s) ∧
      (stepCall s).2.2.1.map σ = D.layArgs c curE tbE s ∧
      (stepCall s).2.2.2.map σ = (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s)) := by
  have hτ1 := h.1
  obtain ⟨-, p5, -, -, -, -, -, h17, h33, h47, -, -, -, -, -, -, -, hcap0, -, ecells, a201, -,
    a274, -, -⟩ := head_first h hm hσd
  obtain ⟨hio, h0, hL, -⟩ := step_on' h hm hσd hs h17 a201 a274
  have hy := D.layer_y h hs.le
  have p11 : σ (.n (val% «verify_keccak» "tabs")) = VsC.ptrAtV tbE := by rw [hσd]; exact val_tabs h
  have hT6 := stepT0_lt s hs
  have hr : ∀ j < 6, σ (.n (stepE s - 6 + j)) =
      ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).getD j 0 := fun j hj ↦ by
    rw [hσd]; exact step_rets h hs hj
  have hRL : ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).length = 6 := by
    simp [LayerData.rets, beta_cap_length]
  rcases s with _ | k
  · obtain ⟨e1, e3, e5⟩ := h0 rfl
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stepCall, ↓reduceIte, layArgs, layerArgs, List.map_append, List.map_map,
        List.map_cons, List.map_nil, Function.comp_def]
      rw [show (stepCap 0).map (fun v ↦ σ (.n v)) = (D.layer 0).cap by rw [← hcap0]; rfl]
      congr 1
      simp only [cells, ↓reduceIte] at ecells ⊢
      simp only [List.cons.injEq, and_true]
      refine ⟨(Prod.ext_iff.1 ecells).1, (Prod.ext_iff.1 ecells).2,
        by rw [e1, p5, ptr_mul_gen1]; simp [lcur], by rw [e3, hy], by rw [h33, hy],
        by rw [h47, hy], by rw [a201]; rfl, by rw [e5, a201, ptr_mul_gen], hio, p11⟩
    · simp only [stepCall, ↓reduceIte, List.map_map, Function.comp_def]
      apply List.ext_getElem (by simp [hRL])
      intro j h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2, ← hr j h1]
      congr 2
  · have hk0 : k + 1 ≠ 0 := by omega
    obtain ⟨e0, e1, e3, e5, e7⟩ := hL hk0
    have hEk := stepE_succ k (by omega)
    have hk : k < 12 := by omega
    have hprev : ∀ j < 6, σ (.n (stepB (k + 1) - 6 + j)) =
        ((D.layer k).rets (firstOf k) (VsC.ptrAtV (curE + D.lcur k))).getD j 0 := fun j hj ↦ by
      rw [← hEk, hσd]; exact step_rets h hk hj
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stepCall, hk0, ↓reduceIte, layArgs, layerArgs, List.map_append, List.map_map,
        List.map_cons, List.map_nil, Function.comp_def]
      congr 1
      · apply List.ext_getElem (by simp [stepCap]; rw [D.layer_cap h (by omega)])
        intro j h1 h2
        simp only [stepCap, hk0, ↓reduceIte, List.length_map, List.length_range] at h1
        simp only [stepCap, hk0, ↓reduceIte, List.map_map, Function.comp_def, List.getElem_map,
          List.getElem_range]
        rw [hprev j (by omega), rets_cap h hk (by omega), ← List.getD_eq_getElem _ 0 h2]
        rfl
      · simp only [cells, hk0, ↓reduceIte, List.cons.injEq, and_true]
        refine ⟨e0, e1, ?_, by rw [e3, hy], by rw [h33, hy], by rw [h47, hy],
          by rw [e5, a201, ptr_mul_gen], by rw [e7, a201, ptr_mul_gen], hio, p11⟩
        have := hprev 5 (by norm_num)
        rw [rets_cur h hk] at this
        simp only [stepCur, hk0, ↓reduceIte]
        rw [show stepB (k + 1) - 1 = stepB (k + 1) - 6 + 5 by
          have := step_bounds (k + 1) (by omega); omega]
        exact this
    · simp only [stepCall, hk0, ↓reduceIte, List.map_map, Function.comp_def]
      apply List.ext_getElem (by simp [hRL])
      intro j h1 h2
      simp only [List.length_map, List.length_range] at h1
      rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem _ 0 h2, ← hr j h1]
      congr 2

end VkData

end
end LeanVM.Guest.B1.VerifySub
