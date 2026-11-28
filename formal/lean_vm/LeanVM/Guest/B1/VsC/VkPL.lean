/-
  LeanVM.Guest.B1.VsC.VkPL

  `verify_keccak` placed: on a memory holding the layout, its calls carry their honest words
  (`honest_of_mem`).
-/

module

public import LeanVM.Guest.B1.VsC.VkPK
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The calls on the layout

`calls_eq`: the body's calls on a valuation whose three copy loops are entered. `honestX_of_mem`:
on a memory holding the layout, the honest valuation's calls carry their honest words (`HonestX`),
hence `HonestCalls` (`honest_of_x`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

theorem one_add_gen_ne {n : ℕ} (h0 : 0 < n) (h1 : n < 2 ^ 64 - 1) : (1 : E) + gen ^ n ≠ 0 := by
  rw [show (1 : E) = gen ^ 0 from (pow_zero _).symm]
  exact fun h ↦ absurd ((VsC.gen_add_ne' (by norm_num) h1).mp h) (by omega)

/-- **The body's calls**, its three copy loops entered. -/
theorem calls_eq {σ : Val} (h1 : σ (.n (val% «verify_keccak» "s17#1")) ≠ 0)
    (h2 : σ (.n (val% «verify_keccak» "s57#1")) ≠ 0) (h3 : σ (.n (val% «verify_keccak» "s81#1")) ≠ 0) :
    calls (vkPre.flatMap (slEvs σ)) =
      ⟨name% «verify_keccak_loop0», l0Call.2.2.1, [], true⟩ ::
        ((List.range 12).map fun s ↦ (⟨VkData.lname s, (stepCall s).2.2.1, (stepCall s).2.2.2, true⟩ : Call)) ++
        [⟨"keccak_plain_rounds__L6_L0", oCall.2.2.1, oCall.2.2.2, true⟩,
          ⟨name% «verify_keccak_loop1», l1Call.2.2.1, [], true⟩,
          ⟨"keccak_plain_rounds__L4_L1", iCall.2.2.1, iCall.2.2.2, true⟩,
          ⟨"keccak_plain_rounds__L6_L0", sCall.2.2.1, sCall.2.2.2, true⟩,
          ⟨name% «verify_keccak_loop2», l2Call.2.2.1, [], true⟩] := by
  rw [(straight_parts σ _ vkPre_kernel.1).2.2.2, vkPre_kernel.2.2.2, vkCalls]
  simp only [List.map_cons, List.map_append, List.map_map, List.cons_append]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_)
  · simp [mkCall, l0Call, h1]
  · refine List.map_congr_left fun s _ ↦ ?_
    by_cases h0 : s = 0 <;> simp only [Function.comp, stepCall, VkData.lname, VkData.firstOf, h0, ↓reduceIte, mkCall]
  · simp [mkCall, oCall, l1Call, iCall, sCall, l2Call, h2, h3]

namespace VkData

variable {D : VkData} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
variable {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ}

/-- The copy loops' conditions, on the honest valuation. -/
theorem conds (h : D.Ok) :
    D.val rd c curE chiE olE zvE slE tbE (.n (val% «verify_keccak» "s17#1")) ≠ 0 ∧
    D.val rd c curE chiE olE zvE slE tbE (.n (val% «verify_keccak» "s57#1")) ≠ 0 ∧
    D.val rd c curE chiE olE zvE slE tbE (.n (val% «verify_keccak» "s81#1")) ≠ 0 := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  set σ := D.val rd c curE chiE olE zvE slE tbE with hσd
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w c curE) σ s := (val_good h).2.1
  have gA : ∀ a, Stmt.atom a ∈ vkT → pinB (.atom a) = false → Good rd vkSt (D.w c curE) σ a :=
    fun a h hp ↦ hG _ h hp
  have mB : ∀ s ∈ vkBitsT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ ?_))))
    rw [vkHeadT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have mP : ∀ s ∈ vkPointT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ ?_))))
    rw [vkHeadT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
  have mO : ∀ s ∈ vkOutT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hs))
  have mF : ∀ s ∈ vkFinT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    exact List.mem_append_right _ hs
  -- `pack_g`, from the bits
  have hbits : ∀ j < 5, σ (.n (21 + j)) = Value.bitE ((D.τ - 3).testBit j) := by
    intro j hj
    have g := hG (.atom (.hint (.bitsExp (.n 20) 5 (.stack [.n 21, .n 22, .n 23, .n 24, .n 25]))))
      (mB _ (by simp [vkBitsT])) rfl
    exact (g (.n (21 + j)) (by simp; omega)).trans (w_bits hj)
  have hpar : ∀ i < 12, σ (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0 := (val_good h).2.2
  have p6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ := by
    obtain ⟨f0, f1, f2, f3, f4, hf⟩ := five_of_length' h.2.2.2.2.1
    rw [hpar _ (by norm_num), args, hf]; rfl
  obtain ⟨h17, -⟩ := vkBits_complete (C := fun _ _ _ ↦ True) hτ1 hτ2
    (fun s hs hp ↦ hG s (mB s hs) hp) p6 hbits
  have hne := one_add_gen_ne (n := D.τ - 4) (by omega) (by omega)
  have e1 : ∀ (x y : ℕ), Stmt.atom (.const (.n x) (Guest.word 1 0)) ∈ vkT →
      Stmt.atom (.add (.n y) (.n x) (.n (val% «verify_keccak» "pack_g"))) ∈ vkT → σ (.n y) = 1 + gen ^ (D.τ - 4) := by
    intro x y hx hy
    have cx : σ (.n x) = Guest.word 1 0 := gA _ hx rfl
    have ay : σ (.n y) = σ (.n x) + σ (.n (val% «verify_keccak» "pack_g")) := gA _ hy rfl
    rw [ay, cx, word_one, h17]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1 (val% «verify_keccak» "s17#0") (val% «verify_keccak» "s17#1") (mP _ (by simp [vkPointT]))
      (mP _ (by simp [vkPointT]))]
    exact hne
  · rw [e1 (val% «verify_keccak» "s57#0") (val% «verify_keccak» "s57#1") (mO _ (by simp [vkOutT]))
      (mO _ (by simp [vkOutT]))]
    exact hne
  · rw [e1 (val% «verify_keccak» "s81#0") (val% «verify_keccak» "s81#1") (mF _ (by simp [vkFinT]))
      (mF _ (by simp [vkFinT]))]
    exact hne

/-- **The calls' honest words**, list by list. -/
def HonestX (D : VkData) (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)
    (c curE chiE zvE tbE : ℕ) (σ : Val) : Prop :=
  l0Call.2.2.1.map σ = clArgs 0 (D.τ - 4) c (chiE + 4) ∧
    (∀ s < 12, (stepCall s).2.2.1.map σ = D.layArgs c curE tbE s ∧
      (stepCall s).2.2.2.map σ = (D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))) ∧
    oCall.2.2.1.map σ = D.oArgs curE zvE tbE ∧ oCall.2.2.2.map σ = D.oRets curE ∧
    l1Call.2.2.1.map σ = clArgs 0 (D.τ - 4) (zvE + 4) c ∧
    iCall.2.2.1.map σ = D.iArgs curE zvE tbE ∧ iCall.2.2.2.map σ = D.iRets curE ∧
    sCall.2.2.1.map σ = D.sArgs curE zvE tbE ∧ sCall.2.2.2.map σ = D.sRets curE ∧
    l2Call.2.2.1.map σ = clArgs 0 (D.τ - 4) (zvE + 43) (D.lsP fs al cert k c curE tbE 11)

theorem honest_of_x {σ σ' : Val} (hx : D.HonestX fs al cert k c curE chiE zvE tbE σ)
    (h1 : σ' (.n (val% «verify_keccak» "s17#1")) ≠ 0)
    (h2 : σ' (.n (val% «verify_keccak» "s57#1")) ≠ 0) (h3 : σ' (.n (val% «verify_keccak» "s81#1")) ≠ 0) :
    D.HonestCalls fs al cert k c curE chiE zvE tbE σ (calls (vkPre.flatMap (slEvs σ'))) := by
  rw [calls_eq h1 h2 h3]
  obtain ⟨a, b, c', d, e, f, g, i, j, l⟩ := hx
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, a, b, c', d, e, f, g, i, j, l⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **On a memory holding the layout, the honest valuation's calls carry their honest words.** -/
theorem honestX_of_mem (h : D.Ok)
    (hm : D.Mem rd c curE chiE olE zvE slE tbE (D.lsP fs al cert k c curE tbE)) :
    D.HonestX fs al cert k c curE chiE zvE tbE (D.val rd c curE chiE olE zvE slE tbE) := by
  have hτ1 := h.1
  set σ := D.val rd c curE chiE olE zvE slE tbE with hσd
  obtain ⟨-, p5, p6, p7, -, p9, p10, h17, -, -, a58, -, e61, e63, -, -, -, -, e191, -, a201, -,
    a274, -, -⟩ := head_first h hm hσd
  obtain ⟨eL, e13, e3691, z7, z8, eO, -, ewr, -, e3972, e3974, -⟩ := out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n (val% «verify_keccak» "cursor@14")) = VsC.ptrAtV (curE + D.lcur 12 + 12) := by
    rw [show (val% «verify_keccak» "cursor@14") = (val% «verify_keccak» "fs0@14") + 5 from rfl,
      eO 5 (by norm_num), oRets_cur h]
  obtain ⟨e3976, e3977, e1251, eI, e4104, e4107, z16a, z16b, eS, -⟩ := in_on h hm hσd p6 p9 p10 a201 e3699
  have e4116 : σ (.n (val% «verify_keccak» "in_value")) = D.S.2.1 := by
    rw [show (val% «verify_keccak» "in_value") = (val% «verify_keccak» "fs0@16") + 6 from rfl,
      eS 6 (by norm_num), sRets, List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]; norm_num), (S_ok h).2]
    rfl
  obtain ⟨elp, -, e6581, e6583, -⟩ := fin_on h hm hσd p9 p10 h17 a201 e4104 e4107 e4116 e1251
  have p11 : σ (.n (val% «verify_keccak» "tabs")) = VsC.ptrAtV tbE := by rw [hσd]; exact val_tabs h
  have hmap : ∀ (b : ℕ) (l : List E), l.length = 7 → (∀ j < 7, σ (.n (b + j)) = l.getD j 0) →
      ((List.range 7).map fun j ↦ V.n (b + j)).map σ = l := by
    intro b l hl hj
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp]
    rw [hj i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  have hOL : (D.oRets curE).length = 7 := by simp [oRets, (O_ok h).2]
  have hIL : (D.iRets curE).length = 7 := by simp [iRets, (I_ok h).2]
  have hSL : (D.sRets curE).length = 7 := by simp [sRets, (S_ok h).2]
  have cap5_eq : ∀ (b : ℕ) (l : List E), l.length = 5 → (∀ j < 5, σ (.n (b + j)) = l.getD j 0) →
      (cap5 b).map σ = l := by
    intro b l hl hj
    obtain ⟨x0, x1, x2, x3, x4, rfl⟩ := five_of_length' hl
    simp only [cap5, List.map_cons, List.map_nil]
    rw [show b = b + 0 from rfl, hj 0 (by norm_num), hj 1 (by norm_num), hj 2 (by norm_num),
      hj 3 (by norm_num), hj 4 (by norm_num)]
    rfl
  refine ⟨?_, fun s hs ↦ ⟨(layer_call h hm hσd hs).2.1,
    (layer_call h hm hσd hs).2.2⟩, ?_, hmap _ _ hOL eO, ?_, ?_, hmap _ _ hIL eI, ?_, hmap _ _ hSL eS, ?_⟩
  · simp only [l0Call, List.map_cons, List.map_nil, clArgs]
    show _ = [gen ^ 0, gen ^ (D.τ - 4), VsC.ptrAtV c, VsC.ptrAtV (chiE + 4)]
    rw [e61, h17, a58, e63, ptr_mul_gen, pow_zero]
  · -- the committed outputs' rounds
    have hc : oCall.2.2.1 = cap5 (val% «verify_keccak» "fs0@13") ++ [.n (val% «verify_keccak» "fs0@14~7"),
        .n (val% «verify_keccak» "fs0@14~8"), .n (val% «verify_keccak» "cursor@13"), .n (val% «verify_keccak» "x@1"),
        .n (val% «verify_keccak» "out_slot"), .n (val% «verify_keccak» "tabs")] := rfl
    rw [hc, List.map_append, show cap5 (val% «verify_keccak» "fs0@13") = cap5 910 from rfl, eL, oArgs]
    simp only [List.map_cons, List.map_nil]
    rw [z7, z8, e13, e191, e3691, p11]
  · simp only [l1Call, List.map_cons, List.map_nil, clArgs]
    rw [e3972, h17, e3974, a58, ptr_mul_gen, pow_zero]
  · -- the inputs' rounds
    have hc : iCall.2.2.1 = cap5 (val% «verify_keccak» "fs0@14") ++ [.n (val% «verify_keccak» "word_rate[0]"),
        .n (val% «verify_keccak» "word_rate[1]"), .n (val% «verify_keccak» "fs0@15~8"),
        .n (val% «verify_keccak» "fs0@15~9"), .n (val% «verify_keccak» "fs0@15~11"),
        .n (val% «verify_keccak» "tabs")] := rfl
    rw [hc, List.map_append, cap5_eq _ D.O.2.2.cap (O_ok h).2 (fun j hj ↦ by
      rw [eO j (by omega), oRets, List.getD_append _ _ _ _ (by rw [(O_ok h).2]; exact hj)]), iArgs]
    simp only [List.map_cons, List.map_nil]
    rw [← ewr, e3976, e3977, e1251, p11]
    simp only [cL, ptr_mul_gen, ptr_mul_gen1]
  · -- the inputs' opening's rounds
    have hc : sCall.2.2.1 = cap5 (val% «verify_keccak» "fs0@15") ++ [.n (val% «verify_keccak» "fs0@16~7"),
        .n (val% «verify_keccak» "fs0@16~8"), .n (val% «verify_keccak» "cursor@15"),
        .n (val% «verify_keccak» "low_value"), .n (val% «verify_keccak» "in_slot"),
        .n (val% «verify_keccak» "tabs")] := rfl
    rw [hc, List.map_append, cap5_eq _ D.I.2.2.cap (I_ok h).2 (fun j hj ↦ by
      rw [eI j (by omega), iRets, List.getD_append _ _ _ _ (by rw [(I_ok h).2]; exact hj)]), sArgs]
    simp only [List.map_cons, List.map_nil]
    have e15 : σ (.n (val% «verify_keccak» "cursor@15")) = D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4) := by
      rw [show (val% «verify_keccak» "cursor@15") = (val% «verify_keccak» "fs0@15") + 5 from rfl, eI 5 (by norm_num),
        iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2]), (I_ok h).2]; rfl
    have elow : σ (.n (val% «verify_keccak» "low_value")) = D.I.2.1 := by
      rw [show (val% «verify_keccak» "low_value") = (val% «verify_keccak» "fs0@15") + 6 from rfl, eI 6 (by norm_num),
        iRets, List.getD_append_right _ _ _ _ (by rw [(I_ok h).2]; norm_num), (I_ok h).2]; rfl
    rw [z16a, z16b, e15, elow, e4107, p11]
  · simp only [l2Call, List.map_cons, List.map_nil, clArgs]
    rw [e6581, show (val% «verify_keccak» "pack_g") = (val% «verify_keccak» "pack_g") from rfl, h17, e6583, elp,
      ptr_mul_gen, pow_zero]

end VkData

end
end LeanVM.Guest.B1.VerifySub
