/-
  LeanVM.Guest.B1.KeccakGkr.VkCT

  `verify_keccak`'s body on its layout, whole.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCS

/-!
# The body, whole

`body_holds`: on the layout, the honest valuation satisfies the whole body and returns the
capacity after the ring map's first challenge, the cursor past the words read, the word and the
challenge. `body_sizes`, `body_bases`: the buffers' sizes and bases are the layout's.
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

theorem stepCb_eq : ∀ s < 12, 2 ≤ s → stepCb s = stepPn (s - 1) := by decide

theorem stepPn_eq : ∀ s < 11,
    stepPn (s + 1) = stepT0 s (stepB s) + (if s = 0 then 5 else 7) := by decide +kernel

/-- **The claim records' pointers the steps pass on**: step `s ≥ 1` reads claim `s`'s at
`stepCb s` and claim `s + 1`'s at `stepPn s`, as the step before computed them. -/
theorem steps_chain (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (h17 : σ (.n 18) = gen ^ (D.τ - 4))
    (h201 : σ (.n 161) = ptr (B + D.o201)) (h274 : σ (.n 234) = ptr (B + D.o274)) :
    ∀ s, s < 12 → 1 ≤ s → σ (.n (stepCb s)) = σ (.n 161) * gen ^ (22 * (s - 1)) ∧
      σ (.n (stepPn s)) = σ (.n 161) * gen ^ (22 * s)
  | 0, _, h1 => absurd h1 (by norm_num)
  | 1, _, _ => by
    refine ⟨by simp [stepCb], ?_⟩
    rw [stepPn_eq 0 (by norm_num)]
    exact ((step_on h hm hσd (s := 0) (by norm_num) h17 h201 h274 (fun h ↦ absurd h (by norm_num))
      (fun h ↦ absurd h (by norm_num))).2.1 rfl).2.2
  | k + 2, hs, _ => by
    have IH := steps_chain h hm hσd h17 h201 h274 (k + 1) (by omega) (by omega)
    refine ⟨by rw [stepCb_eq (k + 2) hs (by omega)]; exact IH.2, ?_⟩
    rw [stepPn_eq (k + 1) (by omega)]
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact ((step_on h hm hσd (s := k + 1) (by omega) h17 h201 h274 (fun _ ↦ IH.1)
      (fun _ ↦ IH.2)).2.2.1 (by omega)).2.2.2.2

/-- **The twelve steps, on the layout.** -/
theorem steps_holds (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (h17 : σ (.n 18) = gen ^ (D.τ - 4))
    (h201 : σ (.n 161) = ptr (B + D.o201))
    (h274 : σ (.n 234) = ptr (B + D.o274)) {next : Prop} {kret : List E → Prop} (hn : next) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkStepsT next kret := by
  have S : ∀ s, s < 12 → ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ
        (stepT s (stepB s) (stepCap s) (stepCur s) (stepCb s) (stepPn s)) next kret :=
    fun s hs ↦ (step_on h hm hσd hs h17 h201 h274
      (fun h1 ↦ (steps_chain h hm hσd h17 h201 h274 s hs h1).1)
      (fun h1 ↦ (steps_chain h hm hσd h17 h201 h274 s hs h1).2)).2.2.2
  rw [vkStepsT]
  simp only [holdsList_append]
  exact S 0 (by norm_num) (S 1 (by norm_num) (S 2 (by norm_num) (S 3 (by norm_num)
    (S 4 (by norm_num) (S 5 (by norm_num) (S 6 (by norm_num) (S 7 (by norm_num)
    (S 8 (by norm_num) (S 9 (by norm_num) (S 10 (by norm_num) (S 11 (by norm_num) hn)))))))))))

set_option maxRecDepth 20000 in
/-- **The body, on the layout.** -/
theorem body_holds (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) :
    Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkT False
      (fun r ↦ r = capOf D.sF.perm ++ [ptr curE * gen ^ D.xs.length, D.word]) := by
  obtain ⟨-, -, p6, -, -, p9, p10, h17, -, -, a58, -, -, -, -, -, -, -, -, -, a201, -,
    a274, -, HF⟩ := head_first h hm hσd
  obtain ⟨-, -, -, -, -, eO, e3701, -, -, -, -, HO⟩ := out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n 929) = ptr (curE + D.lcur 12 + 12) := by
    have := eO 5 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2]), (O_ok h).2]
    simp [cL, ptr_mul_gen]
  obtain ⟨-, -, e1251, -, e4104, e4107, -, -, e4110, -, hcp, HI⟩ :=
    in_on h hm hσd p6 p9 p10 a201 e3699
  have e4115 : σ (.n 1338) = ptr (curE + D.lcur 12 + 33) := by
    rw [show (1338 : ℕ) = 1333 + 5 from rfl, e4110 5 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
  have e4116 : σ (.n 1339) = D.S.2.1 := by
    rw [show (1339 : ℕ) = 1333 + 6 from rfl, e4110 6 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]; norm_num), (S_ok h).2]
    rfl
  obtain ⟨-, -, -, -, HFn⟩ := fin_on h hm hσd p9 p10 h17 a201 e4104 e4107 e4116 e1251
  rw [vkT, holdsList_append, holdsList_append, holdsList_append, holdsList_append]
  refine HF (steps_holds h hm hσd h17 a201 a274 (HO (HI (HFn ?_))))
  rw [hcp, e4115, e3701, ptr_mul_gen, ptr_mul_gen, xs_length h,
    show curE + D.lcur 12 + 33 + 64 = curE + (D.lcur 12 + 97) by omega]
  rfl

theorem val_57 (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE tbE)
    (h17 : σ (.n 18) = gen ^ (D.τ - 4)) : σ (.n 60) = gen ^ (D.τ - 3) := by
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w B curE) σ s := by
    subst hσd; exact (val_good h).2.1
  have gA : ∀ a, Stmt.atom a ∈ vkT → pinB (.atom a) = false → Good rd vkSt (D.w B curE) σ a :=
    fun a h hp ↦ hG _ h hp
  have c56 : σ (.n 59) = Guest.word 2 0 :=
    gA (.const (.n 59) (Guest.word 2 0)) (by simp [vkT, vkHeadT, vkPointT]) rfl
  have m57 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n 60) (.n 18) (.n 59)) (by simp [vkT, vkHeadT, vkPointT]) rfl)
  rw [m57, h17, c56, word_gen, ← pow_succ]
  congr 1
  have := h.1
  omega

/-- **The buffers' sizes.** -/
theorem body_sizes (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE tbE)
    (h17 : σ (.n 18) = gen ^ (D.τ - 4)) :
    (vkPre.filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) = D.sizes := by
  have hτ := h.2.1
  rw [vkPre_kernel.2.2.1]
  simp only [vkAllocs, sizes, List.map_cons, List.map_nil, Sum.elim_inl, Sum.elim_inr, id]
  rw [val_57 h hσd h17, gen_pow_eq_ofK, logG_spec (by omega)]

/-- **The buffers' bases.** -/
theorem body_bases (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) :
    ((vkPre.filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
      (bases B D.sizes).map (fun b ↦ ofK (Parameters.addressOfIndex b)) := by
  have ha : ∀ x ∈ vkAllocs, σ x.1 = D.w B curE x.1.idx := by subst hσd; exact val_alloc h
  have e : vkAllocs.map (σ ∘ Prod.fst) = vkAllocs.map (fun x ↦ D.w B curE x.1.idx) :=
    List.map_congr_left (fun x hx ↦ ha x hx)
  rw [vkPre_kernel.2.2.1, List.map_map, e, bases_eq D B (by have := h.1; omega)]
  simp only [vkAllocs, List.map_cons, List.map_nil]
  rfl

theorem stepE_succ : ∀ s < 11, stepE s = stepB (s + 1) := by decide

theorem stepT0_lt : ∀ s < 12, 6 ≤ stepT0 s (stepB s) := by decide +kernel

set_option maxRecDepth 20000 in
/-- **Layer `s`'s call**: its name, arguments and returns, as the callee is placed. -/
theorem layer_call (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12) (fs : String → ℕ)
    (ps : List ℕ) :
    (stepCall s).2.1 = D.lname s ∧
      (stepCall s).2.2.1.map σ = (D.layKid fs B curE tbE s).args ps ∧
      (stepCall s).2.2.2.map σ = (D.layer s).rets (firstOf s) (ptr (curE + D.lcur s)) := by
  have hτ1 := h.1
  obtain ⟨-, p5, -, -, -, -, -, h17, h33, h47, -, -, -, -, -, -, -, hcap0, -, ecells, a201, -,
    a274, -, -⟩ := head_first h hm hσd
  obtain ⟨hio, h0, hL, -⟩ := step_on h hm hσd hs h17 a201 a274
    (fun h1 ↦ (steps_chain h hm hσd h17 a201 a274 s hs h1).1)
    (fun h1 ↦ (steps_chain h hm hσd h17 a201 a274 s hs h1).2)
  have hy := D.layer_y h hs.le
  have p11 : σ (.n 11) = ptr tbE := by rw [hσd]; exact val_tabs h
  have hE := stepE_eq s hs
  have hT6 := stepT0_lt s hs
  set T := stepT0 s (stepB s) with hT
  -- the returns
  have hrets : ∀ c, (List.range 6).map (fun j ↦ σ (.n (T + c + j))) =
      (D.layer s).rets (firstOf s) (ptr (curE + D.lcur s)) → True := fun _ _ ↦ trivial
  clear hrets
  have hr : ∀ j < 6, σ (.n (stepE s - 6 + j)) =
      ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD j 0 := fun j hj ↦
    step_rets h hσd hs hj
  have hRL : ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).length = 6 := by
    simp [LayerData.rets, beta_cap_length]
  rcases s with _ | k
  · obtain ⟨e1, e3, e5⟩ := h0 rfl
    simp only [stepTailSz, ↓reduceIte] at hE
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stepCall, ↓reduceIte, layKid, List.map_append, List.map_map, List.map_cons,
        List.map_nil, cells, Function.comp_def]
      rw [show (stepCap 0).map (fun v ↦ σ (.n v)) = (D.layer 0).cap by rw [← hcap0]; rfl]
      congr 1
      simp only [cells, ↓reduceIte] at ecells
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
    simp only [stepTailSz, hk0, ↓reduceIte] at hE
    have hEk := stepE_succ k (by omega)
    have hk : k < 12 := by omega
    have hprev : ∀ j < 6, σ (.n (stepB (k + 1) - 6 + j)) =
        ((D.layer k).rets (firstOf k) (ptr (curE + D.lcur k))).getD j 0 := fun j hj ↦ by
      rw [← hEk]; exact step_rets h hσd hk hj
    refine ⟨rfl, ?_, ?_⟩
    · simp only [stepCall, hk0, ↓reduceIte, layKid, List.map_append, List.map_map, List.map_cons,
        List.map_nil, cells, Function.comp_def]
      congr 1
      · apply List.ext_getElem (by simp [stepCap]; rw [D.layer_cap h (by omega)])
        intro j h1 h2
        simp only [stepCap, hk0, ↓reduceIte, List.length_map, List.length_range] at h1
        simp only [stepCap, hk0, ↓reduceIte, List.map_map, Function.comp_def, List.getElem_map,
          List.getElem_range]
        rw [hprev j (by omega), rets_cap h hk (by omega), ← List.getD_eq_getElem _ 0 h2]
        rfl
      · simp only [List.cons.injEq, and_true]
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
      omega

end VkData

end
end LeanVM.Guest.B1.VerifySub
