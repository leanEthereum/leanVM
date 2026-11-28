/-
  LeanVM.Guest.B1.VsC.VkPE

  `verify_keccak` placed: the openings, the inputs' check and the return on the layout (the
  archive's `VkCO`, `VkCP`).
-/

module

public import LeanVM.Guest.B1.VsC.VkPD
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The openings and the return, on the layout

`step_rets`: layer `s`'s returns are its honest ones. `out_on`: the committed outputs' opening
holds, its check by the honest run's. `in_on`: the inputs' opening holds, and the sponge after the
slices is the honest run's. `fin_on`: the inputs' check holds by the honest run's, and the body
returns its words.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

theorem ptr_mul_gen1 (b : ℕ) : VsC.ptrAtV b * gen = VsC.ptrAtV (b + 1) := by
  rw [← ptr_mul_gen, pow_one]

namespace VkData

variable {D : VkData} {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

/-- **Layer `s`'s returns are its honest ones.** -/
theorem step_rets (h : D.Ok) {s : ℕ} (hs : s < 12) {j : ℕ} (hj : j < 6) :
    D.val rd c curE chiE olE zvE slE tbE (.n (stepE s - 6 + j)) =
      ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).getD j 0 := by
  have hm : stepCall s ∈ vkCalls :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩))
  have hv : V.n (stepE s - 6 + j) ∈ (stepCall s).2.2.2 := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp only [stepCall, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepE, stepTailSz, ↓reduceIte]; congr 1⟩
    · simp only [stepCall, show s ≠ 0 by omega, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepE, stepTailSz, show s ≠ 0 by omega, ↓reduceIte]; congr 1⟩
  rw [calls_good h _ hm _ hv]
  exact w_layer hs hj

theorem beta_cap_length (s : ℕ) : ((D.layer s).beta (firstOf s)).2.cap.length = 5 :=
  (sq_ok _).2

theorem rets_cap (h : D.Ok) {s : ℕ} (hs : s < 12) {cur : E} {j : ℕ} (hj : j < 5) :
    ((D.layer s).rets (firstOf s) cur).getD j 0 = (D.chain (s + 1)).2.cap.getD j 0 := by
  rw [D.layer_succ h hs, LayerData.rets,
    List.getD_append _ _ _ _ (by rw [beta_cap_length]; exact hj)]

theorem rets_cur (h : D.Ok) {s : ℕ} (hs : s < 12) :
    ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).getD 5 0 =
      VsC.ptrAtV (curE + D.lcur (s + 1)) := by
  rw [LayerData.rets, List.getD_append_right _ _ _ _ (by rw [beta_cap_length]),
    beta_cap_length, ptr_mul_gen, D.layer_y h hs.le]
  simp only [Nat.sub_self, List.getD_cons_zero, lcur]
  congr 1
  ring

theorem L_cap (h : D.Ok) (j : ℕ) :
    D.L.2.cap.getD j 0 = (D.chain 12).2.cap.getD j 0 := by rw [L_eq h]

theorem oRets_cur (h : D.Ok) : (D.oRets curE).getD 5 0 = VsC.ptrAtV (curE + D.lcur 12 + 12) := by
  rw [oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2]), (O_ok h).2]
  simp [cL, ptr_mul_gen]

set_option maxRecDepth 20000 in
/-- **The committed outputs' opening, on the layout.** -/
theorem out_on (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) (h6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ)
    (h9 : σ (.n (val% «verify_keccak» "z_vals")) = VsC.ptrAtV zvE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h58 : σ (.n (val% «verify_keccak» "point")) = VsC.ptrAtV c)
    (h274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274)) :
    (cap5 910).map σ = D.L.2.cap ∧ σ (.n (val% «verify_keccak» "cursor@13")) = D.cL curE ∧
      σ (.n (val% «verify_keccak» "out_slot")) = VsC.ptrAtV zvE * gen ^ D.τ ∧
      σ (.n (val% «verify_keccak» "fs0@14~7")) = 0 ∧ σ (.n (val% «verify_keccak» "fs0@14~8")) = 0 ∧
      (∀ j < 7, σ (.n ((val% «verify_keccak» "fs0@14") + j)) = (D.oRets curE).getD j 0) ∧
      σ (.n (val% «verify_keccak» "x@2")) = D.word ∧
      (σ (.n (val% «verify_keccak» "word_rate[0]")), σ (.n (val% «verify_keccak» "word_rate[1]"))) =
        Keccak.scalarCells D.word dsObserve ∧
      σ (.n (val% «verify_keccak» "s57#1")) = 1 + gen ^ (D.τ - 4) ∧ σ (.n (val% «verify_keccak» "s57#2")) = 1 ∧
      σ (.n (val% «verify_keccak» "s57#4")) = VsC.ptrAtV zvE * gen ^ 4 ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkOutT next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkOutT, GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))
  -- the calls' returns
  have eO : ∀ j < 7, σ (.n ((val% «verify_keccak» "fs0@14") + j)) = (D.oRets curE).getD j 0 := fun j hj ↦ by
    subst hσd
    rw [calls_good h oCall (by simp [vkCalls]) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)]
    exact w_o hj
  have hcL : D.L.2.cap.length = 5 := (L_ok h).2
  have e3699 : σ (.n (val% «verify_keccak» "cursor@14")) = VsC.ptrAtV (curE + D.lcur 12 + 12) := by
    rw [show (val% «verify_keccak» "cursor@14") = (val% «verify_keccak» "fs0@14") + 5 from rfl,
      eO 5 (by norm_num), oRets_cur h]
  have e3700 : σ (.n (val% «verify_keccak» "out_value")) = D.O.2.1 := by
    rw [show (val% «verify_keccak» "out_value") = (val% «verify_keccak» "fs0@14") + 6 from rfl,
      eO 6 (by norm_num), oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2]; norm_num), (O_ok h).2]
    rfl
  -- the memory
  obtain ⟨m58, -, -, -, -, -, m274, -, -⟩ := own_mem hm.own
  obtain ⟨-, -, -, mword, -⟩ := xs_reads h hm.cur
  have hslot : ReadsAt rd (σ (.n (val% «verify_keccak» "z_vals")) * σ (.n (val% «verify_keccak» "tau_g"))) D.O.1 := by
    rw [h9, h6]
    have mop := hm.zv
    rw [op_eq] at mop
    have := (readsAt_append.1 mop).2
    rwa [List.take_append_drop, inst_length h] at this
  have hr0 : LoadHolds rd (σ (.n (val% «verify_keccak» "point")) * σ (.n (val% «verify_keccak» "pack_g"))) 0
      (D.seg.getD 0 0) := by
    rw [h58, h17, loadHolds_mul_gen_pow, add_zero, ← c0_point_seg h]
    exact readsAt_getD m58 (by rw [c0_point_length h]; omega)
  have hL : ∀ lane < 25, LoadHolds rd (σ (.n (val% «verify_keccak» "lane_tree"))) (30 + lane)
      ((eqKernel D.rl).getD lane 0) := by
    intro lane hl
    have := lanes_first m274 lane (by simp [eqKernel_length, rl_length]; omega)
    rw [← ptr_mul_gen, loadHolds_mul_gen_pow] at this
    rw [h274, List.getD_eq_getElem _ _ (by simp [eqKernel_length, rl_length]; omega)]
    simpa using this
  -- the check
  have hchk : (∑ lane ∈ range 25, (∑ m ∈ range 1, eqAt [D.seg.getD 0 0] m *
      eqAt D.O.1 (25 * (1 + m) + lane)) * (eqKernel D.rl).getD lane 0) * D.word =
        σ (.n (val% «verify_keccak» "out_value")) := by
    have hspec := vk_out_check (τ := D.τ) D.inst D.outs D.committed (D.seg.getD 0 0) D.rl
      (by simp [inst_length h]) (O1_length h) (word := 1) (mul_one _)
    rw [mul_one] at hspec
    rw [← hspec, e3700]
    have := h.2.2.2.2.2.2.2.2.2.2.1
    rw [← this]
    congr 4
  obtain ⟨e3691, -, e3701, cells, -, e3971, e3972, e3974, H⟩ :=
    vkOut_complete hσ hg h17 (by rw [e3699]; exact mword) hslot (O1_length h) hr0 hL hchk
  have gA : ∀ a, Stmt.atom a ∈ vkOutT → Good rd vkSt (D.w c curE) σ a := fun a h ↦ hg _ h
  have c3692 : σ (.n (val% «verify_keccak» "fs0@14~7")) = Guest.word 0 0 :=
    gA (.const (.n (val% «verify_keccak» "fs0@14~7")) (Guest.word 0 0)) (by simp [vkOutT])
  have c3693 : σ (.n (val% «verify_keccak» "fs0@14~8")) = Guest.word 0 0 :=
    gA (.const (.n (val% «verify_keccak» "fs0@14~8")) (Guest.word 0 0)) (by simp [vkOutT])
  refine ⟨?_, ?_, by rw [e3691, h9, h6], by rw [c3692, word_zero], by rw [c3693, word_zero], eO,
    e3701, cells, by rw [e3971, h17], e3972, by rw [e3974, h9], H⟩
  · apply List.ext_getElem (by simp [cap5, hcL])
    intro j h1 h2
    simp only [cap5, List.length_map, List.length_cons, List.length_nil] at h1
    subst hσd
    rw [← List.getD_eq_getElem _ 0 h2, L_cap h, ← rets_cap h (by norm_num : 11 < 12)
      (cur := VsC.ptrAtV (curE + D.lcur 11)) (by omega), ← step_rets (rd := rd) (c := c) (curE := curE) (chiE := chiE)
      (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) h (by norm_num) (by omega : j < 6)]
    rw [List.getElem_map]
    refine congrArg (D.val rd c curE chiE olE zvE slE tbE) ?_
    interval_cases j <;> rfl
  · subst hσd
    have := step_rets (rd := rd) (c := c) (curE := curE) (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE)
      (tbE := tbE) h (by norm_num : 11 < 12) (j := 5) (by norm_num)
    rw [rets_cur h (by norm_num)] at this
    exact this

theorem L_next (h : D.Ok) : D.L.1 = (D.layer 11).next (firstOf 11) := by
  rw [L_eq h, D.layer_succ h (by norm_num : 11 < 12)]

/-- The last claim's record. -/
theorem outWs_last (h : D.Ok) : D.outWs ls 11 = [D.L.1.value, sumE D.L.1.mu, VsC.ptrAtV (ls 11),
    VsC.ptrAtV (ls 11 + (D.τ - 3) + 11), VsC.ptrAtV (ls 11 + (D.τ - 3)),
    VsC.ptrAtV (ls 11 + (D.τ - 3) + 36)] ++ D.L.1.mu := by
  rw [outWs, VsC.klOutW, L_next h]

/-- The last claim's record, in memory. -/
theorem last_rec (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) :
    ∀ k < 22, LoadHolds rd (VsC.ptrAtV (c + D.o201)) (264 + k) ((D.outWs ls 11).getD k 0) := by
  intro k hk
  obtain ⟨-, -, -, -, mo, -⟩ := own_mem hm.own
  have := readsAt_getD (mo 11 (by norm_num)) (k := k) (by rw [outWs_length]; exact hk)
  rwa [show c + D.o201 + 22 * (11 + 1) = c + D.o201 + 264 from rfl, ← ptr_mul_gen,
    loadHolds_mul_gen_pow] at this

theorem point_low (h : D.Ok) {t : ℕ} (ht : t < 4) : D.point.getD t 0 = D.I.1.getD t 0 := by
  rw [point, List.append_assoc, List.getD_append _ _ _ _ (by rw [I1_length h]; exact ht)]

theorem sRets_cap (h : D.Ok) : (List.range 5).map (fun j ↦ (D.sRets curE).getD j 0) = D.S.2.2.cap := by
  apply List.ext_getElem (by simp [(S_ok h).2])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, sRets]
  rw [List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2]

set_option maxRecDepth 20000 in
/-- **The inputs' opening, on the layout.** -/
theorem in_on (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) (h6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ)
    (h9 : σ (.n (val% «verify_keccak» "z_vals")) = VsC.ptrAtV zvE)
    (h10 : σ (.n (val% «verify_keccak» "slices")) = VsC.ptrAtV slE)
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h3699 : σ (.n (val% «verify_keccak» "cursor@14")) = VsC.ptrAtV (curE + D.lcur 12 + 12)) :
    σ (.n (val% «verify_keccak» "fs0@15~8")) = VsC.ptrAtV (curE + D.lcur 12 + 12) * gen ∧
      σ (.n (val% «verify_keccak» "fs0@15~9")) = D.L.1.value ∧
      σ (.n (val% «verify_keccak» "fs0@15~11")) = VsC.ptrAtV zvE * gen ^ 39 ∧
      (∀ j < 7, σ (.n ((val% «verify_keccak» "fs0@15") + j)) = (D.iRets curE).getD j 0) ∧
      σ (.n (val% «verify_keccak» "mu_at_low@16")) = multilinearEval D.L.1.mu D.I.1 ∧
      σ (.n (val% «verify_keccak» "in_slot")) = VsC.ptrAtV zvE * gen ^ 39 * gen ^ D.τ ∧
      σ (.n (val% «verify_keccak» "fs0@16~7")) = 0 ∧ σ (.n (val% «verify_keccak» "fs0@16~8")) = 0 ∧
      (∀ j < 7, σ (.n ((val% «verify_keccak» "fs0@16") + j)) = (D.sRets curE).getD j 0) ∧
      D.sF.pend.length = rateScalars ∧ capOf D.sF.perm = (cap5 1735).map σ ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInT next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkInT, GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_right _ hst))
  -- the memory
  have hrec := last_rec hm
  rw [outWs_last h] at hrec
  obtain ⟨-, -, -, -, -, -, -, -, m3987⟩ := own_mem hm.own
  obtain ⟨-, -, -, -, -, -, msl⟩ := xs_reads h hm.cur
  have hmuL : D.L.1.mu.length = 16 := by rw [L_next h]; exact keccakInstanceWeights_length _
  have hv : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 264 D.L.1.value := by
    rw [h201]; simpa using hrec 0 (by norm_num)
  have hmu : ∀ k < 16, LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) (270 + k) (D.L.1.mu.getD k 0) := by
    intro k hk
    have := hrec (6 + k) (by omega)
    rw [List.getD_append_right _ _ _ _ (by simp)] at this
    rw [h201, show 270 + k = 264 + (6 + k) by omega]
    simpa using this
  have hlow : ∀ t < 4, LoadHolds rd (σ (.n (val% «verify_keccak» "z_vals"))) (39 + t) (D.I.1.getD t 0) := by
    intro t ht
    rw [h9, ← point_low h ht, ← loadHolds_mul_gen_pow]
    exact readsAt_getD hm.pt (by rw [point_length h]; omega)
  have a3987 : σ (.n (val% «verify_keccak» "low_tree")) = VsC.ptrAtV (c + D.τ + 382) := by
    subst hσd; exact val_alloc h (.n (val% «verify_keccak» "low_tree"), .inl 30) (by simp [vkAllocs])
  have hT : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n (val% «verify_keccak» "low_tree")))
      (2 ^ t - 2 + i) ((eqKernel (D.I.1.take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 4 ≤ D.I.1.length := by rw [I1_length h]
    rw [a3987, ← eqLevels_getD hl t h1 h2 i hi]
    refine readsAt_getD m3987 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  -- the calls' returns
  have hw : ∀ j < 7, D.w c curE ((val% «verify_keccak» "fs0@16") + j) = (D.sRets curE).getD j 0 :=
    fun j hj ↦ w_s hj
  have hcur : ReadsAt rd (D.w c curE 1333) D.slices := by
    rw [show (1333 : ℕ) = (val% «verify_keccak» "fs0@16") + 5 from rfl, hw 5 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
    rw [show curE + D.lcur 12 + 2 * 6 + 1 + 2 * 4 + 2 * 6 = curE + D.lcur 12 + 33 by omega]
    exact msl
  obtain ⟨e3976, e3977, e3979, e3980, e4104, e4107, e4110, -, hpl, hcp, H⟩ :=
    vkIn_complete hσ hg hv (I1_length h) hlow hT hmuL hmu h.2.2.2.2.2.2.2.2.2.1 hcur
      (by rw [h10]; exact hm.sl)
  have gA : ∀ a, Stmt.atom a ∈ vkInT → Good rd vkSt (D.w c curE) σ a := fun a h ↦ hg _ h
  have c4108 : σ (.n (val% «verify_keccak» "fs0@16~7")) = Guest.word 0 0 :=
    gA (.const (.n (val% «verify_keccak» "fs0@16~7")) (Guest.word 0 0)) (by simp [vkInT])
  have c4109 : σ (.n (val% «verify_keccak» "fs0@16~8")) = Guest.word 0 0 :=
    gA (.const (.n (val% «verify_keccak» "fs0@16~8")) (Guest.word 0 0)) (by simp [vkInT])
  refine ⟨by rw [e3976, h3699], e3977, by rw [e3979, h9], fun j hj ↦ (e3980 j hj).trans (w_i hj),
    e4104, by rw [e4107, h9, h6], by rw [c4108, word_zero], by rw [c4109, word_zero],
    fun j hj ↦ (e4110 j hj).trans (hw j hj), ?_, ?_, H⟩
  all_goals rw [List.map_congr_left (fun j hj ↦ hw j (by have := List.mem_range.1 hj; omega)),
    sRets_cap h] at hpl hcp
  all_goals rw [sF, (S_ok h).1]
  · exact hpl
  · exact hcp

set_option maxRecDepth 20000 in
/-- **The inputs' check and the return, on the layout.** -/
theorem fin_on (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h9 : σ (.n (val% «verify_keccak» "z_vals")) = VsC.ptrAtV zvE)
    (h10 : σ (.n (val% «verify_keccak» "slices")) = VsC.ptrAtV slE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201))
    (h4104 : σ (.n (val% «verify_keccak» "mu_at_low@16")) = multilinearEval D.L.1.mu D.I.1)
    (h4107 : σ (.n (val% «verify_keccak» "in_slot")) = VsC.ptrAtV zvE * gen ^ 39 * gen ^ D.τ)
    (h4116 : σ (.n (val% «verify_keccak» "in_value")) = D.S.2.1)
    (h1251 : σ (.n (val% «verify_keccak» "fs0@15~11")) = VsC.ptrAtV zvE * gen ^ 39) :
    σ (.n (val% «verify_keccak» "last_point")) = VsC.ptrAtV (ls 11) ∧
      σ (.n (val% «verify_keccak» "s81#1")) = 1 + gen ^ (D.τ - 4) ∧ σ (.n (val% «verify_keccak» "s81#2")) = 1 ∧
      σ (.n (val% «verify_keccak» "s81#4")) = VsC.ptrAtV zvE * gen ^ 43 ∧
      ∀ {kret : List E → Prop}, kret [σ (.n (val% «verify_keccak» "nxt[8]@22")),
        σ (.n (val% «verify_keccak» "nxt[9]@22")), σ (.n (val% «verify_keccak» "nxt[10]@22")),
        σ (.n (val% «verify_keccak» "nxt[11]@22")), σ (.n (val% «verify_keccak» "nxt[12]@22")),
        σ (.n (val% «verify_keccak» "cursor@16")) * gen ^ 64, σ (.n (val% «verify_keccak» "x@2"))] →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinT False kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkFinT, GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_right _ hst)
  have hrec := last_rec hm
  rw [outWs_last h] at hrec
  have hpp : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 266 (VsC.ptrAtV (ls 11)) := by
    rw [h201]; simpa using hrec 2 (by norm_num)
  -- the last claim's record
  have hcr := recs h hm 12 le_rfl
  have hc12 : (D.layer 12).c = D.L.1 := by rw [L_eq h]; rfl
  rw [hc12, show c + D.o201 + 22 * 12 = (c + D.o201) + 264 from rfl, ← ptr_mul_gen, ← h201] at hcr
  obtain ⟨-, hptL, -, -, -, ⟨pp, hpp', hpt⟩, lp, lanes, hlp, hlen, hlanes, hrest⟩ := hcr
  simp only [show decide ((12 : ℕ) = 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at hrest
  obtain ⟨lc, fl, loc, hlc, hlocL, hloc, -, -, hw⟩ := hrest
  rw [loadHolds_mul_gen_pow] at hpp' hlp hlc
  have epp : pp = VsC.ptrAtV (ls 11) := loadHolds_unique hpp' hpp
  have hslot : ReadsAt rd (σ (.n (val% «verify_keccak» "in_slot"))) D.S.1 := by
    rw [h4107]
    have := (readsAt_append.1 hm.pt).2
    rw [List.length_append, I1_length h, List.length_take, L_point h,
      show min (D.τ - 4) (D.τ - 3) = D.τ - 4 by omega, show 4 + (D.τ - 4) = D.τ by omega] at this
    exact this
  -- the check
  have hdot := vk_in_check (τ := D.τ) (by omega) hptL hlocL hw (S1_length h)
    h.2.2.2.2.2.2.2.2.2.1 (F := fun l ↦ ∑ m ∈ range 2,
      eqAt [D.L.1.point.getD (D.τ - 4) 0] m * eqAt D.S.1 (25 * (0 + m) + l))
    (Sh := fun r ↦ ∑ z ∈ range 64, D.slices.getD z 0 * eqAt (loc.take 6) ((z + r) % 64))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (μ := 1) (one_mul _)
  rw [one_mul] at hdot
  have hchk := h.2.2.2.2.2.2.2.2.2.2.2
  rw [hdot] at hchk
  obtain ⟨e4977, e6580, e6581, e6583, H⟩ := vkFin_complete hσ hg (by omega) h17 hpp' hpt hptL
    hlc hloc hlocL hlp hlanes hlen hslot (S1_length h) (by rw [h10]; exact hm.sl)
    h.2.2.2.2.2.2.2.2.2.1 (by rw [h4104, h4116, ← hchk]) (by rw [h1251, h9])
  exact ⟨by rw [e4977, epp], by rw [e6580, h17], e6581, by rw [e6583, h9], H⟩

end VkData

end
end LeanVM.Guest.B1.VerifySub
