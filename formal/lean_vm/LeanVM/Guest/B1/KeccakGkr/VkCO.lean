/-
  LeanVM.Guest.B1.KeccakGkr.VkCO

  `verify_keccak`'s openings on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCN

/-!
# The openings, on the layout

`rets_good`: a call's returns are the oracle's. `step_rets`: layer `s`'s returns are its honest
ones. `out_on`: the committed outputs' opening holds on the layout, its check by the honest run's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **A call's returns are the oracle's.** -/
theorem rets_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ s ∈ pre, pinB s = false → GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap Main.Stmt.callS, ∀ v ∈ x.2.2.2, σ v = w v.idx := by
  intro x hx v hv
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  cases s with
  | call f args rets =>
    simp only [Main.Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    exact hg _ hs rfl v hv
  | callIf c f args =>
    simp only [Main.Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    simp at hv
  | _ => simp [Main.Stmt.callS] at hsx

namespace VkData

variable {D : VkData} {rd : Reader} {B curE chiE olE zvE slE : ℕ} {ls : ℕ → ℕ}

theorem calls_good (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE) :
    ∀ x ∈ vkCalls, ∀ v ∈ x.2.2.2, σ v = D.w B curE v.idx := by
  have hg : ∀ s ∈ vkPre, pinB s = false → GoodS rd vkSt (D.w B curE) σ s := fun s hs hp ↦ by
    subst hσd; exact (val_good h).2.1 s (by rw [vkT_pre]; exact List.mem_append_left _ hs) hp
  rw [← vkPre_kernel.2.2.2.2]
  exact rets_good hg

/-- **Layer `s`'s returns are its honest ones.** -/
theorem step_rets (h : D.Ok) {σ : Val} (hσd : σ = D.val rd B curE chiE olE zvE slE) {s : ℕ}
    (hs : s < 12) {j : ℕ} (hj : j < 6) :
    σ (.n (stepE s - 6 + j)) = ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD j 0 := by
  have hm : stepCall s ∈ vkCalls :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩))
  have hE := stepE_eq s hs
  have hv : V.n (stepE s - 6 + j) ∈ (stepCall s).2.2.2 := by
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp only [stepCall, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepTailSz, ↓reduceIte] at hE; congr 1⟩
    · simp only [stepCall, show s ≠ 0 by omega, ↓reduceIte, List.mem_map, List.mem_range]
      exact ⟨j, hj, by simp only [stepTailSz, show s ≠ 0 by omega, ↓reduceIte] at hE; congr 1; omega⟩
  rw [calls_good h hσd _ hm _ hv]
  exact w_layer hs hj

theorem beta_cap_length (s : ℕ) : ((D.layer s).beta (firstOf s)).2.cap.length = 5 :=
  (sq_ok _).2.1

theorem rets_cap (h : D.Ok) {s : ℕ} (hs : s < 12) {cur : E} {j : ℕ} (hj : j < 5) :
    ((D.layer s).rets (firstOf s) cur).getD j 0 = (D.chain (s + 1)).2.cap.getD j 0 := by
  rw [D.layer_succ h hs, LayerData.rets,
    List.getD_append _ _ _ _ (by rw [beta_cap_length]; exact hj)]

theorem rets_cur (h : D.Ok) {s : ℕ} (hs : s < 12) :
    ((D.layer s).rets (firstOf s) (ptr (curE + D.lcur s))).getD 5 0 = ptr (curE + D.lcur (s + 1)) := by
  rw [LayerData.rets, List.getD_append_right _ _ _ _ (by rw [beta_cap_length]),
    beta_cap_length, ptr_mul_gen, D.layer_y h hs.le]
  simp only [Nat.sub_self, List.getD_cons_zero, lcur]
  congr 1
  ring

theorem L_cap (h : D.Ok) (j : ℕ) :
    D.L.2.cap.getD j 0 = (D.chain 12).2.cap.getD j 0 := by rw [L_eq h]

set_option maxRecDepth 20000 in
/-- **The committed outputs' opening, on the layout.** -/
theorem out_on (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE) (h6 : σ (.n 6) = gen ^ D.τ)
    (h9 : σ (.n 9) = ptr zvE) (h17 : σ (.n 17) = gen ^ (D.τ - 4)) (h58 : σ (.n 60) = ptr B)
    (h274 : σ (.n 276) = ptr (B + D.o274)) :
    (cap5 957).map σ = D.L.2.cap ∧ σ (.n 962) = D.cL curE ∧
      σ (.n 963) = ptr zvE * gen ^ D.τ ∧ σ (.n 964) = 0 ∧ σ (.n 965) = 0 ∧
      (∀ j < 7, σ (.n (966 + j)) = (D.oRets curE).getD j 0) ∧ σ (.n 973) = D.word ∧
      (σ (.n 980), σ (.n 982)) = Keccak.scalarCells D.word dsObserve ∧
      σ (.n 1243) = 1 + gen ^ (D.τ - 4) ∧ σ (.n 1244) = 1 ∧ σ (.n 1246) = ptr zvE * gen ^ 4 ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkOutT next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkOutT, GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hst)))
  -- the calls' returns
  have hcg := calls_good h hσd
  have eO : ∀ j < 7, σ (.n (966 + j)) = (D.oRets curE).getD j 0 := fun j hj ↦ by
    rw [hcg (none, "keccak_plain_rounds__L6_L0", [.n 957, .n 958, .n 959, .n 960, .n 961,
      .n 964, .n 965, .n 962, .n 193, .n 963], (List.range 7).map fun j ↦ .n (966 + j))
      (by simp [vkCalls]) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)]
    exact w_o hj
  have hcL : D.L.2.cap.length = 5 := (L_ok h).2.1
  have hoc : ∀ j < 5, (D.oRets curE).getD j 0 = D.O.2.2.cap.getD j 0 := fun j hj ↦ by
    rw [oRets, List.getD_append _ _ _ _ (by rw [(O_ok h).2.1]; exact hj)]
  have e3699 : σ (.n 971) = ptr (curE + D.lcur 12 + 12) := by
    have := eO 5 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2.1]), (O_ok h).2.1]
    simp [cL, ptr_mul_gen]
  have e3700 : σ (.n 972) = D.O.2.1 := by
    have := eO 6 (by norm_num)
    rw [this, oRets, List.getD_append_right _ _ _ _ (by rw [(O_ok h).2.1]; norm_num), (O_ok h).2.1]
    rfl
  -- the memory
  obtain ⟨m58, -, -, -, m274, -, -⟩ := own_mem (by omega) hm.own
  have mop := memL_entry hm.lin (b := zvE) (ws := D.op) (by simp [lin])
  obtain ⟨-, -, -, mword, -⟩ := xs_reads h (memL_entry hm.lin (b := curE) (ws := D.xs) (by simp [lin]))
  have hslot : ReadsAt rd (σ (.n 9) * σ (.n 6)) D.O.1 := by
    rw [h9, h6]
    rw [op_eq] at mop
    have := (readsAt_append.1 mop).2
    rwa [List.take_append_drop, inst_length h] at this
  have hr0 : LoadHolds rd (σ (.n 60) * σ (.n 17)) 0 (D.seg.getD 0 0) := by
    rw [h58, h17, loadHolds_mul_gen_pow, add_zero, ← c0_point_seg h]
    exact ClaimLay.getD_load m58 (by rw [c0_point_length h]; omega)
  have hL : ∀ lane < 25, LoadHolds rd (σ (.n 276)) (30 + lane) ((eqKernel D.rl).getD lane 0) := by
    intro lane hl
    have := lanes_first m274 lane (by simp [eqKernel_length, rl_length]; omega)
    rw [← ptr_mul_gen, loadHolds_mul_gen_pow] at this
    rw [h274, List.getD_eq_getElem _ _ (by simp [eqKernel_length, rl_length]; omega)]
    simpa using this
  -- the check
  have hchk : (∑ lane ∈ range 25, (∑ m ∈ range 1, eqAt [D.seg.getD 0 0] m *
      eqAt D.O.1 (25 * (1 + m) + lane)) * (eqKernel D.rl).getD lane 0) * D.word = σ (.n 972) := by
    have hspec := vk_out_check (τ := D.τ) D.inst D.outs D.committed (D.seg.getD 0 0) D.rl
      (by simp [inst_length h]) (O1_length h) (word := 1) (mul_one _)
    rw [mul_one] at hspec
    rw [← hspec, e3700]
    have := h.2.2.2.2.2.2.2.2.2.2.2.1
    rw [← this]
    congr 4
  obtain ⟨e3691, -, e3701, cells, -, -, e3971, e3972, e3974, H⟩ :=
    vkOut_complete hσ hg h17 (by rw [e3699]; exact mword) hslot (O1_length h) hr0 hL hchk
  have gA : ∀ a, Stmt.atom a ∈ vkOutT → Good rd vkSt (D.w B curE) σ a := fun a h ↦ hg _ h
  have c3692 : σ (.n 964) = Guest.word 0 0 0 :=
    gA (.const (.n 964) (Guest.word 0 0)) (by simp [vkOutT])
  have c3693 : σ (.n 965) = Guest.word 0 0 0 :=
    gA (.const (.n 965) (Guest.word 0 0)) (by simp [vkOutT])
  refine ⟨?_, ?_, by rw [e3691, h9, h6], by rw [c3692, word_zero], by rw [c3693, word_zero], eO,
    e3701, cells, by rw [e3971, h17], e3972, by rw [e3974, h9], H⟩
  · apply List.ext_getElem (by simp [cap5, hcL])
    intro j h1 h2
    simp only [cap5, List.length_map, List.length_cons, List.length_nil] at h1
    rw [← List.getD_eq_getElem _ 0 h2, L_cap h, ← rets_cap h (by norm_num : 11 < 12)
      (cur := ptr (curE + D.lcur 11)) (by omega), ← step_rets h hσd (by norm_num) (by omega : j < 6)]
    interval_cases j <;> rfl
  · have := step_rets h hσd (by norm_num : 11 < 12) (j := 5) (by norm_num)
    rw [rets_cur h (by norm_num)] at this
    exact this

end VkData

end
end LeanVM.Guest.B1.VerifySub
