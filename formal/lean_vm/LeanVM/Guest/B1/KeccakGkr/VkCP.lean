/-
  LeanVM.Guest.B1.KeccakGkr.VkCP

  `verify_keccak`'s inputs' opening, check and return on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCO

/-!
# The inputs' opening and the return, on the layout

`in_on`: the inputs' opening holds on the layout, and the ring map's first challenge and the
sponge after it are the honest run's (`D.fin`). `fin_on`: the inputs' check holds by the honest
run's, and the body returns the honest words.
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

theorem L_next (h : D.Ok) : D.L.1 = (D.layer 11).next (firstOf 11) := by
  rw [L_eq h, D.layer_succ h (by norm_num : 11 < 12)]

/-- The last claim's record. -/
theorem outWs_last (h : D.Ok) : D.outWs ls 11 = [D.L.1.value, sumE D.L.1.mu, ptr (ls 11),
    ptr (ls 11 + (D.layer 11).y + 139), ptr (ls 11 + (D.layer 11).y + 128),
    ptr (ls 11 + (D.layer 11).y + 164)] ++ D.L.1.mu := by
  rw [outWs, LayerData.outW, L_next h]

/-- The last claim's record, in memory. -/
theorem last_rec (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) :
    ∀ k < 22, LoadHolds rd (ptr (B + D.o201)) (264 + k) ((D.outWs ls 11).getD k 0) := by
  intro k hk
  obtain ⟨-, -, m201, -⟩ := own_mem (by have := h.1; omega) hm.own
  have := claims_slice h (by norm_num : 11 < 12) m201
  rw [← ptr_mul_gen] at this
  have := ClaimLay.getD_load this (k := k) (by rw [outWs_length]; exact hk)
  rwa [loadHolds_mul_gen_pow] at this

theorem point_low (h : D.Ok) {t : ℕ} (ht : t < 4) : D.point.getD t 0 = D.I.1.getD t 0 := by
  rw [point, List.append_assoc, List.getD_append _ _ _ _ (by rw [I1_length h]; exact ht)]

theorem sRets_cap (h : D.Ok) : (List.range 5).map (fun j ↦ (D.sRets curE).getD j 0) = D.S.2.2.cap := by
  apply List.ext_getElem (by simp [(S_ok h).2])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, sRets]
  rw [List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2]

set_option maxRecDepth 20000 in
/-- **The inputs' opening, on the layout.** -/
theorem in_on (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (h6 : σ (.n 6) = gen ^ D.τ)
    (h9 : σ (.n 9) = ptr zvE) (h10 : σ (.n 10) = ptr slE) (h201 : σ (.n 161) = ptr (B + D.o201))
    (h3699 : σ (.n 929) = ptr (curE + D.lcur 12 + 12)) :
    σ (.n 1199) = ptr (curE + D.lcur 12 + 12) * gen ∧ σ (.n 1200) = D.L.1.value ∧
      σ (.n 1202) = ptr zvE * gen ^ 39 ∧ (∀ j < 7, σ (.n (1203 + j)) = (D.iRets curE).getD j 0) ∧
      σ (.n 1327) = multilinearEval D.L.1.mu D.I.1 ∧ σ (.n 1330) = ptr zvE * gen ^ 39 * gen ^ D.τ ∧
      σ (.n 1331) = 0 ∧ σ (.n 1332) = 0 ∧ (∀ j < 7, σ (.n (1333 + j)) = (D.sRets curE).getD j 0) ∧
      D.sF.pend.length = rateScalars ∧ capOf D.sF.perm = (cap5 1740).map σ ∧
      ∀ {next : Prop} {kret : List E → Prop}, next →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkInT next kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkInT, GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_right _ hst))
  -- the memory
  have hrec := last_rec h hm
  rw [outWs_last h] at hrec
  obtain ⟨-, -, -, -, -, -, m3987⟩ := own_mem (by omega) hm.own
  have mpt := memL_entry hm.lin (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp [lin])
  obtain ⟨-, -, -, -, -, -, msl⟩ := xs_reads h (memL_entry hm.lin (b := curE) (ws := D.xs)
    (by simp [lin]))
  have msl' := memL_entry hm.lin (b := slE) (ws := D.slices) (by simp [lin])
  have hmuL : D.L.1.mu.length = 16 := by rw [L_next h]; exact keccakInstanceWeights_length _
  have hv : LoadHolds rd (σ (.n 161)) 264 D.L.1.value := by
    rw [h201]; simpa using hrec 0 (by norm_num)
  have hmu : ∀ k < 16, LoadHolds rd (σ (.n 161)) (270 + k) (D.L.1.mu.getD k 0) := by
    intro k hk
    have := hrec (6 + k) (by omega)
    rw [List.getD_append_right _ _ _ _ (by simp)] at this
    rw [h201, show 270 + k = 264 + (6 + k) by omega]
    simpa using this
  have hlow : ∀ t < 4, LoadHolds rd (σ (.n 9)) (39 + t) (D.I.1.getD t 0) := by
    intro t ht
    rw [h9, ← point_low h ht, ← loadHolds_mul_gen_pow, ptr_mul_gen]
    exact ClaimLay.getD_load mpt (by rw [point_length h]; omega)
  have a3987 : σ (.n 1210) = ptr (B + D.τ + 382) := by
    subst hσd; exact val_alloc h (.n 1210, .inl 30) (by simp [vkAllocs])
  have hT : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n 1210)) (2 ^ t - 2 + i)
      ((eqKernel (D.I.1.take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 4 ≤ D.I.1.length := by rw [I1_length h]
    rw [a3987, ← eqLevels_getD hl t h1 h2 i hi]
    refine ClaimLay.getD_load m3987 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  -- the calls' returns
  have hcg := calls_good h hσd
  have hw : ∀ j < 7, D.w B curE (1333 + j) = (D.sRets curE).getD j 0 := fun j hj ↦ w_s hj
  have hcur : ReadsAt rd (D.w B curE 1338) D.slices := by
    rw [show (1338 : ℕ) = 1333 + 5 from rfl, hw 5 (by norm_num), sRets,
      List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
    rw [show curE + D.lcur 12 + 2 * 6 + 1 + 2 * 4 + 2 * 6 = curE + D.lcur 12 + 33 by omega]
    exact msl
  obtain ⟨e3976, e3977, e3979, e3980, e4104, e4107, e4110, -, hpl, hcp, H⟩ :=
    vkIn_complete hσ hg hv (I1_length h) hlow hT hmuL hmu h.2.2.2.2.2.2.2.2.2.1 hcur
      (by rw [h10]; exact msl')
  have gA : ∀ a, Stmt.atom a ∈ vkInT → Good rd vkSt (D.w B curE) σ a := fun a h ↦ hg _ h
  have c4108 : σ (.n 1331) = Guest.word 0 0 :=
    gA (.const (.n 1331) (Guest.word 0 0)) (by simp [vkInT])
  have c4109 : σ (.n 1332) = Guest.word 0 0 :=
    gA (.const (.n 1332) (Guest.word 0 0)) (by simp [vkInT])
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
theorem fin_on (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) (h9 : σ (.n 9) = ptr zvE)
    (h10 : σ (.n 10) = ptr slE) (h17 : σ (.n 18) = gen ^ (D.τ - 4)) (h201 : σ (.n 161) = ptr (B + D.o201))
    (h4104 : σ (.n 1327) = multilinearEval D.L.1.mu D.I.1)
    (h4107 : σ (.n 1330) = ptr zvE * gen ^ 39 * gen ^ D.τ) (h4116 : σ (.n 1339) = D.S.2.1)
    (h1251 : σ (.n 1202) = ptr zvE * gen ^ 39) :
    σ (.n 1745) = ptr (ls 11) ∧ σ (.n 3360) = 1 + gen ^ (D.τ - 4) ∧ σ (.n 3361) = 1 ∧
      σ (.n 3363) = ptr zvE * gen ^ 43 ∧
      ∀ {kret : List E → Prop}, kret [σ (.n 1740), σ (.n 1741), σ (.n 1742), σ (.n 1743),
        σ (.n 1744), σ (.n 1338) * gen ^ 64, σ (.n 931)] →
        Stmt.HoldsList (fun _ _ _ ↦ True) rd σ vkFinT False kret := by
  have hτ1 := h.1
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hg : ∀ st ∈ vkFinT, GoodS rd vkSt (D.w B curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_right _ hst)
  have hrec := last_rec h hm
  rw [outWs_last h] at hrec
  have hL := hm.lay 11 (by norm_num)
  rw [layerBufs_eq] at hL
  have mpt := memL_entry hm.lin (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp [lin])
  have msl := memL_entry hm.lin (b := slE) (ws := D.slices) (by simp [lin])
  have hpp : LoadHolds rd (σ (.n 161)) 266 (ptr (ls 11)) := by
    rw [h201]; simpa using hrec 2 (by norm_num)
  have hlc : LoadHolds rd (σ (.n 161)) 268 (ptr (ls 11 + (D.layer 11).y + 128)) := by
    rw [h201]; simpa using hrec 4 (by norm_num)
  have hlp : LoadHolds rd (σ (.n 161)) 267 (ptr (ls 11 + (D.layer 11).y + 139)) := by
    rw [h201]; simpa using hrec 3 (by norm_num)
  have hpt : ReadsAt rd (ptr (ls 11)) D.L.1.point := by
    rw [L1_point h]; exact memL_entry hL (by simp)
  have hloc : ReadsAt rd (ptr (ls 11 + (D.layer 11).y + 128)) ((D.layer 11).locPt (firstOf 11)) :=
    memL_entry hL (by simp)
  have hlanes : ReadsAt rd (ptr (ls 11 + (D.layer 11).y + 139))
      (lanesOut ((D.layer 11).locPt (firstOf 11)) ((D.layer 11).beta (firstOf 11)).1) :=
    memL_entry hL (by simp)
  have hslot : ReadsAt rd (σ (.n 1330)) D.S.1 := by
    rw [h4107]
    have := (readsAt_append.1 mpt).2
    rw [List.length_append, I1_length h, List.length_take, L_point h,
      show min (D.τ - 4) (D.τ - 3) = D.τ - 4 by omega, ptr_mul_gen,
      show zvE + qkeccakVarsCap + (4 + (D.τ - 4)) = zvE + 39 + D.τ by simp; omega] at this
    rwa [ptr_mul_gen, ptr_mul_gen]
  have hlocL := locPt_length h (by norm_num : 11 < 12)
  -- the check
  have hok := D.CL_ok h B ls (s := 12) le_rfl
  simp only [ClaimLay.Ok, CL, show firstOf 12 = 0 from rfl, show (0 : ℕ) = 1 ↔ False by decide,
    ↓reduceIte] at hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hw⟩ := hok
  have hc12 : (D.layer 12).c = D.L.1 := by rw [L_eq h]; rfl
  rw [hc12] at hw
  have hdot := vk_in_check (τ := D.τ) (by omega) (L_point h) hlocL hw (S1_length h)
    h.2.2.2.2.2.2.2.2.2.1 (F := fun l ↦ ∑ m ∈ range 2,
      eqAt [D.L.1.point.getD (D.τ - 4) 0] m * eqAt D.S.1 (25 * (0 + m) + l))
    (Sh := fun r ↦ ∑ z ∈ range 64, D.slices.getD z 0 *
      eqAt (((D.layer 11).locPt (firstOf 11)).take 6) ((z + r) % 64))
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (μ := 1) (one_mul _)
  rw [one_mul] at hdot
  have hchk := h.2.2.2.2.2.2.2.2.2.2.2
  rw [hdot] at hchk
  obtain ⟨e4977, e6580, e6581, e6583, H⟩ := vkFin_complete hσ hg (by omega) h17 hpp hpt (L_point h)
    hlc hloc hlocL hlp hlanes (lanesOut_length _ _) hslot (S1_length h) (by rw [h10]; exact msl)
    h.2.2.2.2.2.2.2.2.2.1 (by rw [h4104, h4116, ← hchk]) (by rw [h1251, h9])
  exact ⟨e4977, by rw [e6580, h17], e6581, by rw [e6583, h9], H⟩

end VkData

end
end LeanVM.Guest.B1.VerifySub
