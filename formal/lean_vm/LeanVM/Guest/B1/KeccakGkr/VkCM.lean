/-
  LeanVM.Guest.B1.KeccakGkr.VkCM

  `verify_keccak`'s head and first claim record on its layout.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCL

/-!
# The head and the first record, on the layout

`head_first`: on a memory holding the layout (`Mem`), the honest valuation satisfies the head and
the first claim's record, and the values the rest reads are the honest ones: the arguments, `y` in
the exponent, the buffers' bases, the segment and lane coordinates, the sponge before the layers,
the committed word and its cells.
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

set_option maxRecDepth 20000 in
/-- **The head and the first record, on the layout.** -/
theorem head_first (h : D.Ok) (hm : D.Mem rd B curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd B curE chiE olE zvE slE tbE) :
    (∀ i < 5, σ (.n i) = D.f.getD i 0) ∧ σ (.n 5) = ptr curE ∧ σ (.n 6) = gen ^ D.τ ∧
    σ (.n 7) = ptr chiE ∧ σ (.n 8) = ptr olE ∧ σ (.n 9) = ptr zvE ∧ σ (.n 10) = ptr slE ∧
    σ (.n 18) = gen ^ (D.τ - 4) ∧ σ (.n 34) = gen ^ ((D.τ - 3) / 8) ∧
    σ (.n 48) = gen ^ ((D.τ - 3) % 8) ∧ σ (.n 61) = ptr B ∧
    σ (.n 63) = 1 + gen ^ (D.τ - 4) ∧ σ (.n 64) = 1 ∧ σ (.n 66) = ptr chiE * gen ^ 4 ∧
    σ (.n 67) = ptr B * gen ^ (D.τ - 4) ∧ σ (.n 86) = D.seg.getD 0 0 ∧
    σ (.n 87) = ptr (B + (D.τ - 3)) ∧ (cap5 152).map σ = (D.layer 0).cap ∧
    σ (.n 158) = D.committed ∧ (σ (.n 159), σ (.n 160)) = D.cells 0 ∧
    σ (.n 161) = ptr (B + D.o201) ∧ σ (.n 163) = ptr (B + D.τ + 288) ∧
    σ (.n 234) = ptr (B + D.o274) ∧ σ (.n 342) = ptr (B + D.τ + 380) ∧
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (vkHeadT ++ vkFirstT) next kret := by
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w B curE) σ s := by
    subst hσd; exact (val_good h).2.1
  have hpar : ∀ i < 12, σ (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0 := by
    subst hσd; exact (val_good h).2.2
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hchis := h.2.2.1
  have houts : D.outs.length = 25 := h.2.2.2.1
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := five_of_length' h.2.2.2.2.1
  have pa : ∀ i < 12, σ (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0 := hpar
  have p0 : σ (.n 0) = f0 := by rw [pa 0 (by norm_num), args, hf]; rfl
  have p1 : σ (.n 1) = f1 := by rw [pa 1 (by norm_num), args, hf]; rfl
  have p2 : σ (.n 2) = f2 := by rw [pa 2 (by norm_num), args, hf]; rfl
  have p3 : σ (.n 3) = f3 := by rw [pa 3 (by norm_num), args, hf]; rfl
  have p4 : σ (.n 4) = f4 := by rw [pa 4 (by norm_num), args, hf]; rfl
  have p5 : σ (.n 5) = ptr curE := by rw [pa 5 (by norm_num), args, hf]; rfl
  have p6 : σ (.n 6) = gen ^ D.τ := by rw [pa 6 (by norm_num), args, hf]; rfl
  have p7 : σ (.n 7) = ptr chiE := by rw [pa 7 (by norm_num), args, hf]; rfl
  have p8 : σ (.n 8) = ptr olE := by rw [pa 8 (by norm_num), args, hf]; rfl
  have p9 : σ (.n 9) = ptr zvE := by rw [pa 9 (by norm_num), args, hf]; rfl
  have p10 : σ (.n 10) = ptr slE := by rw [pa 10 (by norm_num), args, hf]; rfl
  -- the buffers' bases
  have ha : ∀ x ∈ vkAllocs, σ x.1 = D.w B curE x.1.idx := by subst hσd; exact val_alloc h
  have a58 : σ (.n 61) = ptr B := ha (.n 61, .inr (.n 60)) (by simp [vkAllocs])
  have a90 : σ (.n 87) = ptr (B + (D.τ - 3)) := ha (.n 87, .inl 5) (by simp [vkAllocs])
  have a201 : σ (.n 161) = ptr (B + D.o201) := ha (.n 161, .inl 286) (by simp [vkAllocs])
  have a203 : σ (.n 163) = ptr (B + D.τ + 288) := ha (.n 163, .inl 30) (by simp [vkAllocs])
  have a274 : σ (.n 234) = ptr (B + D.o274) := ha (.n 234, .inl 62) (by simp [vkAllocs])
  have a382 : σ (.n 342) = ptr (B + D.τ + 380) := ha (.n 342, .inl 2) (by simp [vkAllocs])
  -- the memory
  obtain ⟨m58, m90, m201, m203, m274, m382, -⟩ := own_mem (by omega) hm.own
  have mchis := memL_entry hm.lin (b := chiE) (ws := D.chis) (by simp [lin])
  have mouts := memL_entry hm.lin (b := olE) (ws := D.outs) (by simp [lin])
  have mop := memL_entry hm.lin (b := zvE) (ws := D.op) (by simp [lin])
  obtain ⟨mcom, -⟩ := xs_reads h (memL_entry hm.lin (b := curE) (ws := D.xs) (by simp [lin]))
  -- the head
  have mH : ∀ s ∈ vkHeadT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hs))))
  have hbits : ∀ j < 5, σ (.n (21 + j)) = Value.bitE ((D.τ - 3).testBit j) := by
    intro j hj
    have g := hG (.atom (.hint (.bitsExp (.n 20) 5 (.stack [.n 21, .n 22, .n 23, .n 24, .n 25]))))
      (mH _ (by
      rw [vkHeadT]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (by simp [vkBitsT]))))))) rfl
    exact (g (.n (21 + j)) (by simp; omega)).trans (w_bits hj)
  obtain ⟨h17, -, h33, h47, e52, e60, e61, e63, e64, q1, q5, e191, -, fcells, HH⟩ :=
    vkHead_complete (S := vkSt) (w := D.w B curE) hσ (fun s hs hp ↦ hG s (mH s hs) hp)
      (fun d off ↦ not_mem_of_noStoreVia vk_ker2.1 (p := .n 7) (by simp) d off)
      (fun d off ↦ not_mem_of_noStoreVia vk_ker2.1 (p := .n 5) (by simp) d off) hτ1 hτ2 p6 hbits
      (chis := D.chis) (by rw [p7]; exact mchis) (by omega) (committed := D.committed)
      (by rw [p5]; exact mcom)
  rw [p0, p1, p2, p3, p4, ← hf] at q1
  have hsq1 : D.sq1 = ([σ (.n 86)], ⟨(cap5 81).map σ, []⟩) := by
    rw [sq1, keccakSegmentBits_eq]; exact q1
  have hseg : D.seg = [σ (.n 86)] := by rw [seg, hsq1]
  have hsq2 : D.sq2 = ((List.range 5).map (fun i ↦ σ (.n (101 + 14 * i))), ⟨(cap5 152).map σ, []⟩) := by
    rw [sq2, hsq1]; exact q5
  have hrl : D.rl = (List.range 5).map (fun i ↦ σ (.n (101 + 14 * i))) := by rw [rl, hsq2]
  have hcap0 : (cap5 152).map σ = (D.layer 0).cap := by
    simp [layer, chain_zero, S0, hsq2, Fs.absorb, rateScalars]
  have e89 : σ (.n 86) = D.seg.getD 0 0 := by rw [hseg]; rfl
  have e64' : σ (.n 67) = ptr B * gen ^ (D.τ - 4) := by rw [e64, a58, h17]
  have l64 : LoadHolds rd (σ (.n 67)) 0 (σ (.n 86)) := by
    rw [e64', loadHolds_mul_gen_pow, add_zero, e89, ← c0_point_seg h]
    exact ClaimLay.getD_load m58 (by rw [c0_point_length h]; omega)
  have l90 : ∀ i < 5, LoadHolds rd (σ (.n 87)) i (σ (.n (101 + 14 * i))) := by
    intro i hi
    have := ClaimLay.getD_load m90 (k := i) (by rw [rl_length]; exact hi)
    rw [a90]
    rwa [hrl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
      at this
  have l9 : ∀ i < 4, LoadHolds rd (σ (.n 9)) i (σ (.n (55 + i))) := by
    intro i hi
    rw [p9, e52 i hi, ← op_getD h (by omega)]
    exact ClaimLay.getD_load mop (by rw [op_length h]; omega)
  -- the first record
  have mF : ∀ s ∈ vkFirstT, GoodS rd vkSt (D.w B curE) σ s := fun s hs ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hs))))
  have hzv : ∀ i < 4, LoadHolds rd (σ (.n 9)) i (D.chis.getD i 0) := fun i hi ↦ by
    rw [← e52 i hi]; exact l9 i hi
  have hrlL : ∀ i < 5, LoadHolds rd (σ (.n 87)) i (D.rl.getD i 0) := fun i hi ↦ by
    rw [hrl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact l90 i hi
  have hT203 : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n 163)) (2 ^ t - 2 + i)
      ((eqKernel ((D.chis.take 4).take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 4 ≤ (D.chis.take 4).length := by simp; omega
    rw [a203, ← eqLevels_getD hl t h1 h2 i hi]
    refine ClaimLay.getD_load m203 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hT274 : ∀ t, 1 ≤ t → t ≤ 5 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n 234)) (2 ^ t - 2 + i)
      ((eqKernel (D.rl.take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 5 ≤ D.rl.length := by rw [rl_length]
    rw [a274, ← eqLevels_getD hl t h1 h2 i hi]
    refine ClaimLay.getD_load m274 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hT382 : ∀ i < 2, LoadHolds rd (σ (.n 342)) i ((eqKernel [σ (.n 86)]).getD i 0) := by
    intro i hi
    rw [a382, ← hseg]
    exact ClaimLay.getD_load m382 (by rw [eqKernel_length, seg_length]; simpa using hi)
  obtain ⟨e202, e381, e258, e487, HF⟩ := vkFirst_complete (C := fun _ _ _ ↦ True) hσ mF
    (by omega) hzv (rl_length) hrlL l64
    houts (by rw [p8]; exact mouts) hT203 hT274 hT382
  -- the first record's stores
  have hcl : ∀ j < 22, LoadHolds rd (σ (.n 161)) j ((D.cw0 B).getD j 0) := fun j hj ↦ by
    rw [a201, ← claims_cw0 (ls := ls) h hj]
    exact ClaimLay.getD_load m201 (by
      rw [claims, List.length_append]; simp [cw0, c0_mu h]; omega)
  have s1 : LoadHolds rd (σ (.n 161)) 1 (σ (.n 162)) := by rw [e202]; exact hcl 1 (by norm_num)
  have s2 : LoadHolds rd (σ (.n 161)) 2 (σ (.n 61)) := by rw [a58]; exact hcl 2 (by norm_num)
  have s6 : ∀ i < 16, LoadHolds rd (σ (.n 161)) (6 + i) (σ (.n (218 + i))) := by
    intro i hi
    have := hcl (6 + i) (by omega)
    rw [e258 i hi]
    rwa [cw0, List.getD_append_right _ _ _ _ (by simp),
      show 6 + i - [D.c0.value, 1, ptr B, ptr (B + D.o274 + 30), 0, 0].length = i by simp,
      c0_mu_eq h] at this
  have s3 : LoadHolds rd (σ (.n 161)) 3 (σ (.n 341)) := by
    rw [e381, a274, ptr_mul_gen]; exact hcl 3 (by norm_num)
  have s0 : LoadHolds rd (σ (.n 161)) 0 (σ (.n 447)) := by
    have := hcl 0 (by norm_num)
    suffices hv : (D.cw0 B).getD 0 0 = σ (.n 447) by rwa [hv] at this
    rw [e487, e191]
    simp only [cw0, c0, vkFirst, keccakSegments_eq, show 2 - 1 = 1 from rfl]
    rw [hseg, dot_eq _ _ (by simp [eqKernel_length, rl_length, houts])]
    simp only [List.length_take, eqKernel_length, rl_length, show min 25 (2 ^ 5) = 25 from rfl]
    refine congrArg (D.committed + (eqKernel [σ (.n 86)]).getD 1 0 * ·)
      (Finset.sum_congr rfl fun k hk ↦ ?_)
    simp [List.getD_eq_getElem?_getD, Finset.mem_range.1 hk]
  refine ⟨fun i hi ↦ ?_, p5, p6, p7, p8, p9, p10, h17, h33, h47, a58,
    by rw [e60, h17], e61, by rw [e63, p7], e64', e89, a90, hcap0, e191, fcells, a201, a203,
    a274, a382, fun {next kret} hn ↦ ?_⟩
  · interval_cases i <;> simp [p0, p1, p2, p3, p4, hf]
  · rw [holdsList_append]
    exact HH l9 l64 l90 (HF s1 s2 s6 s3 s0 hn)

end VkData

end
end LeanVM.Guest.B1.VerifySub
