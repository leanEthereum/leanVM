/-
  LeanVM.Guest.B1.VsC.VkPC

  `verify_keccak` placed: the honest valuation's equations, the head and the first claim's record
  on the layout (the archive's `VkCL`, `VkCM`).
-/

module

public import LeanVM.Guest.B1.VsC.VkPB
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The head and the first record, on the layout

`val_good`: the honest valuation satisfies every statement of the body but the pins, its
parameters are the arguments; `val_alloc`: its buffers' bases are the oracle's. `head_first`: on a
memory holding the layout (`Mem`), the head and the first claim's record hold, and the values the
rest reads are the honest ones.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

theorem alloc_goodP {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ s ∈ pre, pinB s = false → GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap Stmt.allocSz, σ x.1 = w x.1.idx := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  have h := hg s hs
  cases s with
  | atom a =>
    cases a with
    | hint hh =>
      cases hh with
      | alloc d n =>
        simp only [Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h rfl
      | allocDyn d sz =>
        simp only [Stmt.allocSz, Option.some.injEq] at hsx
        subst hsx
        exact h rfl
      | _ => simp [Stmt.allocSz] at hsx
    | _ => simp [Stmt.allocSz] at hsx
  | _ => simp [Stmt.allocSz] at hsx

/-- **A call's returns are the oracle's.** -/
theorem rets_good {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {pre : List Stmt}
    (hg : ∀ s ∈ pre, pinB s = false → GoodS rd S w σ s) :
    ∀ x ∈ pre.filterMap Stmt.callS, ∀ v ∈ x.2.2.2, σ v = w v.idx := by
  intro x hx v hv
  obtain ⟨s, hs, hsx⟩ := List.mem_filterMap.mp hx
  cases s with
  | call f args rets =>
    simp only [Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    exact hg _ hs rfl v hv
  | callIf c f args =>
    simp only [Stmt.callS, Option.some.injEq] at hsx
    subst hsx
    simp at hv
  | _ => simp [Stmt.callS] at hsx

namespace VkData

variable {D : VkData} {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

theorem args_length (h : D.Ok) : (D.args curE chiE olE zvE slE tbE).length = 12 := by
  simp [args, h.2.2.2.2.1]

/-- The facts every section starts from: the values by index, the equations, the arguments. -/
theorem val_good (h : D.Ok) :
    (∀ v, D.val rd c curE chiE olE zvE slE tbE v = D.val rd c curE chiE olE zvE slE tbE (.n v.idx)) ∧
    (∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w c curE) (D.val rd c curE chiE olE zvE slE tbE) s) ∧
    (∀ i < 12, D.val rd c curE chiE olE zvE slE tbE (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0) :=
  ⟨fun v ↦ vkσ_idx v, fun _ hs hp ↦ vk_good (args_length h) hs hp,
    fun _ hi ↦ vk_param (args_length h) hi⟩

theorem val_tabs (h : D.Ok) :
    D.val rd c curE chiE olE zvE slE tbE (.n (val% «verify_keccak» "tabs")) = VsC.ptrAtV tbE := by
  rw [(val_good h).2.2 11 (by norm_num), args,
    List.getD_append_right _ _ _ _ (by rw [h.2.2.2.2.1]; norm_num), h.2.2.2.2.1]
  rfl

/-- Every statement after the head satisfies its equations. -/
theorem val_good' (h : D.Ok) {s : Stmt}
    (hs : s ∈ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT) :
    GoodS rd vkSt (D.w c curE) (D.val rd c curE chiE olE zvE slE tbE) s :=
  (val_good h).2.1 s (by
    rw [vkT]; simp only [List.append_assoc, List.mem_append] at hs ⊢; exact Or.inr hs)
    (by have := List.all_eq_true.mp vk_ker2.2 s hs; simpa using this)

theorem val_alloc (h : D.Ok) :
    ∀ x ∈ vkAllocs, D.val rd c curE chiE olE zvE slE tbE x.1 = D.w c curE x.1.idx := by
  have := alloc_goodP (pre := vkPre) (fun s hs hp ↦ (val_good (rd := rd) (c := c) (curE := curE)
    (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) h).2.1 s
    (by rw [vkT_pre]; exact List.mem_append_left _ hs) hp)
  rwa [vkPre_kernel.2.2.1] at this

theorem calls_good (h : D.Ok) :
    ∀ x ∈ vkCalls, ∀ v ∈ x.2.2.2, D.val rd c curE chiE olE zvE slE tbE v = D.w c curE v.idx := by
  have hg : ∀ s ∈ vkPre, pinB s = false →
      GoodS rd vkSt (D.w c curE) (D.val rd c curE chiE olE zvE slE tbE) s := fun s hs hp ↦
    (val_good h).2.1 s (by rw [vkT_pre]; exact List.mem_append_left _ hs) hp
  rw [← vkPre_kernel.2.2.2]
  exact rets_good hg

set_option maxRecDepth 20000 in
/-- **The head and the first record, on the layout.** -/
theorem head_first (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) :
    (∀ i < 5, σ (.n i) = D.f.getD i 0) ∧ σ (.n (val% «verify_keccak» "cursor@1")) = VsC.ptrAtV curE ∧
    σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ ∧ σ (.n (val% «verify_keccak» "chi")) = VsC.ptrAtV chiE ∧
    σ (.n (val% «verify_keccak» "output_lanes")) = VsC.ptrAtV olE ∧
    σ (.n (val% «verify_keccak» "z_vals")) = VsC.ptrAtV zvE ∧
    σ (.n (val% «verify_keccak» "slices")) = VsC.ptrAtV slE ∧
    σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4) ∧ σ (.n 29) = gen ^ ((D.τ - 3) / krStep) ∧
    σ (.n 48) = gen ^ ((D.τ - 3) % krStep) ∧ σ (.n (val% «verify_keccak» "point")) = VsC.ptrAtV c ∧
    σ (.n (val% «verify_keccak» "s17#1")) = 1 + gen ^ (D.τ - 4) ∧ σ (.n (val% «verify_keccak» "s17#2")) = 1 ∧
    σ (.n (val% «verify_keccak» "s17#4")) = VsC.ptrAtV chiE * gen ^ 4 ∧
    σ (.n (val% «verify_keccak» "segment")) = VsC.ptrAtV c * gen ^ (D.τ - 4) ∧
    σ (.n (val% «verify_keccak» "nxt[0]@1")) = D.seg.getD 0 0 ∧
    σ (.n (val% «verify_keccak» "r_lane")) = VsC.ptrAtV (c + (D.τ - 3)) ∧ (cap5 148).map σ = (D.layer 0).cap ∧
    σ (.n (val% «verify_keccak» "x@1")) = D.committed ∧
    (σ (.n (val% «verify_keccak» "value_rate[0]")), σ (.n (val% «verify_keccak» "value_rate[1]"))) = D.cells 0 ∧
    σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201) ∧
    σ (.n (val% «verify_keccak» "mu_tree")) = VsC.ptrAtV (c + D.τ + 288) ∧
    σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274) ∧
    σ (.n (val% «verify_keccak» "segment_tree")) = VsC.ptrAtV (c + D.τ + 380) ∧
    ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ (vkHeadT ++ vkFirstT) next kret := by
  have hσ : ∀ v, σ v = σ (.n v.idx) := by subst hσd; exact (val_good h).1
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w c curE) σ s := by
    subst hσd; exact (val_good h).2.1
  have hpar : ∀ i < 12, σ (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0 := by
    subst hσd; exact (val_good h).2.2
  have hτ1 := h.1
  have hτ2 := h.2.1
  have houts : D.outs.length = 25 := h.2.2.2.1
  obtain ⟨f0, f1, f2, f3, f4, hf⟩ := five_of_length' h.2.2.2.2.1
  have p0 : σ (.n 0) = f0 := by rw [hpar 0 (by norm_num), args, hf]; rfl
  have p1 : σ (.n 1) = f1 := by rw [hpar 1 (by norm_num), args, hf]; rfl
  have p2 : σ (.n 2) = f2 := by rw [hpar 2 (by norm_num), args, hf]; rfl
  have p3 : σ (.n 3) = f3 := by rw [hpar 3 (by norm_num), args, hf]; rfl
  have p4 : σ (.n 4) = f4 := by rw [hpar 4 (by norm_num), args, hf]; rfl
  have p5 : σ (.n (val% «verify_keccak» "cursor@1")) = VsC.ptrAtV curE := by
    rw [hpar _ (by norm_num), args, hf]; rfl
  have p6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ := by rw [hpar _ (by norm_num), args, hf]; rfl
  have p7 : σ (.n (val% «verify_keccak» "chi")) = VsC.ptrAtV chiE := by rw [hpar _ (by norm_num), args, hf]; rfl
  have p8 : σ (.n (val% «verify_keccak» "output_lanes")) = VsC.ptrAtV olE := by
    rw [hpar _ (by norm_num), args, hf]; rfl
  have p9 : σ (.n (val% «verify_keccak» "z_vals")) = VsC.ptrAtV zvE := by rw [hpar _ (by norm_num), args, hf]; rfl
  have p10 : σ (.n (val% «verify_keccak» "slices")) = VsC.ptrAtV slE := by rw [hpar _ (by norm_num), args, hf]; rfl
  -- the buffers' bases
  have ha : ∀ x ∈ vkAllocs, σ x.1 = D.w c curE x.1.idx := by subst hσd; exact val_alloc h
  have a58 : σ (.n (val% «verify_keccak» "point")) = VsC.ptrAtV c := ha (.n (val% «verify_keccak» "point"), .inr (.n (val% «verify_keccak» "point~1"))) (by simp [vkAllocs])
  have a90 : σ (.n (val% «verify_keccak» "r_lane")) = VsC.ptrAtV (c + (D.τ - 3)) := ha (.n (val% «verify_keccak» "r_lane"), .inl 5) (by simp [vkAllocs])
  have a201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201) := ha (.n (val% «verify_keccak» "claims"), .inl 286) (by simp [vkAllocs])
  have a203 : σ (.n (val% «verify_keccak» "mu_tree")) = VsC.ptrAtV (c + D.τ + 288) := ha (.n (val% «verify_keccak» "mu_tree"), .inl 30) (by simp [vkAllocs])
  have a274 : σ (.n (val% «verify_keccak» "lane_tree")) = VsC.ptrAtV (c + D.o274) := ha (.n (val% «verify_keccak» "lane_tree"), .inl 62) (by simp [vkAllocs])
  have a382 : σ (.n (val% «verify_keccak» "segment_tree")) = VsC.ptrAtV (c + D.τ + 380) :=
    ha (.n (val% «verify_keccak» "segment_tree"), .inl 2) (by simp [vkAllocs])
  -- the memory
  obtain ⟨m58, m90, mcw, mmu, -, m203, m274, m382, -⟩ := own_mem hm.own
  obtain ⟨mcom, -⟩ := xs_reads h hm.cur
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
    vkHead_complete (S := vkSt) (w := D.w c curE) hσ (fun s hs hp ↦ hG s (mH s hs) hp)
      (fun d off ↦ not_mem_of_noStoreVia vk_ker2.1 (p := .n (val% «verify_keccak» "chi")) (by simp) d off)
      (fun d off ↦ not_mem_of_noStoreVia vk_ker2.1 (p := .n (val% «verify_keccak» "cursor@1")) (by simp) d off)
      hτ1 hτ2 p6 hbits
      (chis := D.chis) (by rw [p7]; exact hm.chi) (by have := h.2.2.1; omega) (committed := D.committed)
      (by rw [p5]; exact mcom)
  rw [p0, p1, p2, p3, p4, ← hf] at q1
  have hsq1 : D.sq1 = ([σ (.n (val% «verify_keccak» "nxt[0]@1"))], ⟨(cap5 82).map σ, []⟩) := by
    rw [sq1, keccakSegmentBits_eq]; exact q1
  have hseg : D.seg = [σ (.n (val% «verify_keccak» "nxt[0]@1"))] := by rw [seg, hsq1]
  have hsq2 : D.sq2 = ((List.range 5).map (fun i ↦ σ (.n (88 + 13 * i))), ⟨(cap5 148).map σ, []⟩) := by
    rw [sq2, hsq1]; exact q5
  have hrl : D.rl = (List.range 5).map (fun i ↦ σ (.n (88 + 13 * i))) := by rw [rl, hsq2]
  have hcap0 : (cap5 148).map σ = (D.layer 0).cap := by
    simp [layer, chain_zero, S0, hsq2, Fs.absorb, rateScalars]
  have e89 : σ (.n (val% «verify_keccak» "nxt[0]@1")) = D.seg.getD 0 0 := by rw [hseg]; rfl
  have e64' : σ (.n (val% «verify_keccak» "segment")) = VsC.ptrAtV c * gen ^ (D.τ - 4) := by rw [e64, a58, h17]
  have l64 : LoadHolds rd (σ (.n (val% «verify_keccak» "segment"))) 0 (σ (.n (val% «verify_keccak» "nxt[0]@1"))) := by
    rw [e64', loadHolds_mul_gen_pow, add_zero, e89, ← c0_point_seg h]
    exact readsAt_getD m58 (by rw [c0_point_length h]; omega)
  have l90 : ∀ i < 5, LoadHolds rd (σ (.n (val% «verify_keccak» "r_lane"))) i (σ (.n (88 + 13 * i))) := by
    intro i hi
    have := readsAt_getD m90 (k := i) (by rw [rl_length]; exact hi)
    rw [a90]
    rwa [hrl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
      at this
  have l9 : ∀ i < 4, LoadHolds rd (σ (.n (val% «verify_keccak» "z_vals"))) i
      (σ (.n ((val% «verify_keccak» "s14.u0.s0#0") + i))) := by
    intro i hi
    rw [p9, e52 i hi, ← op_getD h (by omega)]
    exact readsAt_getD hm.zv (by rw [op_length h]; omega)
  -- the first record
  have mF : ∀ s ∈ vkFirstT, GoodS rd vkSt (D.w c curE) σ s := fun s hs ↦ by
    subst hσd
    exact val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hs))))
  have hzv : ∀ i < 4, LoadHolds rd (σ (.n (val% «verify_keccak» "z_vals"))) i (D.chis.getD i 0) := fun i hi ↦ by
    rw [← e52 i hi]; exact l9 i hi
  have hrlL : ∀ i < 5, LoadHolds rd (σ (.n (val% «verify_keccak» "r_lane"))) i (D.rl.getD i 0) := fun i hi ↦ by
    rw [hrl, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
    exact l90 i hi
  have hT203 : ∀ t, 1 ≤ t → t ≤ 4 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n (val% «verify_keccak» "mu_tree")))
      (2 ^ t - 2 + i) ((eqKernel ((D.chis.take 4).take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 4 ≤ (D.chis.take 4).length := by simp; have := h.2.2.1; omega
    rw [a203, ← eqLevels_getD hl t h1 h2 i hi]
    refine readsAt_getD m203 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hT274 : ∀ t, 1 ≤ t → t ≤ 5 → ∀ i < 2 ^ t, LoadHolds rd (σ (.n (val% «verify_keccak» "lane_tree")))
      (2 ^ t - 2 + i) ((eqKernel (D.rl.take t)).getD i 0) := by
    intro t h1 h2 i hi
    have hl : 5 ≤ D.rl.length := by rw [rl_length]
    rw [a274, ← eqLevels_getD hl t h1 h2 i hi]
    refine readsAt_getD m274 ?_
    rw [eqLevels_length hl]
    have : 2 ^ t ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) h2
    omega
  have hT382 : ∀ i < 2, LoadHolds rd (σ (.n (val% «verify_keccak» "segment_tree"))) i
      ((eqKernel [σ (.n (val% «verify_keccak» "nxt[0]@1"))]).getD i 0) := by
    intro i hi
    rw [a382, ← hseg]
    exact readsAt_getD m382 (by rw [eqKernel_length, seg_length]; simpa using hi)
  obtain ⟨e202, e381, e258, e487, HF⟩ := vkFirst_complete (C := fun _ _ _ ↦ True) hσ mF
    (by have := h.2.2.1; omega) hzv (rl_length) hrlL l64
    houts (by rw [p8]; exact hm.ol) hT203 hT274 hT382
  -- the first record's stores
  have hcl : ∀ j < 4, LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) j ((D.cw0 c).getD j 0) :=
    fun j hj ↦ by rw [a201]; exact readsAt_getD mcw (by simp [cw0]; omega)
  have s1 : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 1 (σ (.n (val% «verify_keccak» "s32#0"))) := by
    rw [e202]; exact hcl 1 (by norm_num)
  have s2 : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 2 (σ (.n (val% «verify_keccak» "point"))) := by
    rw [a58]; exact hcl 2 (by norm_num)
  have s6 : ∀ i < 16, LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) (6 + i)
      (σ (.n ((val% «verify_keccak» "s36.u0.s0#0") + i))) := by
    intro i hi
    have := readsAt_getD mmu (k := i) (by rw [c0_mu h]; exact hi)
    rw [← ptr_mul_gen, loadHolds_mul_gen_pow, c0_mu_eq h] at this
    rw [e258 i hi, a201]
    exact this
  have s3 : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 3 (σ (.n (val% «verify_keccak» "s40#1"))) := by
    rw [e381, a274, ptr_mul_gen]; exact hcl 3 (by norm_num)
  have s0 : LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) 0 (σ (.n (val% «verify_keccak» "s45#2"))) := by
    have := hcl 0 (by norm_num)
    suffices hv : (D.cw0 c).getD 0 0 = σ (.n (val% «verify_keccak» "s45#2")) by rwa [hv] at this
    rw [e487, e191]
    simp only [cw0, c0, vkFirst, keccakSegments_eq, show 2 - 1 = 1 from rfl]
    rw [hseg, dot_eq _ _ (by simp [eqKernel_length, rl_length, houts])]
    simp only [List.length_take, eqKernel_length, rl_length, show min 25 (2 ^ 5) = 25 from rfl]
    refine congrArg (D.committed + (eqKernel [σ (.n (val% «verify_keccak» "nxt[0]@1"))]).getD 1 0 * ·)
      (Finset.sum_congr rfl fun k hk ↦ ?_)
    simp [List.getD_eq_getElem?_getD, Finset.mem_range.1 hk]
  refine ⟨fun i hi ↦ ?_, p5, p6, p7, p8, p9, p10, h17, h33, h47, a58,
    by rw [e60, h17], e61, by rw [e63, p7], e64', e89, a90, hcap0, e191, by rw [cells]; exact fcells,
    a201, a203, a274, a382, fun {next kret} hn ↦ ?_⟩
  · interval_cases i <;> simp [p0, p1, p2, p3, p4, hf]
  · rw [holdsList_append]
    exact HH l9 l64 l90 (HF s1 s2 s6 s3 s0 hn)

end VkData

end
end LeanVM.Guest.B1.VerifySub
