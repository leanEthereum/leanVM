/-
  LeanVM.Guest.B1.VsC.VkPG

  `verify_keccak` placed: its loads land in the caller's words, its buffers or the layers'
  (the archive's `VkCQ`, `VkCR` on Hotwire's layers).
-/

module

public import LeanVM.Guest.B1.VsC.VkPF
public import LeanVM.Guest.Memory.Uniform
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# The loads, on the layout

`step_ptrs`, `fin_ptrs`: the pointers the steps and the inputs' check load through, read from the
claim records (the first claim's point is `point`, a later one's buffers are its layer's).
`vk_loads`: every load of the body is through one of `vkGroups`, at an offset in its range (a
kernel check). `loads_in`: each lands in the caller's words (`LinR`), the buffers or a layer's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

/-- Step `s`'s pointers: its claim's point's segment coordinate, its flips. -/
def stepGroups (s : ℕ) : List (V × ℕ × ℕ) :=
  [(.n (stepB s + 1), 0, 1)] ++
    if s = 0 then [] else (List.range (iotaUsed s).length).map fun j ↦ (.n (stepB s + 6 + 2 * j), 0, 7)

/-- The pointers the body loads through, with their offsets' ranges. -/
def vkGroups : List (V × ℕ × ℕ) :=
  [(.n (val% «verify_keccak» "cursor@1"), 0, 1), (.n (val% «verify_keccak» "chi"), 0, 4),
    (.n (val% «verify_keccak» "output_lanes"), 0, 25), (.n (val% «verify_keccak» "z_vals"), 0, 4),
    (.n (val% «verify_keccak» "z_vals"), 39, 43), (.n (val% «verify_keccak» "slices"), 0, 64),
    (.n (val% «verify_keccak» "segment"), 0, 1), (.n (val% «verify_keccak» "r_lane"), 0, 5),
    (.n (val% «verify_keccak» "claims"), 0, 286), (.n (val% «verify_keccak» "mu_tree"), 0, 30),
    (.n (val% «verify_keccak» "lane_tree"), 0, 62), (.n (val% «verify_keccak» "segment_tree"), 0, 2),
    (.n (val% «verify_keccak» "out_slot"), 0, 6), (.n (val% «verify_keccak» "cursor@14"), 0, 1),
    (.n (val% «verify_keccak» "s52#0"), 0, 1), (.n (val% «verify_keccak» "low_tree"), 0, 30),
    (.n (val% «verify_keccak» "cursor@16"), 0, 64), (.n (val% «verify_keccak» "in_slot"), 0, 6),
    (.n (val% «verify_keccak» "s72#0"), 0, 1), (.n (val% «verify_keccak» "last_local"), 0, 6),
    (.n (val% «verify_keccak» "last_lanes"), 0, 25)] ++
    (List.range 12).flatMap stepGroups

/-- A load through one of `vkGroups`. -/
def inGroups (q : V × ℕ) : Bool :=
  vkGroups.any fun g ↦ g.1 == q.1 && decide (g.2.1 ≤ q.2) && decide (q.2 < g.2.2)

theorem vk_loads : (vkPre.filterMap LeanVM.Guest.B1.Stmt.loadS).all inGroups = true := by decide +kernel

/-- A load at `ptr a` and `off`, inside a run `[b, b + n)` of `T`. -/
theorem reg_at {T : ℕ → Prop} {b n : ℕ} (hT : ∀ i, b ≤ i → i < b + n → T i) {p : E} {a off : ℕ}
    (hp : p = VsC.ptrAtV a) (h1 : b ≤ a + off) (h2 : a + off < b + n) :
    ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
  ⟨a + off, by rw [hp]; exact ptr_addr a off, hT _ h1 h2⟩

namespace VkData

variable {D : VkData} {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}

/-- The caller's words. -/
def LinR (D : VkData) (curE chiE olE zvE slE : ℕ) (i : ℕ) : Prop :=
  (curE ≤ i ∧ i < curE + D.xs.length) ∨ (chiE ≤ i ∧ i < chiE + D.chis.length) ∨
    (olE ≤ i ∧ i < olE + D.outs.length) ∨ (zvE ≤ i ∧ i < zvE + D.op.length) ∨
    (zvE + qkeccakVarsCap ≤ i ∧ i < zvE + qkeccakVarsCap + D.point.length) ∨
    (slE ≤ i ∧ i < slE + D.slices.length)

/-- Claim `s`'s record's words: the first's, or layer `s - 1`'s next claim's. -/
def recW (D : VkData) (c : ℕ) (ls : ℕ → ℕ) : ℕ → List E
  | 0 => D.cw0 c
  | k + 1 => D.outWs ls k

/-- Word `k` of claim `s`'s record, through the claim records' pointer. -/
theorem rec_word (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201)) {s : ℕ} (hs : s < 12) {k : ℕ}
    (hk : k < (D.recW c ls s).length) :
    LoadHolds rd (σ (.n (val% «verify_keccak» "claims"))) (22 * s + k) ((D.recW c ls s).getD k 0) := by
  obtain ⟨-, -, mcw, -, mo, -⟩ := own_mem hm.own
  have hcw : ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * s)) (D.recW c ls s) := by
    rcases s with _ | j
    · simpa [recW] using mcw
    · exact mo j (by omega)
  rw [← ptr_mul_gen, ← h201] at hcw
  exact (loadHolds_mul_gen_pow rd _ _ _ _).1 (readsAt_getD hcw hk)

/-- Where claim `s`'s point is. -/
def ptB (c : ℕ) (ls : ℕ → ℕ) : ℕ → ℕ
  | 0 => c
  | k + 1 => ls k

/-- **Step `s`'s pointers.** -/
theorem step_ptrs (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) {s : ℕ} (hs : s < 12)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201)) :
    σ (.n (stepB s + 1)) = VsC.ptrAtV (ptB c ls s) * gen ^ (D.τ - 4) ∧
    (∀ k, s = k + 1 → ∀ j < (iotaUsed s).length,
      σ (.n (stepB s + 6 + 2 * j)) = VsC.ptrAtV (ls k + (D.τ - 3) + 36)) := by
  have hg : ∀ st ∈ stepCore s (stepB s), GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    refine val_good' h (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_steps s hs st ?_)))))
    rw [stepT_split]; exact List.mem_append_left _ hst
  have gA : ∀ a, Stmt.atom a ∈ stepCore s (stepB s) → Good rd vkSt (D.w c curE) σ a :=
    fun a h ↦ hg _ h
  have mA : ∀ a ∈ [Atom.load (.n (stepB s)) (.n (val% «verify_keccak» "claims")) (22 * s + 2),
      .mul (.n (stepB s + 1)) (.n (stepB s)) (.n (val% «verify_keccak» "pack_g"))],
      Stmt.atom a ∈ stepCore s (stepB s) := by
    intro a ha
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp
  obtain ⟨k1, -, -, k5, -⟩ := step_ker s hs
  obtain ⟨-, hbB, -⟩ := step_bounds s hs
  have h2 : (D.recW c ls s).getD 2 0 = VsC.ptrAtV (ptB c ls s) := by
    rcases s with _ | j
    · rfl
    · simp [recW, ptB, outWs, VsC.klOutW]
  have e0 : σ (.n (stepB s)) = VsC.ptrAtV (ptB c ls s) := by
    have := rec_word hm h201 hs (k := 2) (by
      rcases s with _ | j
      · simp [recW, cw0]
      · simp [recW, outWs_length])
    rw [h2] at this
    exact load_val (gA _ (mA _ (by simp))) (not_mem_of_noneIn k1 _ (by simp)) this
  have m1 := mulG (by omega) (by omega) (gA _ (mA (.mul (.n (stepB s + 1)) (.n (stepB s))
    (.n (val% «verify_keccak» "pack_g"))) (by simp)))
  refine ⟨by rw [m1, e0, h17], fun k hk j hj ↦ ?_⟩
  subst hk
  have hs0 : k + 1 ≠ 0 := by omega
  have m0 : Stmt.atom (.load (.n (stepB (k + 1) + 6 + 2 * j)) (.n (val% «verify_keccak» "claims"))
      (22 * (k + 1) + 5)) ∈ flipsT (k + 1) (stepB (k + 1) + 6) := by
    simp only [flipsT, List.mem_flatten, List.mem_map, List.mem_range]
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [flipT, flipSz]⟩
  have l5 := rec_word hm h201 hs (k := 5) (by simp [recW, outWs_length])
  have h5 : (D.recW c ls (k + 1)).getD 5 0 = VsC.ptrAtV (ls k + (D.τ - 3) + 36) := by
    simp [recW, outWs, VsC.klOutW]
  rw [h5] at l5
  exact load_val (w := D.w c curE) (hg _ (mem_stepCoreF m0))
    (not_mem_of_noneIn k5 _ (load_mem_resid m0)) l5

/-- **The inputs' check's pointers.** -/
theorem fin_ptrs (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE)
    (h17 : σ (.n (val% «verify_keccak» "pack_g")) = gen ^ (D.τ - 4))
    (h201 : σ (.n (val% «verify_keccak» "claims")) = VsC.ptrAtV (c + D.o201)) :
    σ (.n (val% «verify_keccak» "s72#0")) = VsC.ptrAtV (ls 11) * gen ^ (D.τ - 4) ∧
      σ (.n (val% «verify_keccak» "last_local")) = VsC.ptrAtV (ls 11 + (D.τ - 3)) ∧
      σ (.n (val% «verify_keccak» "last_lanes")) = VsC.ptrAtV (ls 11 + (D.τ - 3) + 11) := by
  have hg : ∀ st ∈ vkFinT, GoodS rd vkSt (D.w c curE) σ st := fun st hst ↦ by
    subst hσd
    exact val_good' h (List.mem_append_right _ hst)
  have gA : ∀ a, Stmt.atom a ∈ vkFinT → Good rd vkSt (D.w c curE) σ a := fun a h ↦ hg _ h
  have k1 := vkFin_ker.1
  have hrec := last_rec hm
  rw [outWs_last h, ← h201] at hrec
  have e4977 : σ (.n (val% «verify_keccak» "last_point")) = VsC.ptrAtV (ls 11) :=
    load_val (gA (.load (.n (val% «verify_keccak» "last_point")) (.n (val% «verify_keccak» "claims")) 266)
      (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 2 (by norm_num))
  have m4978 := mulG (by norm_num) (by norm_num)
    (gA (.mul (.n (val% «verify_keccak» "s72#0")) (.n (val% «verify_keccak» "last_point"))
      (.n (val% «verify_keccak» "pack_g"))) (by simp [vkFinT]))
  refine ⟨by rw [m4978, e4977, h17], ?_, ?_⟩
  · exact load_val (gA (.load (.n (val% «verify_keccak» "last_local")) (.n (val% «verify_keccak» "claims")) 268)
      (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 4 (by norm_num))
  · exact load_val (gA (.load (.n (val% «verify_keccak» "last_lanes")) (.n (val% «verify_keccak» "claims")) 267)
      (by simp [vkFinT])) (not_mem_of_noneIn k1 _ (by simp)) (by simpa using hrec 3 (by norm_num))

set_option maxRecDepth 20000 in
/-- **Every load lands in the layout.** -/
theorem loads_in (h : D.Ok) (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) {σ : Val}
    (hσd : σ = D.val rd c curE chiE olE zvE slE tbE) {T : ℕ → Prop}
    (hLin : ∀ i, D.LinR curE chiE olE zvE slE i → T i)
    (hOwn : ∀ i, c ≤ i → i < c + D.τ + 412 → T i)
    (hLay : ∀ s < 12, ∀ i, ls s ≤ i → i < ls s + (D.τ - 3) + 43 → T i) :
    ∀ q ∈ vkPre.filterMap LeanVM.Guest.B1.Stmt.loadS,
      ∃ i, (σ q.1).limb 0 * Parameters.addressOfIndex q.2 = Parameters.addressOfIndex i ∧ T i := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  have hchis := h.2.2.1
  have houts : D.outs.length = 25 := h.2.2.2.1
  have hslL : D.slices.length = 64 := h.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, p5, p6, p7, p8, p9, p10, h17, -, -, a58, -, -, -, e64, -, a90, -, -, -, a201, a203,
    a274, a382, -⟩ := head_first h hm hσd
  obtain ⟨-, -, e3691, -, -, eO, -⟩ := out_on h hm hσd p6 p9 h17 a58 a274
  have e3699 : σ (.n (val% «verify_keccak» "cursor@14")) = VsC.ptrAtV (curE + D.lcur 12 + 12) := by
    rw [show (val% «verify_keccak» "cursor@14") = (val% «verify_keccak» "fs0@14") + 5 from rfl,
      eO 5 (by norm_num), oRets_cur h]
  obtain ⟨-, -, -, -, -, e4107, -, -, e4110, -⟩ := in_on h hm hσd p6 p9 p10 a201 e3699
  have e4115 : σ (.n (val% «verify_keccak» "cursor@16")) = VsC.ptrAtV (curE + D.lcur 12 + 33) := by
    rw [show (val% «verify_keccak» "cursor@16") = (val% «verify_keccak» "fs0@16") + 5 from rfl,
      e4110 5 (by norm_num), sRets, List.getD_append_right _ _ _ _ (by rw [(S_ok h).2]), (S_ok h).2]
    simp only [Nat.sub_self, List.getD_cons_zero, cL, ptr_mul_gen, ptr_mul_gen1]
  obtain ⟨e4978, e5212, e6363⟩ := fin_ptrs h hm hσd h17 a201
  have e3711 : σ (.n (val% «verify_keccak» "s52#0")) = VsC.ptrAtV c * gen ^ (D.τ - 4) := by
    have g : Good rd vkSt (D.w c curE) σ (.mul (.n (val% «verify_keccak» "s52#0"))
        (.n (val% «verify_keccak» "point")) (.n (val% «verify_keccak» "pack_g"))) := by
      subst hσd
      exact val_good' h (s := .atom (.mul (.n (val% «verify_keccak» "s52#0")) (.n (val% «verify_keccak» "point"))
        (.n (val% «verify_keccak» "pack_g"))))
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp [vkOutT]))))
    rw [mulG (by norm_num) (by norm_num) g, a58, h17]
  have a3987 : σ (.n (val% «verify_keccak» "low_tree")) = VsC.ptrAtV (c + D.τ + 382) := by
    subst hσd; exact val_alloc h (.n (val% «verify_keccak» "low_tree"), .inl 30) (by simp [vkAllocs])
  have mLin : ∀ {b n : ℕ}, (∀ i, b ≤ i → i < b + n → D.LinR curE chiE olE zvE slE i) →
      ∀ {p : E} {a off : ℕ}, p = VsC.ptrAtV a → b ≤ a + off → a + off < b + n →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun hb _ _ _ hp h1 h2 ↦ reg_at (fun i h1 h2 ↦ hLin i (hb i h1 h2)) hp h1 h2
  have mOwn : ∀ {p : E} {a off : ℕ}, p = VsC.ptrAtV a → c ≤ a + off → a + off < c + D.τ + 412 →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun hp h1 h2 ↦ reg_at (n := D.τ + 412) (fun i h1 h2 ↦ hOwn i h1 (by omega)) hp h1 (by omega)
  have mLay : ∀ s < 12, ∀ {p : E} {a off : ℕ}, p = VsC.ptrAtV a → ls s ≤ a + off →
      a + off < ls s + (D.τ - 3) + 43 →
      ∃ i, p.limb 0 * Parameters.addressOfIndex off = Parameters.addressOfIndex i ∧ T i :=
    fun s hs _ _ _ hp h1 h2 ↦ reg_at (n := (D.τ - 3) + 43) (fun i h1 h2 ↦ hLay s hs i h1 (by omega))
      hp h1 (by omega)
  intro q hq
  have hg := List.all_eq_true.mp vk_loads q hq
  simp only [inGroups, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
  obtain ⟨⟨gp, lo, hi⟩, hgm, ⟨hp, hlo⟩, hhi⟩ := hg
  obtain ⟨p, off⟩ := q
  simp only at hp hlo hhi ⊢
  subst hp
  simp only [vkGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range, Prod.mk.injEq] at hgm
  have hpL := point_length h
  have hoL := op_length h
  have hxL := xs_len h
  have hc0 := c0_point_length h
  have hq39 : qkeccakVarsCap = 39 := rfl
  rcases hgm with (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) | ⟨s, hs, hsg⟩
  · exact mLin (b := curE) (n := D.xs.length) (fun i h1 h2 ↦ Or.inl ⟨h1, h2⟩) p5 (by omega) (by omega)
  · exact mLin (b := chiE) (n := D.chis.length) (fun i h1 h2 ↦ Or.inr (Or.inl ⟨h1, h2⟩)) p7 (by omega)
      (by omega)
  · exact mLin (b := olE) (n := D.outs.length) (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))) p8
      (by omega) (by omega)
  · exact mLin (b := zvE) (n := D.op.length) (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      p9 (by omega) (by omega)
  · exact mLin (b := zvE + qkeccakVarsCap) (n := D.point.length)
      (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))) p9 (by omega) (by omega)
  · exact mLin (b := slE) (n := D.slices.length)
      (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))) p10 (by omega) (by omega)
  · exact mOwn (by rw [e64, ptr_mul_gen]) (by omega) (by omega)
  · exact mOwn a90 (by omega) (by omega)
  · exact mOwn a201 (by simp [o201]; omega) (by simp [o201]; omega)
  · exact mOwn a203 (by omega) (by omega)
  · exact mOwn a274 (by simp [o274]; omega) (by simp [o274]; omega)
  · exact mOwn a382 (by omega) (by omega)
  · exact mLin (b := zvE) (n := D.op.length) (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      (by rw [e3691, ptr_mul_gen]) (by omega) (by omega)
  · exact mLin (b := curE) (n := D.xs.length) (fun i h1 h2 ↦ Or.inl ⟨h1, h2⟩) e3699 (by omega)
      (by simp [lcur] at hxL ⊢; omega)
  · exact mOwn (by rw [e3711, ptr_mul_gen]) (by omega) (by omega)
  · exact mOwn a3987 (by omega) (by omega)
  · exact mLin (b := curE) (n := D.xs.length) (fun i h1 h2 ↦ Or.inl ⟨h1, h2⟩) e4115 (by omega)
      (by omega)
  · exact mLin (b := zvE + qkeccakVarsCap) (n := D.point.length)
      (fun i h1 h2 ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))
      (by rw [e4107, ptr_mul_gen, ptr_mul_gen]) (by omega) (by omega)
  · exact mLay 11 (by norm_num) (by rw [e4978, ptr_mul_gen]) (by omega) (by omega)
  · exact mLay 11 (by norm_num) e5212 (by omega) (by omega)
  · exact mLay 11 (by norm_num) e6363 (by omega) (by omega)
  · -- a step's
    obtain ⟨hpp, hfl⟩ := step_ptrs h hm hσd hs h17 a201
    simp only [stepGroups, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hsg
    rcases hsg with ⟨rfl, rfl, rfl⟩ | hsg
    · rcases s with _ | k
      · exact mOwn (a := c + (D.τ - 4)) (by rw [hpp, ptr_mul_gen]; rfl) (by omega) (by omega)
      · exact mLay k (by omega) (a := ls k + (D.τ - 4)) (by rw [hpp, ptr_mul_gen]; rfl)
          (by omega) (by omega)
    · rcases s with _ | k
      · simp at hsg
      · simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, List.mem_map, List.mem_range,
          Prod.mk.injEq] at hsg
        obtain ⟨j, hj, rfl, rfl, rfl⟩ := hsg
        exact mLay k (by omega) (a := ls k + (D.τ - 3) + 36) (hfl k rfl j hj) (by omega) (by omega)

end VkData

end
end LeanVM.Guest.B1.VerifySub
