/-
  LeanVM.Guest.B1.VsC.VkPB

  `verify_keccak` placed: its body flat, its layout, own words, oracle and valuation (the archive's
  `VkCJ`, `VkCG`, `VkCK`, `VkCL` on Hotwire's template and layers).
-/

module

public import LeanVM.Guest.B1.VsC.VkPA
public import LeanVM.Guest.B1.VsC.VkCCK
public import LeanVM.Guest.Memory.Straight
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# `verify_keccak`, its layout

* `vkT = vkPre ++ [.ret vkVs]`; `vkPre_kernel`: straight, no frame address, its seven buffers
  (`vkAllocs`), its calls (`vkCalls`).
* From the cursor `c`: the point (`τ - 3` words), the lane coordinates (`5`), the claim records
  (`286`, at `c + o201`), the instance tree (`30`), the lane tree (`62`, at `c + o274`), the
  segment tree (`2`), the low tree (`30`). `D.Wo c ls`: the words it writes there, the records
  of the later claims pointing into the layers' buffers at `ls s` (`klOutW`).
* `D.w c curE`: the oracle (the bits of `y`, the bases, the callees' returns); `D.val`: the honest
  valuation. `D.Mem`: what a memory holds (the own words, the caller's words, each layer's next
  claim); `D.recs`: each claim's record (`ClaimRec`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr LeanVM.Guest.B1.VerifySub.KL

@[expose] public section

/-! ## The body, flat -/

/-- The inputs' check and the return but the return. -/
def vkFinPre : List Stmt := vkFinT.dropLast

/-- The returned values. -/
def vkVs : List V := [.n (val% «verify_keccak» "s82#0"), .n (val% «verify_keccak» "s82#0[1]"),
  .n (val% «verify_keccak» "s82#0[2]"), .n (val% «verify_keccak» "s82#0[3]"),
  .n (val% «verify_keccak» "s82#0[4]"), .n (val% «verify_keccak» "s82#0[5]"),
  .n (val% «verify_keccak» "s82#0[6]")]

/-- The body but its return. -/
def vkPre : List Stmt := vkHeadT ++ vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinPre

theorem vkFinT_pre : vkFinT = vkFinPre ++ [.ret vkVs] := stmtsEqb_sound (by decide +kernel)

theorem vkT_pre : vkT = vkPre ++ [.ret vkVs] := by
  rw [vkT, vkPre, vkFinT_pre]; simp only [List.append_assoc]

/-- The buffers. -/
def vkAllocs : List (V × (ℕ ⊕ V)) :=
  [(.n (val% «verify_keccak» "point"), .inr (.n (val% «verify_keccak» "point~1"))),
    (.n (val% «verify_keccak» "r_lane"), .inl 5), (.n (val% «verify_keccak» "claims"), .inl 286),
    (.n (val% «verify_keccak» "mu_tree"), .inl 30), (.n (val% «verify_keccak» "lane_tree"), .inl 62),
    (.n (val% «verify_keccak» "segment_tree"), .inl 2), (.n (val% «verify_keccak» "low_tree"), .inl 30)]

/-- Where step `s`'s call returns. -/
def stepE (s : ℕ) : ℕ := stepT0 s (stepB s) + stepTailSz s

/-- Step `s`'s call's arguments and returns. -/
def stepCall (s : ℕ) : Option V × String × List V × List V :=
  let T := stepT0 s (stepB s)
  if s = 0 then
    (none, layerName 1, (stepCap s).map .n ++ [.n (val% «verify_keccak» "value_rate[0]"),
      .n (val% «verify_keccak» "value_rate[1]"), .n (T + 1), .n (T + 3), .n 29, .n 48,
      .n (val% «verify_keccak» "claims"), .n (T + 5), .n (T - 1), .n (val% «verify_keccak» "tabs")],
      (List.range 6).map fun j ↦ .n (T + 6 + j))
  else
    (none, layerName 0, (stepCap s).map .n ++ [.n T, .n (T + 1), .n (stepCur s), .n (T + 3), .n 29,
      .n 48, .n (T + 5), .n (T + 7), .n (T - 1), .n (val% «verify_keccak» "tabs")],
      (List.range 6).map fun j ↦ .n (T + 8 + j))

/-- The committed outputs' rounds. -/
def oCall : Option V × String × List V × List V :=
  (none, "keccak_plain_rounds__L6_L0", [.n (val% «verify_keccak» "fs0@13"),
    .n (val% «verify_keccak» "fs1@13"), .n (val% «verify_keccak» "fs2@13"),
    .n (val% «verify_keccak» "fs3@13"), .n (val% «verify_keccak» "fs4@13"),
    .n (val% «verify_keccak» "fs0@14~7"), .n (val% «verify_keccak» "fs0@14~8"),
    .n (val% «verify_keccak» "cursor@13"), .n (val% «verify_keccak» "x@1"),
    .n (val% «verify_keccak» "out_slot"), .n (val% «verify_keccak» "tabs")],
    (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@14") + j))

/-- The inputs' rounds. -/
def iCall : Option V × String × List V × List V :=
  (none, "keccak_plain_rounds__L4_L1", [.n (val% «verify_keccak» "fs0@14"),
    .n (val% «verify_keccak» "fs1@14"), .n (val% «verify_keccak» "fs2@14"),
    .n (val% «verify_keccak» "fs3@14"), .n (val% «verify_keccak» "fs4@14"),
    .n (val% «verify_keccak» "word_rate[0]"), .n (val% «verify_keccak» "word_rate[1]"),
    .n (val% «verify_keccak» "fs0@15~8"), .n (val% «verify_keccak» "fs0@15~9"),
    .n (val% «verify_keccak» "fs0@15~11"), .n (val% «verify_keccak» "tabs")],
    (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@15") + j))

/-- The inputs' opening's rounds. -/
def sCall : Option V × String × List V × List V :=
  (none, "keccak_plain_rounds__L6_L0", [.n (val% «verify_keccak» "fs0@15"),
    .n (val% «verify_keccak» "fs1@15"), .n (val% «verify_keccak» "fs2@15"),
    .n (val% «verify_keccak» "fs3@15"), .n (val% «verify_keccak» "fs4@15"),
    .n (val% «verify_keccak» "fs0@16~7"), .n (val% «verify_keccak» "fs0@16~8"),
    .n (val% «verify_keccak» "cursor@15"), .n (val% «verify_keccak» "low_value"),
    .n (val% «verify_keccak» "in_slot"), .n (val% «verify_keccak» "tabs")],
    (List.range 7).map fun j ↦ .n ((val% «verify_keccak» "fs0@16") + j))

/-- The copy loops. -/
def l0Call : Option V × String × List V × List V :=
  (some (.n (val% «verify_keccak» "s17#1")), name% «verify_keccak_loop0»,
    [.n (val% «verify_keccak» "s17#2"), .n (val% «verify_keccak» "pack_g"),
      .n (val% «verify_keccak» "point"), .n (val% «verify_keccak» "s17#4")], [])
def l1Call : Option V × String × List V × List V :=
  (some (.n (val% «verify_keccak» "s57#1")), name% «verify_keccak_loop1»,
    [.n (val% «verify_keccak» "s57#2"), .n (val% «verify_keccak» "pack_g"),
      .n (val% «verify_keccak» "s57#4"), .n (val% «verify_keccak» "point")], [])
def l2Call : Option V × String × List V × List V :=
  (some (.n (val% «verify_keccak» "s81#1")), name% «verify_keccak_loop2»,
    [.n (val% «verify_keccak» "s81#2"), .n (val% «verify_keccak» "pack_g"),
      .n (val% «verify_keccak» "s81#4"), .n (val% «verify_keccak» "last_point")], [])

/-- **The calls.** -/
def vkCalls : List (Option V × String × List V × List V) :=
  [l0Call] ++ (List.range 12).map stepCall ++ [oCall, l1Call, iCall, sCall, l2Call]

theorem vkPre_kernel :
    vkPre.all Stmt.straight = true ∧ vkPre.filterMap Stmt.addrS = [] ∧
    vkPre.filterMap Stmt.allocSz = vkAllocs ∧ vkPre.filterMap Stmt.callS = vkCalls := by
  decide +kernel

theorem vk_ker2 : noStoreVia [.n (val% «verify_keccak» "cursor@1"), .n (val% «verify_keccak» "chi")] vkSt = true ∧
    (vkFirstT ++ vkStepsT ++ vkOutT ++ vkInT ++ vkFinT).all (fun s ↦ !pinB s) = true := by
  decide +kernel

/-! ## The layout -/

namespace VkData

variable (D : VkData)

/-- The claim records' buffer, past the cursor. -/
def o201 : ℕ := D.τ + 2

/-- The lane coordinates' tree, past the cursor. -/
def o274 : ℕ := D.τ + 318

/-- The buffers' sizes. -/
def sizes : List ℕ := [D.τ - 3, 5, 286, 30, 62, 2, 30]

/-- Layer `s`'s next claim's record, pointing into its buffers at `ls s`. -/
def outWs (ls : ℕ → ℕ) (s : ℕ) : List E :=
  VsC.klOutW ((D.layer s).next (firstOf s)) (ls s) (D.τ - 3)

/-- The first claim's record's first four words (its words `4`, `5` are not written). -/
def cw0 (c : ℕ) : List E :=
  [D.c0.value, 1, VsC.ptrAtV c, VsC.ptrAtV (c + D.o274 + 30)]

/-- **The own words**: the buffers' contents the body writes. -/
noncomputable def Wo (c : ℕ) (ls : ℕ → ℕ) : Words :=
  [(c, D.c0.point), (c + (D.τ - 3), D.rl), (c + D.o201, D.cw0 c), (c + D.o201 + 6, D.c0.mu)] ++
    (List.range 12).map (fun s ↦ (c + D.o201 + 22 * (s + 1), D.outWs ls s)) ++
    [(c + D.τ + 288, eqLevels (D.chis.take 4) 4), (c + D.o274, eqLevels D.rl 5),
      (c + D.τ + 380, eqKernel D.seg), (c + D.τ + 382, eqLevels D.I.1 4)]

theorem bases_eq (c : ℕ) (h : 3 ≤ D.τ) :
    bases c D.sizes = [c, c + (D.τ - 3), c + D.o201, c + D.τ + 288, c + D.o274, c + D.τ + 380,
      c + D.τ + 382] := by
  simp only [sizes, o201, o274, bases]
  simp only [List.cons.injEq, and_true, true_and]
  repeat' apply And.intro
  all_goals omega

/-! ## The oracle -/

/-- **The oracle**: the bits of `y`, the buffers' bases, the callees' returns. -/
noncomputable def w (c curE : ℕ) (i : ℕ) : E :=
  if 21 ≤ i ∧ i < 26 then Value.bitE ((D.τ - 3).testBit (i - 21))
  else if i = val% «verify_keccak» "point" then VsC.ptrAtV c
  else if i = val% «verify_keccak» "r_lane" then VsC.ptrAtV (c + (D.τ - 3))
  else if i = val% «verify_keccak» "claims" then VsC.ptrAtV (c + D.o201)
  else if i = val% «verify_keccak» "mu_tree" then VsC.ptrAtV (c + D.τ + 288)
  else if i = val% «verify_keccak» "lane_tree" then VsC.ptrAtV (c + D.o274)
  else if i = val% «verify_keccak» "segment_tree" then VsC.ptrAtV (c + D.τ + 380)
  else if i = val% «verify_keccak» "low_tree" then VsC.ptrAtV (c + D.τ + 382)
  else if val% «verify_keccak» "fs0@14" ≤ i ∧ i < val% «verify_keccak» "fs0@14" + 7 then
    (D.oRets curE).getD (i - val% «verify_keccak» "fs0@14") 0
  else if val% «verify_keccak» "fs0@15" ≤ i ∧ i < val% «verify_keccak» "fs0@15" + 7 then
    (D.iRets curE).getD (i - val% «verify_keccak» "fs0@15") 0
  else if val% «verify_keccak» "fs0@16" ≤ i ∧ i < val% «verify_keccak» "fs0@16" + 7 then
    (D.sRets curE).getD (i - val% «verify_keccak» "fs0@16") 0
  else match (List.range 12).find? (fun s ↦ stepE s - 6 ≤ i && i < stepE s) with
    | some s => ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).getD (i - (stepE s - 6)) 0
    | none => 0

/-- `verify_keccak`'s arguments. -/
def args (curE chiE olE zvE slE tbE : ℕ) : List E :=
  D.f ++ [VsC.ptrAtV curE, gen ^ D.τ, VsC.ptrAtV chiE, VsC.ptrAtV olE, VsC.ptrAtV zvE,
    VsC.ptrAtV slE, VsC.ptrAtV tbE]

/-- **The honest valuation.** -/
noncomputable def val (rd : Reader) (c curE chiE olE zvE slE tbE : ℕ) : Val :=
  vkσ rd (D.w c curE) (D.args curE chiE olE zvE slE tbE)

/-- **What a memory holds**: the own words, the caller's words, and after each layer its next
claim (what its own words give, `KeccakLayerCompleteA`'s `Out`). -/
structure Mem (rd : Reader) (c curE chiE olE zvE slE tbE : ℕ) (ls : ℕ → ℕ) : Prop where
  own : HoldsWords rd (D.Wo c ls)
  tabs : WinTabs rd (VsC.ptrAtV tbE)
  chi : ReadsAt rd (VsC.ptrAtV chiE) D.chis
  ol : ReadsAt rd (VsC.ptrAtV olE) D.outs
  cur : ReadsAt rd (VsC.ptrAtV curE) D.xs
  zv : ReadsAt rd (VsC.ptrAtV zvE) D.op
  pt : ReadsAt rd (VsC.ptrAtV zvE * gen ^ qkeccakVarsCap) D.point
  sl : ReadsAt rd (VsC.ptrAtV slE) D.slices
  lay : ∀ s < 12, ClaimRec rd false (VsC.ptrAtV (c + D.o201 + 22 * (s + 1)))
    ((D.layer s).next (firstOf s)) (D.τ - 3)

variable {D}

theorem w_bits {c curE j : ℕ} (hj : j < 5) : D.w c curE (21 + j) = Value.bitE ((D.τ - 3).testBit j) := by
  simp only [w, Nat.le_add_right, true_and, show 21 + j < 26 by omega, ↓reduceIte,
    Nat.add_sub_cancel_left]

theorem w_o {c curE j : ℕ} (hj : j < 7) :
    D.w c curE ((val% «verify_keccak» "fs0@14") + j) = (D.oRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_i {c curE j : ℕ} (hj : j < 7) :
    D.w c curE ((val% «verify_keccak» "fs0@15") + j) = (D.iRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_s {c curE j : ℕ} (hj : j < 7) :
    D.w c curE ((val% «verify_keccak» "fs0@16") + j) = (D.sRets curE).getD j 0 := by
  interval_cases j <;> rfl

theorem w_layer {c curE s : ℕ} (hs : s < 12) {j : ℕ} (hj : j < 6) :
    D.w c curE (stepE s - 6 + j) =
      ((D.layer s).rets (firstOf s) (VsC.ptrAtV (curE + D.lcur s))).getD j 0 := by
  interval_cases s <;> interval_cases j <;> rfl

/-! ## The own words, read -/

theorem outWs_length (ls : ℕ → ℕ) (s : ℕ) : (D.outWs ls s).length = 22 := by
  simp [outWs, VsC.klOutW, LayerData.next, layerClaim, keccakInstanceWeights_length]

theorem wo_mem {c : ℕ} {ls : ℕ → ℕ} {q : ℕ × List E} (hq : q ∈ D.Wo c ls) {rd : Reader}
    (h : HoldsWords rd (D.Wo c ls)) : ReadsAt rd (VsC.ptrAtV q.1) q.2 := h q hq

/-- **The own words, each in memory.** -/
theorem own_mem {rd : Reader} {c : ℕ} {ls : ℕ → ℕ} (hm : HoldsWords rd (D.Wo c ls)) :
    ReadsAt rd (VsC.ptrAtV c) D.c0.point ∧ ReadsAt rd (VsC.ptrAtV (c + (D.τ - 3))) D.rl ∧
      ReadsAt rd (VsC.ptrAtV (c + D.o201)) (D.cw0 c) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.o201 + 6)) D.c0.mu ∧
      (∀ s < 12, ReadsAt rd (VsC.ptrAtV (c + D.o201 + 22 * (s + 1))) (D.outWs ls s)) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.τ + 288)) (eqLevels (D.chis.take 4) 4) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.o274)) (eqLevels D.rl 5) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.τ + 380)) (eqKernel D.seg) ∧
      ReadsAt rd (VsC.ptrAtV (c + D.τ + 382)) (eqLevels D.I.1 4) := by
  have hl : ∀ q ∈ [(c, D.c0.point), (c + (D.τ - 3), D.rl), (c + D.o201, D.cw0 c),
      (c + D.o201 + 6, D.c0.mu)], q ∈ D.Wo c ls :=
    fun q hq ↦ List.mem_append_left _ (List.mem_append_left _ hq)
  have hr : ∀ q ∈ [(c + D.τ + 288, eqLevels (D.chis.take 4) 4), (c + D.o274, eqLevels D.rl 5),
      (c + D.τ + 380, eqKernel D.seg), (c + D.τ + 382, eqLevels D.I.1 4)], q ∈ D.Wo c ls :=
    fun q hq ↦ List.mem_append_right _ hq
  refine ⟨hm (c, D.c0.point) (hl _ (by simp only [List.mem_cons, true_or])),
    hm (c + (D.τ - 3), D.rl) (hl _ (by simp only [List.mem_cons, true_or, or_true])),
    hm (c + D.o201, D.cw0 c) (hl _ (by simp only [List.mem_cons, true_or, or_true])),
    hm (c + D.o201 + 6, D.c0.mu) (hl _ (by simp only [List.mem_cons, true_or, or_true])),
    fun s hs ↦ hm (c + D.o201 + 22 * (s + 1), D.outWs ls s)
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨s, List.mem_range.2 hs, rfl⟩))),
    hm (c + D.τ + 288, eqLevels (D.chis.take 4) 4) (hr _ (by simp only [List.mem_cons, true_or])),
    hm (c + D.o274, eqLevels D.rl 5) (hr _ (by simp only [List.mem_cons, true_or, or_true])),
    hm (c + D.τ + 380, eqKernel D.seg) (hr _ (by simp only [List.mem_cons, true_or, or_true])),
    hm (c + D.τ + 382, eqLevels D.I.1 4) (hr _ (by simp only [List.mem_cons, true_or, or_true]))⟩

/-- The first claim's lanes, in the lane coordinates' tree. -/
theorem lanes_first {rd : Reader} {c : ℕ} (ht : ReadsAt rd (VsC.ptrAtV (c + D.o274)) (eqLevels D.rl 5)) :
    ReadsAt rd (VsC.ptrAtV (c + D.o274 + 30)) ((eqKernel D.rl).take 25) := by
  rw [eqLevels_succ] at ht
  have := (readsAt_append.1 ht).2
  rw [ptr_mul_gen, eqLevels_length (by rw [rl_length]; norm_num),
    show D.rl.take (4 + 1) = D.rl from List.take_of_length_le (by rw [rl_length])] at this
  intro k hk
  simp only [List.length_take, eqKernel_length, rl_length] at hk
  rw [List.getElem_take]
  exact this k (by simp [eqKernel_length, rl_length]; omega)

theorem c0_weights : D.c0.weights = firstWeights ((eqKernel D.rl).take 25) := by
  simp only [c0, vkFirst, firstWeights]
  refine List.map_congr_left fun j hj ↦ ?_
  have : j / 64 < 25 := by
    have := List.mem_range.1 hj; simp only [keccakBits] at this; omega
  simp [List.getD_eq_getElem?_getD, this]

/-- **The first claim's record.** -/
theorem rec0 (h : D.Ok) {rd : Reader} {c : ℕ} {ls : ℕ → ℕ} (hm : HoldsWords rd (D.Wo c ls)) :
    ClaimRec rd true (VsC.ptrAtV (c + D.o201)) D.c0 (D.τ - 3) := by
  obtain ⟨m0, -, mcw, mmu, -, -, mln, -, -⟩ := own_mem hm
  have hmu := c0_mu h
  have hcw : ∀ k < 4, LoadHolds rd (VsC.ptrAtV (c + D.o201)) k ((D.cw0 c).getD k 0) :=
    fun k hk ↦ readsAt_getD mcw (by simp [cw0]; omega)
  refine ⟨hmu, c0_point h, by simpa [cw0] using hcw 0 (by norm_num), ?_, fun i hi ↦ ?_,
    ⟨VsC.ptrAtV c, by simpa [cw0] using hcw 2 (by norm_num), m0⟩,
    VsC.ptrAtV (c + D.o274 + 30), (eqKernel D.rl).take 25, by simpa [cw0] using hcw 3 (by norm_num),
    by simp [eqKernel_length, rl_length], lanes_first mln, by simpa using c0_weights (D := D)⟩
  · rw [c0, vkFirst]; simp only; rw [sumE_eqKernel]; simpa [cw0] using hcw 1 (by norm_num)
  · have := readsAt_getD mmu (k := i) (by rw [hmu]; exact hi)
    rwa [← ptr_mul_gen, loadHolds_mul_gen_pow, show 6 + i = 6 + i from rfl] at this

/-- **Each claim's record.** -/
theorem recs (h : D.Ok) {rd : Reader} {c curE chiE olE zvE slE tbE : ℕ} {ls : ℕ → ℕ}
    (hm : D.Mem rd c curE chiE olE zvE slE tbE ls) :
    ∀ s ≤ 12, ClaimRec rd (decide (s = 0)) (VsC.ptrAtV (c + D.o201 + 22 * s)) (D.layer s).c (D.τ - 3)
  | 0, _ => by rw [layer_zero_c]; simpa using rec0 h hm.own
  | k + 1, hk => by
    have hc : (D.layer (k + 1)).c = (D.layer k).next (firstOf k) := by
      show (D.chain (k + 1)).1 = _
      rw [D.layer_succ h (by omega)]
    rw [hc]
    simpa using hm.lay k (by omega)

end VkData

end
end LeanVM.Guest.B1.VerifySub
