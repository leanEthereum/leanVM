/-
  LeanVM.Guest.B1.VsC.VkPM

  **`verify_keccak` completes placed** from its layers' completeness (`vkFromLayerA`), hence
  `verifyKeccakCompleteA`.
-/

module

public import LeanVM.Guest.B1.VsC.VkPL
public import LeanVM.Guest.B1.VsC.SqueezePackedA
public import LeanVM.Guest.B1.VsC.VkEnd
public import LeanVM.Guest.B1.VsC.CalleesB
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_keccak»

/-!
# `verify_keccak`, placed

`vkFromLayerA`: `VkFromLayerA fs al cert k`. A memory holding the caller's words fixes its
pointers as word indices (else no memory satisfies the precondition); the run is a `VkData`'s. If
a memory holds the layout (`Mem`), `callAtA_nodeRd` on the honest valuation of such a memory
before the memory, the callees by `vk_kids`, on each memory the body by `body_holds`; otherwise no
memory holding the callees' words satisfies the precondition. `verifyKeccakCompleteA`: with
`KL.keccakLayerCompleteA`, the field `vsCalleesCompleteA_of_rest` takes.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset LeanVM.Guest.B1.VerifySub.KL
open LeanVM.Prover.Exec (allocBase)

open LeanVM.Guest.B1.VsC (PostQuiet lpB clArgs plain60_placed plain41_placed)

@[expose] public section

/-- A pointer read through is a word index's. -/
theorem ptr_of_load {rd : Reader} {p a : E} (h : LoadHolds rd p 0 a) {i : ℕ}
    (hi : p.limb 0 * addressOfIndex 0 = addressOfIndex i) : p = VsC.ptrAtV i := by
  obtain ⟨a0, rfl⟩ := (isInK_iff _).mp h.1
  have e : a0 = addressOfIndex i := by simpa using hi
  rw [e]

theorem vkPre_callIfs : vkPre.all (fun s ↦ match s with
    | .callIf c _ _ => c == .n (val% «verify_keccak» "s17#1") || c == .n (val% «verify_keccak» "s57#1") ||
        c == .n (val% «verify_keccak» "s81#1")
    | _ => true) = true := by decide +kernel

theorem vkPre_quiet : vkPre.all VsC.stmtQuietB = true := by decide +kernel

theorem vkPre_noHeap : vkPre.all VsC.noHeapHintB = true := by decide +kernel

/-- The bits' hint aside, nothing of the body is computed. -/
theorem vkPre_noComputed : vkPre.all (fun s ↦ stmtsEqb [s] [.atom (.hint (.bitsExp (.n 20) 5
    (.stack [.n 21, .n 22, .n 23, .n 24, .n 25])))] || VsC.noComputedB s) = true := by decide +kernel

/-- **The events don't depend on the valuation** past the copy loops' conditions. -/
theorem evs_eq {σ σ' : Val} (h1 : σ (.n (val% «verify_keccak» "s17#1")) ≠ 0)
    (h2 : σ (.n (val% «verify_keccak» "s57#1")) ≠ 0) (h3 : σ (.n (val% «verify_keccak» "s81#1")) ≠ 0)
    (h1' : σ' (.n (val% «verify_keccak» "s17#1")) ≠ 0)
    (h2' : σ' (.n (val% «verify_keccak» "s57#1")) ≠ 0) (h3' : σ' (.n (val% «verify_keccak» "s81#1")) ≠ 0) :
    vkPre.flatMap (slEvs σ) = vkPre.flatMap (slEvs σ') := by
  refine List.flatMap_congr fun s hs ↦ ?_
  have hc := List.all_eq_true.mp vkPre_callIfs s hs
  cases s with
  | callIf c f args =>
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    simp only [slEvs]
    rcases hc with (rfl | rfl) | rfl <;> simp [h1, h2, h3, h1', h2', h3']
  | _ => rfl

namespace VkData

variable {D : VkData} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
variable {c curE chiE olE zvE slE tbE : ℕ}

/-- Each run ends at or before the next one starts. -/
def RunsSorted : Words → Prop
  | q :: q' :: rest => q.1 + q.2.length ≤ q'.1 ∧ RunsSorted (q' :: rest)
  | _ => True

/-- **Runs one after the other are pairwise disjoint.** -/
theorem pairwise_of_sorted : ∀ {W : Words}, RunsSorted W →
    W.Pairwise fun q q' => q.1 + q.2.length ≤ q'.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | q :: q' :: rest, h => by
    obtain ⟨h1, h2⟩ := h
    have ih := pairwise_of_sorted h2
    refine List.Pairwise.cons (fun r hr ↦ ?_) ih
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · have := List.rel_of_pairwise_cons ih hr
      omega

/-- The own words, listed. -/
theorem wo_eq (ls : ℕ → ℕ) : D.Wo c ls = [(c, D.c0.point), (c + (D.τ - 3), D.rl), (c + D.o201, D.cw0 c),
      (c + D.o201 + 6, D.c0.mu),
      (c + D.o201 + 22 * (0 + 1), D.outWs ls 0),
      (c + D.o201 + 22 * (1 + 1), D.outWs ls 1),
      (c + D.o201 + 22 * (2 + 1), D.outWs ls 2),
      (c + D.o201 + 22 * (3 + 1), D.outWs ls 3),
      (c + D.o201 + 22 * (4 + 1), D.outWs ls 4),
      (c + D.o201 + 22 * (5 + 1), D.outWs ls 5),
      (c + D.o201 + 22 * (6 + 1), D.outWs ls 6),
      (c + D.o201 + 22 * (7 + 1), D.outWs ls 7),
      (c + D.o201 + 22 * (8 + 1), D.outWs ls 8),
      (c + D.o201 + 22 * (9 + 1), D.outWs ls 9),
      (c + D.o201 + 22 * (10 + 1), D.outWs ls 10),
      (c + D.o201 + 22 * (11 + 1), D.outWs ls 11),
      (c + D.τ + 288, eqLevels (D.chis.take 4) 4), (c + D.o274, eqLevels D.rl 5),
      (c + D.τ + 380, eqKernel D.seg), (c + D.τ + 382, eqLevels D.I.1 4)] := rfl

/-- **The own words lie in the buffers**, one after the other. -/
theorem wo_in (h : D.Ok) (ls : ℕ → ℕ) (lo hi : ℕ) : WordsInA (D.Wo c ls) lo hi c (c + D.τ + 412) := by
  have hτ1 := h.1
  have hp := c0_point_length h
  have hmu := c0_mu h
  have hl4 : 4 ≤ (D.chis.take 4).length := by simp; have := h.2.2.1; omega
  have e1 : (eqLevels (D.chis.take 4) 4).length = 30 := by rw [eqLevels_length hl4]; norm_num
  have e2 : (eqLevels D.rl 5).length = 62 := by rw [eqLevels_length (by rw [rl_length])]; norm_num
  have e3 : (eqLevels D.I.1 4).length = 30 := by rw [eqLevels_length (by rw [I1_length h])]; norm_num
  have hseg : (eqKernel D.seg).length = 2 := by rw [eqKernel_length, seg_length]; norm_num
  have hcw : (D.cw0 c).length = 4 := rfl
  have hol : ∀ s, (D.outWs ls s).length = 22 := outWs_length ls
  rw [wo_eq]
  refine ⟨fun q hq ↦ Or.inr ?_, (pairwise_of_sorted ?_).imp Or.inl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [hp, rl_length, hcw, hmu, hol, e1, e2, e3, hseg, o201, o274]
    all_goals omega
  · simp only [RunsSorted, hp, rl_length, hcw, hmu, hol, e1, e2, hseg, o201, o274, and_true]
    and_intros
    all_goals omega

/-- What `verify_keccak` loads from of its own and its caller's, as `callAtA_nodeRd` regions. -/
theorem hRN_of (h : D.Ok) {fp : ℕ} {es : List LeanVM.Guest.Memory.Ev} (cert : String → V → ℕ) :
    ∀ i, ((c ≤ i ∧ i < c + D.τ + 412) ∨ D.LinR curE chiE olE zvE slE i ∨
      (tbE ≤ i ∧ i < tbE + 2 ^ winTabBits)) →
      VsC.ptrRegion (VsC.vkArrays (VsC.ptrAtV curE) (VsC.ptrAtV chiE) (VsC.ptrAtV olE) (VsC.ptrAtV zvE)
        (VsC.ptrAtV slE) (VsC.ptrAtV tbE) D.xs D.chis D.op D.point) i ∨
      ownData cert fp c "verify_keccak" D.sizes es i := by
  have hτ1 := h.1
  intro i hi
  have pr : ∀ (a n : ℕ), (VsC.ptrAtV a, n) ∈ VsC.vkArrays (VsC.ptrAtV curE) (VsC.ptrAtV chiE)
      (VsC.ptrAtV olE) (VsC.ptrAtV zvE) (VsC.ptrAtV slE) (VsC.ptrAtV tbE) D.xs D.chis D.op D.point →
      a ≤ i → i < a + n → VsC.ptrRegion (VsC.vkArrays (VsC.ptrAtV curE) (VsC.ptrAtV chiE) (VsC.ptrAtV olE)
        (VsC.ptrAtV zvE) (VsC.ptrAtV slE) (VsC.ptrAtV tbE) D.xs D.chis D.op D.point) i :=
    fun a n hm h1 h2 ↦ ⟨_, hm, i - a, by simp only; omega, by rw [ptr_addr]; congr 1; omega⟩
  rcases hi with hi | (hi | hi | hi | hi | hi | hi) | hi
  · right; left
    rw [bases_eq D c (by omega)]
    simp only [sizes, List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false]
    rcases (by omega : i < c + (D.τ - 3) ∨ (c + (D.τ - 3) ≤ i ∧ i < c + (D.τ - 3) + 5) ∨
      (c + (D.τ + 2) ≤ i ∧ i < c + (D.τ + 2) + 286) ∨ (c + D.τ + 288 ≤ i ∧ i < c + D.τ + 288 + 30) ∨
      (c + (D.τ + 318) ≤ i ∧ i < c + (D.τ + 318) + 62) ∨ (c + D.τ + 380 ≤ i ∧ i < c + D.τ + 380 + 2) ∨
      (c + D.τ + 382 ≤ i)) with h' | h' | h' | h' | h' | h' | h'
    · exact ⟨_, Or.inl rfl, by simp only; omega, by simp only; omega⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by simp only; omega, by simp only; omega⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by simp only [o201]; omega, by simp only [o201]; omega⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by simp only; omega, by simp only; omega⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), by simp only [o274]; omega,
        by simp only [o274]; omega⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by simp only; omega,
        by simp only; omega⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), by simp only; omega,
        by simp only; omega⟩
  · exact Or.inl (pr curE _ (by simp [VsC.vkArrays]) hi.1 hi.2)
  · exact Or.inl (pr chiE _ (by simp [VsC.vkArrays]) hi.1 hi.2)
  · exact Or.inl (pr olE 25 (by simp [VsC.vkArrays]) hi.1 (by rw [h.2.2.2.1] at hi; exact hi.2))
  · exact Or.inl (pr zvE _ (by simp [VsC.vkArrays]) hi.1 hi.2)
  · exact Or.inl (pr (zvE + qkeccakVarsCap) D.point.length (by simp [VsC.vkArrays, ptr_mul_gen]) hi.1 hi.2)
  · exact Or.inl (pr slE 64 (by simp [VsC.vkArrays]) hi.1
      (by rw [h.2.2.2.2.2.2.2.2.2.1] at hi; exact hi.2))
  · exact Or.inl (pr tbE _ (by simp [VsC.vkArrays]) hi.1 hi.2)

/-- **The calls of two valuations carrying the honest words agree.** -/
theorem callsAgree_of_x {σ σ' : Val} (hx : D.HonestX fs al cert k c curE chiE zvE tbE σ)
    (hx' : D.HonestX fs al cert k c curE chiE zvE tbE σ')
    (h1 : σ (.n (val% «verify_keccak» "s17#1")) ≠ 0) (h2 : σ (.n (val% «verify_keccak» "s57#1")) ≠ 0)
    (h3 : σ (.n (val% «verify_keccak» "s81#1")) ≠ 0) :
    VsC.CallsAgree σ σ' (calls (vkPre.flatMap (slEvs σ))) := by
  rw [calls_eq h1 h2 h3]
  obtain ⟨a0, as, ao, ro, a1, ai, ri, as', rs', a2⟩ := hx
  obtain ⟨b0, bs, bo, so, b1, bi, si, bs', ss', b2⟩ := hx'
  intro cl hcl
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | ⟨s, hs, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · exact ⟨a0.trans b0.symm, rfl⟩
  · exact ⟨(as s hs).1.trans (bs s hs).1.symm, (as s hs).2.trans (bs s hs).2.symm⟩
  · exact ⟨ao.trans bo.symm, ro.trans so.symm⟩
  · exact ⟨a1.trans b1.symm, rfl⟩
  · exact ⟨ai.trans bi.symm, ri.trans si.symm⟩
  · exact ⟨as'.trans bs'.symm, rs'.trans ss'.symm⟩
  · exact ⟨a2.trans b2.symm, rfl⟩

theorem vk_wf : Stmt.wfList coreProgram vkT = true := by decide +kernel

theorem loadS_eq : vkPre.filterMap Memory.stmtLoad? = vkPre.filterMap LeanVM.Guest.B1.Stmt.loadS := by
  decide +kernel

theorem vk_params : (fn% «verify_keccak»).params = (List.range 12).map V.n := by decide +kernel

/-- The honest valuation takes the arguments. -/
theorem params_val (h : D.Ok) {rd : Reader} :
    (fn% «verify_keccak»).params.map (D.val rd c curE chiE olE zvE slE tbE) =
      D.args curE chiE olE zvE slE tbE := by
  rw [vk_params]
  apply List.ext_getElem (by simp [args_length h])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [(val_good h).2.2 i (by simpa using h1), List.getD_eq_getElem _ _ h2]

/-- The bits' hint is exact on the honest valuation. -/
theorem bits_exact (h : D.Ok) {rd : Reader} :
    (Atom.hint (.bitsExp (.n 20) 5 (.stack [.n 21, .n 22, .n 23, .n 24, .n 25]))).Exact rd
      (D.val rd c curE chiE olE zvE slE tbE) := by
  have hτ1 := h.1
  have hτ2 := h.2.1
  set σ := D.val rd c curE chiE olE zvE slE tbE with hσd
  have hG : ∀ s ∈ vkT, pinB s = false → GoodS rd vkSt (D.w c curE) σ s := (val_good h).2.1
  have mB : ∀ s ∈ vkBitsT, s ∈ vkT := fun s hs ↦ by
    rw [vkT]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ ?_))))
    rw [vkHeadT]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hs))))
  have hbits : ∀ j < 5, σ (.n (21 + j)) = Value.bitE ((D.τ - 3).testBit j) := by
    intro j hj
    have g := hG (.atom (.hint (.bitsExp (.n 20) 5 (.stack [.n 21, .n 22, .n 23, .n 24, .n 25]))))
      (mB _ (by simp [vkBitsT])) rfl
    exact (g (.n (21 + j)) (by simp; omega)).trans (w_bits hj)
  have hpar : ∀ i < 12, σ (.n i) = (D.args curE chiE olE zvE slE tbE).getD i 0 := (val_good h).2.2
  have p6 : σ (.n (val% «verify_keccak» "tau_g")) = gen ^ D.τ := by
    obtain ⟨f0, f1, f2, f3, f4, hf⟩ := five_of_length' h.2.2.2.2.1
    rw [hpar _ (by norm_num), args, hf]; rfl
  obtain ⟨-, h20, -⟩ := vkBits_complete (C := fun _ _ _ ↦ True) hτ1 hτ2
    (fun s hs hp ↦ hG s (mB s hs) hp) p6 hbits
  refine ⟨D.τ - 3, by omega, by rw [show (20 : ℕ) = val% «verify_keccak» "s5#1" from rfl, h20, gen_pow_eq_ofK], ?_⟩
  show [σ (.n (21 + 0)), σ (.n (21 + 1)), σ (.n (21 + 2)), σ (.n (21 + 3)), σ (.n (21 + 4))] = _
  rw [hbits 0 (by norm_num), hbits 1 (by norm_num), hbits 2 (by norm_num), hbits 3 (by norm_num),
    hbits 4 (by norm_num)]
  rfl

end VkData

open VkData in
set_option maxRecDepth 20000 in
/-- **`verify_keccak` completes placed**, given its layers' placed completeness, its callees ending
within `2^24` of its cursor when every frame is small. -/
theorem vkFromLayerAE {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    (hL : VsC.KeccakLayerCompleteA fs al cert k) :
    VsC.VerifyKeccakCompleteAE fs al cert k (fun c e => VsC.FsSmall fs → e ≤ c + 2 ^ 24) := by
  intro f0 f1 f2 f3 f4 cur chi ol zv sl tabs τ chis outs xs op point slices word s' fp hτ1 hτ2 hchis houts
    hcar hrun hpend hsl hpb
  by_cases hex : ∃ rd, WinTabs rd tabs ∧ ReadsAt rd chi chis ∧ ReadsAt rd ol outs ∧ ReadsAt rd cur xs ∧
      ReadsAt rd zv op ∧ ReadsAt rd (zv * gen ^ qkeccakVarsCap) point ∧ ReadsAt rd sl slices
  swap
  · exact ⟨fp + fs "verify_keccak", fun _ => Nat.le_add_right _ _, callAtA_vacuous fun rd hp ↦ hex ⟨rd, hp⟩⟩
  obtain ⟨rd0, htb0, hchi0, hol0, hcur0, hzv0, -, hsl0⟩ := hex
  obtain ⟨D, rfl, hDf, rfl, rfl, rfl, rfl, h, rfl, rfl, rfl, rfl⟩ :=
    vkData_of_run (f := [f0, f1, f2, f3, f4]) hτ1 (hτ2.trans (by decide)) hchis houts rfl hcar hrun
  have hτ1' := h.1
  -- the pointers are word indices
  have idx : ∀ (p : E) (n : ℕ) (v : E), (p, n) ∈ VsC.vkArrays cur chi ol zv sl tabs D.xs D.chis D.op D.point →
      0 < n → LoadHolds rd0 p 0 v → ∃ i, p = VsC.ptrAtV i := by
    intro p n v hm hn hl
    obtain ⟨i, -, he⟩ := hpb _ hm 0 hn
    exact ⟨i, ptr_of_load hl he⟩
  have hxL := xs_len h
  have hopL := op_length h
  obtain ⟨curE, rfl⟩ := idx cur D.xs.length _ (by simp [VsC.vkArrays]) (by omega) (readsAt_getD hcur0 (k := 0) (by omega))
  obtain ⟨chiE, rfl⟩ := idx chi D.chis.length _ (by simp [VsC.vkArrays]) (by have := h.2.2.1; omega)
    (readsAt_getD hchi0 (k := 0) (by have := h.2.2.1; omega))
  obtain ⟨olE, rfl⟩ := idx ol 25 _ (by simp [VsC.vkArrays]) (by norm_num)
    (readsAt_getD hol0 (k := 0) (by rw [h.2.2.2.1]; norm_num))
  obtain ⟨zvE, rfl⟩ := idx zv D.op.length _ (by simp [VsC.vkArrays]) (by omega) (readsAt_getD hzv0 (k := 0) (by omega))
  obtain ⟨slE, rfl⟩ := idx sl 64 _ (by simp [VsC.vkArrays]) (by norm_num)
    (readsAt_getD hsl0 (k := 0) (by rw [h.2.2.2.2.2.2.2.2.2.1]; norm_num))
  obtain ⟨tbE, rfl⟩ := idx tabs (2 ^ winTabBits) _ (by simp [VsC.vkArrays]) (by positivity)
    (htb0 0 (by positivity))
  set c := fp + fs "verify_keccak" with hc
  set ls := D.lsP fs al cert k c curE tbE with hls
  by_cases hM : ∃ rd, D.Mem rd c curE chiE olE zvE slE tbE ls
  swap
  · -- no memory holds the layout: the callees' words and the own words, vacuously
    obtain ⟨σ, cs, hH⟩ := honest_exists (fs := fs) (al := al) (cert := cert) (k := k) (c := c) (curE := curE)
      (chiE := chiE) (zvE := zvE) (tbE := tbE) h
    have hK := vk_kids (olE := olE) (slE := slE) hL h (fun i hi ↦ hRN_of (fp := fp) (es := []) h cert i hi) hH
    obtain ⟨Wk, hle, hin, hdisj, hO, -⟩ := kidsAtF_words _ _ _ _ _ _ _ _ hK
    have hwo := wo_in h ls (fp + 2) (fp + fs "verify_keccak") (c := c)
    refine ⟨D.eF fs al cert k c curE tbE, fun hfs => eF_le hL h hfs, D.WoP fs al cert k c curE tbE ++ Wk, ⟨fun q hq ↦ ?_, ?_⟩,
      by omega, fun _ _ ↦ trivial, fun rd _ hW hP ↦ ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · rcases hwo.1 q hq with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h'.1, by omega⟩
      · have := hin q hq; exact Or.inr ⟨by omega, this.2⟩
    · refine List.pairwise_append.mpr ⟨hwo.2, hdisj, fun q hq q' hq' ↦ Or.inl ?_⟩
      have := hin q' hq'
      rcases hwo.1 q hq with h' | h' <;> omega
    · obtain ⟨hw1, hw2⟩ := holdsWords_append.mp hW
      exact (hM ⟨rd, mem_of_oend hP (hO rd hw1 hw2)⟩).elim
  -- a memory holds the layout: the honest valuation of one, before the memory
  obtain ⟨rdM, hmM⟩ := hM
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, σ0 = D.val rdM c curE chiE olE zvE slE tbE := ⟨_, rfl⟩
  obtain ⟨c1, c2, c3⟩ := conds (D := D) (rd := rdM) (c := c) (curE := curE) (chiE := chiE) (olE := olE)
    (zvE := zvE) (slE := slE) (tbE := tbE) h
  have hx0 := honestX_of_mem h hmM
  rw [← hσ0] at c1 c2 c3 hx0
  obtain ⟨es, hes⟩ : ∃ es, es = vkPre.flatMap (slEvs σ0) := ⟨_, rfl⟩
  have hH := honest_of_x hx0 c1 c2 c3
  have hsp0 := straight_parts σ0 vkPre vkPre_kernel.1
  rw [← hes] at hH hsp0
  have h17M := (head_first h hmM hσ0).2.2.2.2.2.2.2.1
  have hal0 : allocs σ0 es = D.sizes := by rw [hsp0.2.1, body_sizes h hσ0 h17M]
  have hsum : D.sizes.sum = D.τ + 412 := by simp only [sizes, List.sum_cons, List.sum_nil]; omega
  have hlp : coreProgram.loop "verify_keccak" = false := by
    rw [Program.loop_of_find? find_vk, Fn.loop, vk_body, vkT_pre]; simp [vkVs]
  refine ⟨D.eF fs al cert k c curE tbE, fun hfs => eF_le hL h hfs, callAtA_nodeRd hlp le_rfl ⟨σ0, fn% «verify_keccak», es, vkVs,
    D.WoP fs al cert k c curE tbE, List.replicate 18 PostQuiet, D.Oend fs al cert k c curE tbE,
    D.Dend fs al cert k c curE tbE, find_vk, ?_, fun _ h ↦ h.elim, ?_, fun _ _ ↦ trivial, ?_⟩⟩
  · rw [hal0, hsum, ← Nat.add_assoc]; exact wo_in h ls _ _
  · rw [hal0, hsum, ← Nat.add_assoc]
    have hK := vk_kids (c := c) (curE := curE) (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) (σ := σ0) (cs := calls es) hL h
      (fun i hi ↦ hRN_of (fp := fp) (es := es) (c := c) (curE := curE) (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) h cert i hi) hH
    exact hK
  -- on a memory
  intro rd hl hP hO
  have hm := mem_of_oend (c := c) (curE := curE) (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) hP hO
  obtain ⟨σ, hσd⟩ : ∃ σ, σ = D.val rd c curE chiE olE zvE slE tbE := ⟨_, rfl⟩
  obtain ⟨d1, d2, d3⟩ := conds (D := D) (rd := rd) (c := c) (curE := curE) (chiE := chiE) (olE := olE)
    (zvE := zvE) (slE := slE) (tbE := tbE) h
  have hxσ := honestX_of_mem h hm
  rw [← hσd] at d1 d2 d3 hxσ
  have hes' : vkPre.flatMap (slEvs σ) = es := by rw [hes]; exact evs_eq d1 d2 d3 c1 c2 c3
  have hwalk' : walk σ (fn% «verify_keccak»).body = .ret (vkPre.flatMap (slEvs σ)) vkVs := by
    rw [vk_body, vkT_pre, walk_straight σ vkVs vkPre vkPre_kernel.1]
  have hwalk : walk σ (fn% «verify_keccak»).body = .ret es vkVs := by rw [hwalk', hes']
  have h17 := (head_first h hm hσd).2.2.2.2.2.2.2.1
  have hsat := walk_sat (P := coreProgram) vkT vk_wf (body_holds h hm hσd)
  rw [← vk_body, hwalk] at hsat
  obtain ⟨hevs, hret⟩ := hsat
  have hRN := hRN_of (fp := fp) (es := es) (c := c) (curE := curE) (chiE := chiE) (olE := olE) (zvE := zvE) (slE := slE) (tbE := tbE) h cert
  refine ⟨σ, by rw [hσd, params_val h, args, hDf]; rfl, hwalk, hret, ?_, ⟨?_, ?_⟩,
    by rw [hes]; exact callsAgree_of_x hx0 hxσ c1 c2 c3, ?_, ?_, fun ev hev ↦ (hevs ev hev).1,
    fun ts hv hp ↦ ?_⟩
  · rw [hal0, ← hes', (straight_parts σ vkPre vkPre_kernel.1).2.1, body_sizes h hσd h17]
  · rw [hal0, hsp0.1, body_bases h hσd]
  · rw [hsp0.2.2.1, vkPre_kernel.2.1]; simp
  · intro A hA
    rw [← hes', Memory.loadAddrs_straight σ vkPre vkPre_kernel.1, loadS_eq, List.mem_map] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    rw [hal0]
    exact loads_in h hm hσd
      (fun i hi ↦ (hRN i (Or.inr (Or.inl hi))).elim (fun h ↦ Or.inr (Or.inl h)) Or.inl)
      (fun i h1 h2 ↦ (hRN i (Or.inl ⟨h1, h2⟩)).elim (fun h ↦ Or.inr (Or.inl h)) Or.inl)
      (fun s hs i h1 h2 ↦ Or.inr (Or.inr ⟨s, hs, h1, h2⟩)) q hq
  · intro A hA
    rw [hes, VsC.heapHintAddrs_nil_of vkPre vkPre_noHeap] at hA
    simp at hA
  · rw [← hes'] at hv hp
    refine VsC.postQuiet_node find_vk hwalk' (fun a ha ↦ ?_) (fun ev hev ↦ ?_) hv ?_ _
    · obtain ⟨s, hs, ha⟩ := List.mem_flatMap.mp ha
      exact VsC.quiet_of_slEvs (List.all_eq_true.mp vkPre_quiet s hs) ha
    · obtain ⟨s, hs, hev⟩ := List.mem_flatMap.mp hev
      have := List.all_eq_true.mp vkPre_noComputed s hs
      simp only [Bool.or_eq_true] at this
      rcases this with hh | hnc
      · obtain rfl := List.head_eq_of_cons_eq (stmtsEqb_sound hh)
        simp only [slEvs, List.mem_singleton] at hev
        subst hev
        rw [hσd]; exact bits_exact h
      · exact VsC.exact_of_slEvs hnc hev
    · have hlen : (calls (vkPre.flatMap (slEvs σ))).length = 18 := by
        rw [(straight_parts σ vkPre vkPre_kernel.1).2.2.2, vkPre_kernel.2.2.2]; rfl
      rw [List.map_const', hlen]; exact hp


/-- **`verify_keccak` completes placed**, given its layers' placed completeness. -/
theorem vkFromLayerA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} :
    VsC.VkFromLayerA fs al cert k := fun hL => (vkFromLayerAE hL).toA

/-- **`verify_keccak` completes placed, its end within `2^24` of its cursor**, every frame small. -/
theorem verifyKeccakCompleteAB {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    (hk : 11 ≤ k) (hfs : VsC.FsSmall fs) : VsC.VerifyKeccakCompleteAB fs al cert k 24 :=
  (vkFromLayerAE (KL.keccakLayerCompleteA hk)).mono fun _ _ h _ => h hfs

/-- **`verify_keccak` completes placed**, its layers by `KL.keccakLayerCompleteA`. -/
theorem verifyKeccakCompleteA {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ}
    (hk : 11 ≤ k) : VsC.VerifyKeccakCompleteA fs al cert k :=
  vkFromLayerA (KL.keccakLayerCompleteA hk)

end
end LeanVM.Guest.B1.VerifySub
