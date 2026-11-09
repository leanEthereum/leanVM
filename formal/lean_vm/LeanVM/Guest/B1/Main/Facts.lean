/-
  LeanVM.Guest.B1.Main.Facts

  What a run of `main`'s body gives (`MainFacts`), from its facts checked by evaluation, the
  digest family's statements and the loops'.
-/

module

public import LeanVM.Guest.B1.Main.Body
public import LeanVM.Guest.B1.Main.LoopsC

/-!
# `main`'s facts

`main_facts`: on a memory image, a run of `main`'s body (under a call relation `C` that unfolds
and lies below `coreProgram.Rel`) gives
`MainFacts`: the counts as powers of `g` (`lg σ v`, the exponent of `σ (.n v)`) with their
bounds, the region sizes, the exponent tables, the declared lists' digests, the byte table, every
raw signature's and every child's iteration, the node's own DA digest slot (the direct DA check's
claim hashed, or zeros), the running counts, the picked DA slot (`da_pick`, the node's own with a
direct DA check) and its two cells, the leaf's or the batching's deferred claim, and the
statement's digest in the public input cells. The signature checks, the DA check, the child
proofs' checks and the batching stay calls of `C`; the other calls are `coreProgram.Rel`'s.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Exponents -/

/-- On at most `2^63` words, the search is `addressIndex?`. -/
theorem indexSearch_eq {κ : ℕ} (hκ : κ < 64) (a : K) : indexSearch κ a = addressIndex? κ a := by
  rcases h : indexSearch κ a with _ | i
  · unfold indexSearch at h
    exact (gLog?_eq_none_iff.mpr fun i hi ↦ by
      simpa [hi] using List.find?_eq_none.mp h i (List.mem_finRange i)).symm
  · unfold indexSearch at h
    have hi := List.find?_some h
    exact ((gLog?_spec hκ).mpr (of_decide_eq_true hi)).symm

theorem gLog_gen_pow {e : ℕ} (he : e < 2 ^ 34) : gLog (gen ^ e) = e := by
  unfold gLog
  rw [indexSearch_eq (by norm_num), gen_pow_eq_ofK, limb_ofK]
  simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
  rw [(gLog?_spec (κ := 34) (by norm_num) (i := ⟨e, he⟩)).mpr rfl]
  rfl

/-- The exponent of `main`'s value `v`. -/
@[irreducible] noncomputable def lg (σ : Val) (v : ℕ) : ℕ := gLog (σ (.n v))

theorem pow_lg {σ : Val} {v e : ℕ} (he : e < 2 ^ 34) (h : σ (.n v) = gen ^ e) :
    σ (.n v) = gen ^ lg σ v ∧ lg σ v = e := by
  have : lg σ v = e := by rw [lg, h, gLog_gen_pow he]
  exact ⟨by rw [this]; exact h, this⟩

/-! ## The facts -/

/-- **What a run of `main`'s body gives.** -/
structure MainFacts (C : CallRel) (rd : Reader) (σ : Val) : Prop where
  counts : ∀ v ∈ [0, 1, 2, 3, 4, 5], σ (.n v) = gen ^ lg σ v ∧ lg σ v ≤ 65535
  kids : σ (.n 6) = gen ^ lg σ 6 ∧ lg σ 6 ≤ 16
  direct : σ (.n 7) = gen ^ lg σ 7 ∧ lg σ 7 ≤ 1
  lxs : σ (.n 40) = gen ^ (lg σ 0 + lg σ 1)
  lss : σ (.n 41) = gen ^ (lg σ 3 + lg σ 4)
  total : σ (.n 42) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4)) ∧
    lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4) ≤ 65535
  exp : ExpTables rd (σ (.n 49))
  xlist : ClaimListOut rd (σ (.n 52)) (lg σ 0) [σ (.n 56), σ (.n 57)]
  slist : ClaimListOut rd (σ (.n 55)) (lg σ 3) [σ (.n 58), σ (.n 59)]
  bytes : Sig.ByteBits rd (σ (.n 68))
  spcov : σ (.n 67) = σ (.n 66) * σ (.n 40)
  rawx : ∀ i < lg σ 2, C "__loop2" (gen ^ i :: l2Args σ) [] ∧
    ∃ s, BelowLog (σ (.n 40)) s ∧ LoadHolds rd (σ (.n 66)) s (gen ^ i)
  tags : Sig.LxTagsHold (fun j => (l2Args σ).getD (4 + j) 0)
  raws : ∀ j < lg σ 5, RawSStepC C rd (σ (.n 41)) (σ (.n 66)) (σ (.n 40)) (σ (.n 2)) (σ (.n 55))
    (σ (.n 68)) (gen ^ j)
  own : σ (.n 387) = σ (.n 385) * gen ^ (2 * lg σ 6)
  da : lg σ 7 = 1 →
    C "da_verify" [σ (.n 49)] [σ (.n 390), σ (.n 391), σ (.n 392), σ (.n 393)] ∧
    AllCanonical [σ (.n 390), σ (.n 391), σ (.n 392), σ (.n 393)] ∧
    LoadHolds rd (σ (.n 387)) 0
      (digestHalves (keccak256 (cellsBytes [σ (.n 390), σ (.n 391), σ (.n 392), σ (.n 393)]))).1 ∧
    LoadHolds rd (σ (.n 387)) 1
      (digestHalves (keccak256 (cellsBytes [σ (.n 390), σ (.n 391), σ (.n 392), σ (.n 393)]))).2
  daz : lg σ 7 = 0 → LoadHolds rd (σ (.n 387)) 0 0 ∧ LoadHolds rd (σ (.n 387)) 1 0
  written0 : LoadHolds rd (σ (.n 420)) 0 (gen ^ (lg σ 2 + lg σ 5))
  children : ∀ c < lg σ 6, KidStepC C rd (σ (.n 420)) (σ (.n 52)) (σ (.n 66)) (σ (.n 40))
    (σ (.n 55)) (σ (.n 67)) (σ (.n 41)) (σ (.n 417)) (σ (.n 385)) (σ (.n 47)) (σ (.n 48))
    (σ (.n 405)) (σ (.n 49)) (σ (.n 411)) (gen ^ c)
  writtenN : LoadHolds rd (σ (.n 420)) (lg σ 6) (σ (.n 42))
  pick : σ (.n 427) = gen ^ lg σ 427 ∧ lg σ 427 ≤ lg σ 6 ∧ (lg σ 7 = 1 → lg σ 427 = lg σ 6)
  picked : σ (.n 437) = σ (.n 385) * gen ^ (2 * lg σ 427)
  leaf : lg σ 6 = 0 → ∀ k < 23, LoadHolds rd (σ (.n 438)) k 0
  agg : lg σ 6 ≠ 0 → C "aggregate_claims"
    [σ (.n 6), σ (.n 405), σ (.n 411), σ (.n 417), σ (.n 438)] []
  dacells : LoadHolds rd (σ (.n 437)) 0 (σ (.n 465)) ∧ LoadHolds rd (σ (.n 437)) 1 (σ (.n 466))
  stmt : coreProgram.Rel rd "statement_digest"
    [σ (.n 47), σ (.n 48), σ (.n 56), σ (.n 57), σ (.n 58), σ (.n 59), σ (.n 465), σ (.n 466),
      σ (.n 438)] [σ (.n 467), σ (.n 468)]
  pub : LoadHolds rd 1 0 (σ (.n 467)) ∧ LoadHolds rd 1 1 (σ (.n 468))

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

set_option maxRecDepth 100000 in
theorem noRet_mDa : Stmt.noRetList mDa = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mDaZ : Stmt.noRetList mDaZ = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mLeaf : Stmt.noRetList mLeaf = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem noRet_mAgg : Stmt.noRetList mAgg = true := by decide +kernel

theorem gen_pow_inj34 {a b : ℕ} (ha : a < 2 ^ 34) (hb : b < 2 ^ 34) (h : gen ^ a = gen ^ b) :
    a = b :=
  gen_pow_inj (by omega) (by omega) h

theorem gen_add_one_ne : gen + (1 : E) ≠ 0 := by
  intro h
  have h1 : gen ^ 1 = gen ^ 0 := by rw [pow_one, pow_zero]; exact e_add_eq_zero_iff.mp h
  exact absurd (gen_pow_inj34 (by norm_num) (by norm_num) h1) (by norm_num)

set_option maxRecDepth 100000 in
/-- **The facts of a run of `main`'s body**, on a memory image, given `exponent_tables`' statement
(B1-a). -/
theorem main_facts {rd : Reader} {C : CallRel} (hC : Unfolds rd C)
    (hle : CallRel.Le C (coreProgram.Rel rd)) (hm : MemOk rd) (hexp : exponent_tables_Spec)
    (hX : ∀ args, C "__loop2" args [] → ∃ sig, Loop2Out C rd args sig)
    {σ : Val} (h : Stmt.HoldsList C rd σ (Fn.body Data.core0) False (fun rs => rs = [])) :
    MainFacts C rd σ := by
  rw [core0_shape] at h
  simp only [List.append_assoc, holdsList_append] at h
  have hP := pre_ok
  have hD := da_ok
  have hZ := daZ_ok
  have hM := mid_ok
  have hL := leaf_ok
  have hQ := post_ok
  simp only [preOk, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at hP
  simp only [daOk, Bool.and_eq_true, and_assoc] at hD
  simp only [daZOk, Bool.and_eq_true, and_assoc] at hZ
  simp only [midOk, Bool.and_eq_true, and_assoc] at hM
  simp only [leafOk, Bool.and_eq_true, and_assoc, List.all_eq_true, List.mem_range] at hL
  simp only [postOk, Bool.and_eq_true, and_assoc] at hQ
  obtain ⟨pflat, prc, prc6, prc7, prc42, pm40, pm41, pm42, pexp, pxl, psl, pbytes, pm67, pl3, ptags, pl4,
    pm335, pm336, pa338, pc337⟩ := hP
  obtain ⟨dflat, dver, dph⟩ := hD
  obtain ⟨zflat, zc362, zl362, zc363, zl363⟩ := hZ
  obtain ⟨mflat, mm381, ml381, ml5, mm385, ml386, meq, mrc, ma395, ma397, mc396,
    mm398, mc399, mae, mm400, mm401, ma404, mc403⟩ := hM
  obtain ⟨lflat, lzero, l405, aflat, acall⟩ := hL
  obtain ⟨qflat, ql429, ql430, qsd, qc433, ql434, qe1, qc435, qc436, qm437, ql438, qe2⟩ := hQ
  -- the blocks
  obtain ⟨hpre, h⟩ := holdsList_flat mPre (List.all_eq_true.mpr pflat) _ _ h
  simp only [Stmt.HoldsList] at h
  rw [holds_ite_noRet _ _ _ noRet_mDa noRet_mDaZ] at h
  obtain ⟨⟨-, hdz, hdn⟩, h⟩ := h
  obtain ⟨hmid, h⟩ := holdsList_flat mMid mflat _ _ h
  rw [holds_ite_noRet _ _ _ noRet_mLeaf noRet_mAgg] at h
  obtain ⟨⟨-, hlz, hln⟩, h⟩ := h
  obtain ⟨hpost, -⟩ := holdsList_flat mPost qflat _ _ h
  have atP := atoms_of_flat hpre
  have atM := atoms_of_flat hmid
  have atQ := atoms_of_flat hpost
  -- the counts
  have hc : ∀ v < 6, ∃ e ≤ 65535, σ (.n v) = gen ^ e :=
    fun v hv => rcConst_sound hm (by norm_num) word_gmax (prc v hv) atP
  have hcl : ∀ v < 6, σ (.n v) = gen ^ lg σ v ∧ lg σ v ≤ 65535 := fun v hv => by
    obtain ⟨e, he, hv'⟩ := hc v hv
    obtain ⟨h1, h2⟩ := pow_lg (by omega) hv'
    exact ⟨h1, by omega⟩
  obtain ⟨e6, he6, h6⟩ := rcConst_sound hm (by norm_num) word_g16 prc6 atP
  obtain ⟨e7, he7, h7⟩ := rcConst_sound hm (by norm_num) word_g1 prc7 atP
  obtain ⟨e42, he42, h42⟩ := rcConst_sound hm (by norm_num) word_gmax prc42 atP
  obtain ⟨l6, r6⟩ := pow_lg (by omega) h6
  obtain ⟨l7, r7⟩ := pow_lg (by omega) h7
  obtain ⟨c0, b0⟩ := hcl 0 (by omega)
  obtain ⟨c1, b1⟩ := hcl 1 (by omega)
  obtain ⟨c2, b2⟩ := hcl 2 (by omega)
  obtain ⟨c3, b3⟩ := hcl 3 (by omega)
  obtain ⟨c4, b4⟩ := hcl 4 (by omega)
  obtain ⟨c5, b5⟩ := hcl 5 (by omega)
  have h40 : σ (.n 40) = gen ^ (lg σ 0 + lg σ 1) := by rw [isMul_sound pm40 atP, c0, c1, pow_add]
  have h41 : σ (.n 41) = gen ^ (lg σ 3 + lg σ 4) := by rw [isMul_sound pm41 atP, c3, c4, pow_add]
  have h42' : σ (.n 42) = gen ^ (lg σ 0 + lg σ 1 + (lg σ 3 + lg σ 4)) := by
    rw [isMul_sound pm42 atP, h40, h41, ← pow_add]
  have hT := gen_pow_inj34 (by omega) (by omega) (h42.symm.trans h42')
  have h336 : σ (.n 387) = σ (.n 385) * gen ^ (2 * lg σ 6) := by
    rw [isMul_sound pm336 atP, isMul_sound pm335 atP, l6, ← pow_add, two_mul]
  -- the pick
  obtain ⟨p, hp, hbl⟩ := rcDir_sound hm mrc atM
  have h389 : σ (.n 6) * gen = gen ^ (lg σ 6 + 1) := by
    rw [l6, pow_succ]
  have hplt := belowLog_lt (by omega) h389 hbl
  obtain ⟨lp, rp⟩ := pow_lg (by omega) hp
  -- the loops
  have hguard3 := guard_soundC pl3 hpre
  have hguard4 := guard_soundC pl4 hpre
  have h67 : σ (.n 67) = σ (.n 66) * σ (.n 40) := isMul_sound pm67 atP
  refine ⟨fun v hv => ?_, ⟨l6, by omega⟩, ⟨l7, by omega⟩, h40, h41, ⟨h42', by omega⟩, ?_, ?_, ?_,
    ?_, h67, ?_, ?_, ?_, h336, ?_, ?_, ?_, ?_, ?_, ⟨lp, by omega, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hcl _ (by omega)
  · -- the exponent tables
    have := hle _ _ _ (call_of_flat hpre pexp)
    exact (hexp rd _ _).mp this
  · obtain ⟨n, hn, hng, hout⟩ :=
      claim_list_digest_sound rd hm _ _ (hle _ _ _ (call_of_flat hpre pxl))
    rw [c0] at hng
    have hn' : n < 8912896 := hn
    have := gen_pow_inj34 (by omega) (by omega) hng
    rwa [this]
  · obtain ⟨n, hn, hng, hout⟩ :=
      claim_list_digest_sound rd hm _ _ (hle _ _ _ (call_of_flat hpre psl))
    rw [c3] at hng
    have hn' : n < 8912896 := hn
    have := gen_pow_inj34 (by omega) (by omega) hng
    rwa [this]
  · intro v hv
    obtain ⟨hcv, hlv⟩ := pbytes v hv
    have := load_sound hlv atP
    rwa [const_sound hcv atP] at this
  · -- raw leanXMSS
    refine loop_soundC (f := "__loop2") (ps := l2Args σ)
      (N := σ (.n 2)) (B := fun x => C "__loop2" (x :: l2Args σ) [] ∧
        ∃ s, BelowLog (σ (.n 40)) s ∧ LoadHolds rd (σ (.n 66)) s x)
      (by unfold ordG; omega) c2 (fun x hx => ?_)
      (fun hne => by simpa [l2Args, lxTagsV, Function.comp_def] using hguard3 hne)
    obtain ⟨h1, h2⟩ := l3_stepC hX hx
    obtain ⟨sig, hout⟩ := hX _ hx
    obtain ⟨s, hbl, hl, -⟩ := rawX_of_out hm hout _ _ _ _ _ rfl
    exact ⟨⟨h1, s, hbl, hl⟩, h2⟩
  · -- the carried tags
    intro i hi hc
    obtain ⟨h1, h2⟩ := Sig.lxTagSlot_spec i hi hc
    have pt := ptags i hi
    simp only [hc, Bool.not_true, Bool.false_or] at pt
    have e := const_sound pt atP
    rw [word_eOfNat] at e
    show (l2Args σ).getD (4 + (Sig.lxTagSlot i - 1)) 0 = _
    rw [← e, l2Args, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, List.getElem?_map]
    rw [List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 2
    omega
  · -- raw leanSPHINCS
    refine loop_soundC (f := "__loop3")
      (ps := [σ (.n 5), σ (.n 41), σ (.n 67), σ (.n 2), σ (.n 55), σ (.n 68)])
      (N := σ (.n 5))
      (B := RawSStepC C rd (σ (.n 41)) (σ (.n 66)) (σ (.n 40)) (σ (.n 2)) (σ (.n 55)) (σ (.n 68)))
      (by unfold ordG; omega) c5 (fun x hx => ?_) (fun hne => by simpa using hguard4 hne)
    obtain ⟨h1, h2⟩ := l4_stepC hC hm hx
    exact ⟨h1 _ _ _ _ _ _ _ (by rw [h67]), h2⟩
  · -- the direct DA check
    intro h71
    have h338 : σ (.n 389) = 0 := by
      rw [add_sound pa338 atP, const_sound pc337 atP, word_gen, l7, h71, pow_one, e_add_self]
    obtain ⟨hdall, -⟩ := holdsList_flat mDa dflat _ _ (hdz h338)
    have atD := atoms_of_flat hdall
    obtain ⟨hcan, h0, h1⟩ := pairHash_sound dph atD
    exact ⟨call_of_flat hdall dver, hcan, h0, h1⟩
  · -- no direct DA check: zeros
    intro h70
    have h338 : σ (.n 389) ≠ 0 := by
      rw [add_sound pa338 atP, const_sound pc337 atP, word_gen, l7, h70, pow_zero, add_comm]
      exact gen_add_one_ne
    obtain ⟨hzall, -⟩ := holdsList_flat mDaZ zflat _ _ (hdn h338)
    have atZ := atoms_of_flat hzall
    have z0 := load_sound zl362 atZ
    have z1 := load_sound zl363 atZ
    rw [const_sound zc362 atZ, word_zero] at z0
    rw [const_sound zc363 atZ, word_zero] at z1
    exact ⟨z0, z1⟩
  · have := load_sound ml381 atM
    rwa [isMul_sound mm381 atM, c2, c5, ← pow_add] at this
  · -- the children
    have hguard5 := guard_soundC ml5 hmid
    refine loop_soundC (f := "__loop4")
      (ps := [σ (.n 6), σ (.n 420), σ (.n 52), σ (.n 66), σ (.n 40), σ (.n 55), σ (.n 67),
        σ (.n 41), σ (.n 417), σ (.n 385), σ (.n 47), σ (.n 48), σ (.n 405), σ (.n 49),
        σ (.n 411)])
      (N := σ (.n 6)) (by unfold ordG; omega) l6 (fun x hx => ?_)
      (fun hne => by simpa using hguard5 hne)
    obtain ⟨h1, h2⟩ := l5_stepC hC hle hm hx
    exact ⟨h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl, h2⟩
  · have := load_sound ml386 atM
    rw [isMul_sound mm385 atM, l6, assertEq_sound meq atM] at this
    have := (loadHolds_mul_gen_pow rd _ (lg σ 6) 0 _).mp this
    simpa using this
  · -- with a direct DA check, the node's own slot
    intro h71
    have h398 : σ (.n 434) = 0 := by
      rw [assertEq_sound mae atM, const_sound mc399 atM, word_zero]
    rw [isMul_sound mm398 atM, add_sound ma395 atM, add_sound ma397 atM, const_sound mc396 atM,
      word_one, l7, h71, pow_one] at h398
    rcases mul_eq_zero.mp h398 with h0 | h0
    · rw [hp, l6] at h0
      exact gen_pow_inj34 (by omega) (by omega) (e_add_eq_zero_iff.mp h0) |>.trans rfl |>.symm.trans
        (by rw [rp]) |>.symm
    · exact absurd h0 gen_add_one_ne
  · rw [isMul_sound mm401 atM, isMul_sound mm400 atM, lp, ← pow_add, two_mul]
  · intro h60 k hk
    have h404 : σ (.n 440) = 0 := by
      rw [add_sound ma404 atM, const_sound mc403 atM, word_one, l6, h60, pow_zero, e_add_self]
    obtain ⟨hlall, -⟩ := holdsList_flat mLeaf (List.all_eq_true.mpr lflat) _ _ (hlz h404)
    have atL := atoms_of_flat hlall
    obtain ⟨hz, hl⟩ := lzero k hk
    have := load_sound hl atL
    rwa [const_sound hz atL, word_zero] at this
  · intro h60
    have h404 : σ (.n 440) ≠ 0 := by
      rw [add_sound ma404 atM, const_sound mc403 atM, word_one, l6]
      intro he
      have h2 : gen ^ 0 = gen ^ lg σ 6 := (pow_zero gen).trans (e_add_eq_zero_iff.mp he).symm
      exact h60 (gen_pow_inj34 (by omega) (by omega) h2).symm
    obtain ⟨haall, -⟩ := holdsList_flat mAgg (List.all_eq_true.mpr aflat) _ _ (hln h404)
    exact call_of_flat haall acall
  · exact ⟨load_sound ql429 atQ, load_sound ql430 atQ⟩
  · exact hle _ _ _ (call_of_flat hpost qsd)
  · have l1 := load_sound ql434 atQ
    rw [const_sound qc433 atQ, word_one, assertEq_sound qe1 atQ] at l1
    have l2 := load_sound ql438 atQ
    rw [isMul_sound qm437 atQ, const_sound qc435 atQ, const_sound qc436 atQ, word_one, word_gen,
      one_mul, assertEq_sound qe2 atQ] at l2
    refine ⟨l1, ?_⟩
    have l2' : LoadHolds rd (1 * gen ^ 1) 0 (σ (.n 468)) := by rwa [one_mul, pow_one]
    have := (loadHolds_mul_gen_pow rd 1 1 0 _).mp l2'
    simpa using this

end
end LeanVM.Guest.B1.Main
