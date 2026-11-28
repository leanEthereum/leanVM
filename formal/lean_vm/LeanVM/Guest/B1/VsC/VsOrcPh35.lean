/-
  LeanVM.Guest.B1.VsC.VsOrcPh35

  `Ph35Hyp` at the honest oracle: `verify_keccak`, the ring's run, `ring_switch_target`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh1213
public import LeanVM.Guest.B1.VerifySub.PhLinkSpine

/-!
# `Ph35` at the honest values

`Ph35In`: `Ph35Hyp`'s facts but the two calls, and for them: `verify_keccak`'s native run (`RunsTo (verifyKeccak τ …)`
from the packed message's returns `w 1288 … w 1292` over the stream words `xs` past the packed message, the Keccak
claim `⟨qkeccak, op, kw⟩`, the point and the slices), its arrays' cells and reads, its returns `w 2915 … w 2921`
as `ret`'s constants; `ring_switch_target`'s return `w 3810` as `ret`'s constant, the ring target of the
three buffers' words. **`ph35Ok_in`**: `Ph35Ok` from it, the callees from `VerifyKeccakCompleteA` and
`RingSwitchTargetCompleteA`, their regions narrowed to the indices.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **`Ph35`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph35In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (qt b15 b20 b21 bm cs τ : ℕ) (nz : E) (xs21 xsm : List E)
    (chis outs xs op point slices : List E) (kw : E) (s' : Fs) : Prop where
  h120 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 120) = gen ^ τ
  h15 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 15) = ptrAt b15
  h20 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 20) = ptrAt b20
  h21 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 21) = ptrAt b21
  h4 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 4) = ptrAt qt
  hτ0 : keccakTauMin ≤ τ
  hτ1 : τ ≤ keccakTauMax
  hτc : τ ≤ chis.length
  houts : outs.length = 25
  hcar : ∃ sp, (⟨[vsW rd1 args cur p ret 1288, vsW rd1 args cur p ret 1289, vsW rd1 args cur p ret 1290,
      vsW rd1 args cur p ret 1291, vsW rd1 args cur p ret 1292], []⟩ : Fs).Carries sp
  hrun : RunsTo (verifyKeccak τ (chis.take τ) outs)
    ⟨[vsW rd1 args cur p ret 1288, vsW rd1 args cur p ret 1289, vsW rd1 args cur p ret 1290,
      vsW rd1 args cur p ret 1291, vsW rd1 args cur p ret 1292], []⟩ xs ([⟨qkeccak, op, kw⟩], point, slices) s'
  hpend : s'.pend.length = rateScalars
  hsl : slices.length = 64
  rvk : ∀ j < 7, ∀ σ, ret (2915 + j) σ = (vkRets s' (ptrAt (bm + 144)) xs.length kw).getD j 0
  hfv : ∀ q ∈ vkIdx bm b15 b20 b21 qt xs.length chis.length op.length point.length, q.1 + q.2 ≤ st.kc
  hcv : ∀ q ∈ vkIdx bm b15 b20 b21 qt xs.length chis.length op.length point.length, ∀ t < q.2,
    (R (q.1 + t) ∨ Own (q.1 + t)) ∨ st.D (q.1 + t)
  hPk : ∀ rd, Pre rd ∧ st.O rd → WinTabs rd (ptrAt qt * word 365917469723852800 0) ∧ ReadsAt rd (ptrAt b15) chis ∧
    ReadsAt rd (ptrAt (bm + 55)) outs ∧ ReadsAt rd (ptrAt (bm + 144)) xs ∧ ReadsAt rd (ptrAt b20) op ∧
    ReadsAt rd (ptrAt (b20 + qkeccakVarsCap)) point ∧ ReadsAt rd (ptrAt b21) slices
  hw2920 : vsW rd1 args cur p ret 2920 = ptrAt cs
  r0cs : ReadsAt rd0 (ptrAt cs) [nz]
  hOcs : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt cs) [nz]
  hOwncs : Own cs
  hl0 : LowDef k rd0
  rt : ExpWinTab rd0 (ptrAt qt)
  hPt : ∀ rd, Pre rd → ExpWinTab rd (ptrAt qt)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hwin : ∀ j ≤ gcW 13, vsW rd1 args cur p ret (2943 + j) =
    gcWin 13 (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2931)) j
  hlow : ((vsVal rd0 (vsW rd1 args cur p ret) args (.n 2931)).limb 0).lane.toNat % 2 ^ 13 = 0
  hw3039 : vsW rd1 args cur p ret 3039 = ptrAt st.a
  hw3040 : vsW rd1 args cur p ret 3040 = ptrAt (st.a + 16)
  hw3553 : vsW rd1 args cur p ret 3553 = ptrAt (st.a + 80)
  hOwn : ∀ j < 144, Own (st.a + j)
  hak : st.a + 144 ≤ st.kc
  r39 : ReadsAt rd0 (ptrAt st.a) (mcW (vsVal rd0 (vsW rd1 args cur p ret) args))
  hO39 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt st.a) (mcW (vsVal rd0 (vsW rd1 args cur p ret) args))
  r40 : ReadsAt rd0 (ptrAt (st.a + 16)) (mcRc (vsVal rd0 (vsW rd1 args cur p ret) args))
  hO40 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt (st.a + 16)) (mcRc (vsVal rd0 (vsW rd1 args cur p ret) args))
  hl21 : 64 ≤ xs21.length
  r21 : ReadsAt rd0 (ptrAt b21) xs21
  hO21 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b21) xs21
  hOwn21 : ∀ j < 64, Own (b21 + j)
  hwm : vsW rd1 args cur p ret 1076 = ptrAt bm
  hlm : 144 ≤ xsm.length
  rm : ReadsAt rd0 (ptrAt bm) xsm
  hOm : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt bm) xsm
  hcm : ∀ j < 144, (R (bm + j) ∨ Own (bm + j)) ∨ st.D (bm + j)
  r53 : ReadsAt rd0 (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3026)))
  hO53 : ∀ rd, Pre rd → st.O rd →
    ReadsAt rd (ptrAt (st.a + 80)) (rsW xs21 xsm (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3026)))
  r3810 : ∀ σ, ret 3810 σ = ringTarget (rsW xs21 xsm (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3026)))
    ((mcW (vsVal rd0 (vsW rd1 args cur p ret) args)).take 8) ((mcW (vsVal rd0 (vsW rd1 args cur p ret) args)).drop 8)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

theorem word_g55 : word 36028797018963968 0 = gen ^ 55 := by
  rw [show (36028797018963968 : ℕ) = 2 ^ 55 by norm_num, word_two_pow (by decide)]

theorem vkIdx_ptr (bm b15 b20 b21 qt : ℕ) (xs chis op point : List E) :
    vkArrays (ptrAt bm * word 21299200 0) (ptrAt b15) (ptrAt bm * word 36028797018963968 0) (ptrAt b20)
      (ptrAt b21) (ptrAt qt * word 365917469723852800 0) xs chis op point =
      (vkIdx bm b15 b20 b21 qt xs.length chis.length op.length point.length).map fun q => (ptrAt q.1, q.2) := by
  simp only [vkArrays, vkIdx, List.map, word_g144, word_g55, word_g178', ptrAt_mul_pow]

/-- `verify_keccak`'s arrays as index arrays, the stream's cursor `w 1076 = ptrAt bm`. -/
theorem vkArrays_ptr' {w : ℕ → E} {bm : ℕ} (hwm : w 1076 = ptrAt bm) (b15 b20 b21 qt : ℕ) (xs chis op point : List E) :
    vkArrays (w 1076 * word 21299200 0) (ptrAt b15) (w 1076 * word 36028797018963968 0) (ptrAt b20)
      (ptrAt b21) (ptrAt qt * word 365917469723852800 0) xs chis op point =
      (vkIdx bm b15 b20 b21 qt xs.length chis.length op.length point.length).map fun q => (ptrAt q.1, q.2) := by
  rw [hwm]; exact vkIdx_ptr bm b15 b20 b21 qt xs chis op point

/-- **`Ph35` at the honest values, at given ends**: `Ph35Ok` from `Ph35In` and the two calls at the ends `ev`, `er`,
the continuation at `er`. -/
theorem ph35Ok_at
    (ha : args.length = 6) (hr : CausalRule ret) {st : St} {K : St → Prop}
    {qt b15 b20 b21 bm cs τ : ℕ} {nz : E} {xs21 xsm : List E} {chis outs xs op point slices : List E} {kw : E}
    {s' : Fs}
    (H : Ph35In fs al cert k rd0 rd1 args cur p ret Own R Pre st qt b15 b20 b21 bm cs τ nz xs21 xsm chis outs xs
      op point slices kw s')
    {ev er : ℕ}
    (hv : VkCall fs al cert k (vsW rd1 args cur p ret) b15 b20 b21 qt τ chis outs xs op point slices kw s'
      (allocBase (al "verify_keccak") st.kc) ev)
    (hrt : RtCall fs al cert k st.a (rsW xs21 xsm (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3026)))
      (mcW (vsVal rd0 (vsW rd1 args cur p ret) args)) (allocBase (al "ring_switch_target") ev) er)
    (hK : K ⟨st.a + 144, er, fun rd => (st.O rd ∧ True) ∧ True, fun i => (st.D i ∨ False) ∨ False,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    Ph35Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  unfold VkCall at hv
  rw [vkArrays_ptr' H.hwm] at hv
  have hv := CallAtA.idxR hv
  have hrets : vkRets s' (vsW rd1 args cur p ret 1076 * word 21299200 0) xs.length kw =
      [vsW rd1 args cur p ret 2915, vsW rd1 args cur p ret 2916, vsW rd1 args cur p ret 2917,
        vsW rd1 args cur p ret 2918, vsW rd1 args cur p ret 2919, vsW rd1 args cur p ret 2920,
        vsW rd1 args cur p ret 2921] := by
    have hl : (vkRets s' (ptrAt (bm + 144)) xs.length kw).length = 7 := rfl
    have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 2915)
      (cs := vkRets s' (ptrAt (bm + 144)) xs.length kw)
      (fun j hj => by rw [hl] at hj; interval_cases j <;> decide)
      (fun j hj σ => H.rvk j (by rw [hl] at hj; exact hj) σ)
    rw [H.hwm, word_g144, ptrAt_mul_pow, ← e, hl]; rfl
  have hrets' : capOf s'.perm ++ [vsW rd1 args cur p ret 1076 * word 21299200 0 * gen ^ xs.length, kw] =
      [vsW rd1 args cur p ret 2915, vsW rd1 args cur p ret 2916, vsW rd1 args cur p ret 2917,
        vsW rd1 args cur p ret 2918, vsW rd1 args cur p ret 2919, vsW rd1 args cur p ret 2920,
        vsW rd1 args cur p ret 2921] := hrets
  rw [hrets'] at hv
  unfold RtCall at hrt
  have e : [(ptrAt (st.a + 80), kBits), (ptrAt st.a, 2 * ringMapWidth)] =
      [(st.a + 80, 64), (st.a, 16)].map fun q => (ptrAt q.1, q.2) := rfl
  rw [e] at hrt
  have hrt := CallAtA.idxR hrt
  have hrt := CallAtA.ret1 hrt (vsW_retC (rd1 := rd1) (cur := cur) (p := p) ha hr (i := 3810) (by decide) H.r3810)
  refine ⟨qt, b15, b20, b21, bm, cs, τ, nz, xs21, xsm, _, _, _, _, _, _, ev, _, _, _, _, _, _, er,
    ⟨H.h120, H.h15, H.h20, H.h21, H.h4, hv, ?_, ?_, H.hw2920, H.r0cs, H.hOcs, H.hOwncs, H.hl0, H.rt, H.hPt, H.hRq,
    H.hwin, H.hlow, H.hw3039, H.hw3040, H.hw3553, H.hOwn, H.r39, H.hO39, H.r40, H.hO40, H.hl21, H.r21, H.hO21,
    H.hOwn21, H.hwm, H.hlm, H.rm, H.hOm, H.hcm, H.r53, H.hO53, hrt, ?_, ?_⟩, hK⟩
  · rintro i ⟨q, hq, t, ht, rfl⟩
    exact H.hcv q hq t ht
  · intro rd hrd
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H.hPk rd hrd
    refine ⟨h1, h2, ?_, ?_, h5, ?_, h7⟩
    · rw [H.hwm, word_g55, ptrAt_mul_pow]; exact h3
    · rw [H.hwm, word_g144, ptrAt_mul_pow]; exact h4
    · rw [ptrAt_mul_pow]; exact h6
  · rintro i ⟨q, hq, t, ht, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · refine Or.inl (Or.inr ?_)
      show Own (st.a + 80 + t)
      rw [Nat.add_assoc]; exact H.hOwn _ (by simp only at ht; omega)
    · exact Or.inl (Or.inr (H.hOwn _ (by simp only at ht; omega)))
  · intro rd ⟨hp, ho, _⟩
    exact ⟨H.hO53 rd hp ho, H.hO39 rd hp ho⟩


/-- **`Ph35` at the honest values**: `Ph35Ok` from `Ph35In`, `verify_keccak` and `ring_switch_target` from
their completeness. -/
theorem ph35Ok_in (hV : VerifyKeccakCompleteA fs al cert k) (hRT : RingSwitchTargetCompleteA fs al cert k)
    (ha : args.length = 6) (hr : CausalRule ret) {st : St} {K : St → Prop}
    {qt b15 b20 b21 bm cs τ : ℕ} {nz : E} {xs21 xsm : List E} {chis outs xs op point slices : List E} {kw : E}
    {s' : Fs}
    (H : Ph35In fs al cert k rd0 rd1 args cur p ret Own R Pre st qt b15 b20 b21 bm cs τ nz xs21 xsm chis outs xs
      op point slices kw s')
    (hK : ∀ er : ℕ, st.kc ≤ er → K ⟨st.a + 144, er, fun rd => (st.O rd ∧ True) ∧ True, fun i => (st.D i ∨ False) ∨ False,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    Ph35Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have harr := vkIdx_ptr bm b15 b20 b21 qt xs chis op point
  rw [← H.hwm] at harr
  obtain ⟨ev, hv⟩ := hV (vsW rd1 args cur p ret 1288) (vsW rd1 args cur p ret 1289) (vsW rd1 args cur p ret 1290)
    (vsW rd1 args cur p ret 1291) (vsW rd1 args cur p ret 1292) (vsW rd1 args cur p ret 1076 * word 21299200 0)
    (ptrAt b15) (vsW rd1 args cur p ret 1076 * word 36028797018963968 0) (ptrAt b20) (ptrAt b21)
    (ptrAt qt * word 365917469723852800 0) τ chis outs xs op point slices kw s'
    (allocBase (al "verify_keccak") st.kc) H.hτ0 H.hτ1 H.hτc H.houts H.hcar H.hrun H.hpend H.hsl
    (by rw [harr]; exact ptrsBelow_idx fun q hq => le_trans (H.hfv q hq) (le_allocBase _ _))
  obtain ⟨_, _, hce, _⟩ := id hv
  obtain ⟨er, hrt⟩ := hRT (ptrAt (st.a + 80)) (ptrAt st.a)
    (rsW xs21 xsm (vsVal rd0 (vsW rd1 args cur p ret) args (.n 3026))) (mcW (vsVal rd0 (vsW rd1 args cur p ret) args))
    (allocBase (al "ring_switch_target") ev) (rsW_length _ _ _) rfl
    (by
      have e : [(ptrAt (st.a + 80), kBits), (ptrAt st.a, 2 * ringMapWidth)] =
          [(st.a + 80, 64), (st.a, 16)].map fun q => (ptrAt q.1, q.2) := rfl
      rw [e]
      refine ptrsBelow_idx fun q hq => ?_
      have := le_allocBase (al "verify_keccak") st.kc
      have := le_allocBase (al "ring_switch_target") ev
      have := H.hak
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp only <;> omega)
  obtain ⟨_, _, hre, _⟩ := id hrt
  exact ph35Ok_at ha hr H hv hrt (hK er (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) (le_trans hce
    (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hre))))))
end

end
end LeanVM.Guest.B1.VsC
