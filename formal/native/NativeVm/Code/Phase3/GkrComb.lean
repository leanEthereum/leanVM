module

public import NativeVm.Code.Phase3.GkrCode
public import NativeVm.Code.Phase3.GkrKern

/-!
# A step's start: `step`, the combiner, the claim

`setStepC_spec`: `step = gkrStepOf rem` at `gStep`, `2^step` at `gN`. `combC_spec`: the combiner
sampled, the claim `polyEval values comb`, the rounds' index `2 rem` and count `depth - rem`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

theorem step_word {rem : Nat} (h : rem < 2 ^ 64) :
    2 - (rem.toUInt64 &&& 1) = (gkrStepOf rem).toUInt64 := by
  have e := toNat_and_one rem.toUInt64
  rw [Field.toNat_toUInt64 h] at e
  unfold gkrStepOf
  apply UInt64.toNat_inj.mp
  split
  · rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, e]; simp; omega), e]
    simp; omega
  · rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, e]; simp; omega), e]
    simp; omega

theorem two_step_word (rem : Nat) :
    (gkrStepOf rem).toUInt64 + (gkrStepOf rem).toUInt64 = (2 ^ gkrStepOf rem).toUInt64 := by
  rcases gkrStepOf_cases rem with h | h <;> rw [h] <;> rfl

/-- **`step` and `2^step`.** -/
theorem setStepC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {rem : Nat}
    (hrem : NatAt s.mem (wd env.work gRem) rem) :
    WP setStepC s (fun s' ↦ NatAt s'.mem (wd env.work gStep) (gkrStepOf rem) ∧
      NatAt s'.mem (wd env.work gN) (2 ^ gkrStepOf rem) ∧ Wrote env [gStepR] s s')
      (fun _ ↦ False) := by
  have hrdi := h.rdi
  unfold setStepC
  refine gwp_ldc hrdi h.workPtr3 ?_
  refine gwp_ldw (env := env) (by rsimp) hrem.2 ?_
  fstep; fstep; fstep
  refine gwp_stw (env := env) (by rsimp) (gsome hi (by gomega) (by gomega)) ?_
  fstep
  refine gwp_stw (env := env) (by rsimp) (by gmem; exact gsome hi (by gomega) (by gomega)) ?_
  apply WP.blk_nil
  have hs : gkrStepOf rem < 2 ^ 64 := by rcases gkrStepOf_cases rem with e | e <;> rw [e] <;> omega
  refine ⟨⟨hs, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · gmem
    rw [step_word hrem.1]
  · rcases gkrStepOf_cases rem with e | e <;> rw [e] <;> omega
  · gmem
    rw [step_word hrem.1, two_step_word]
  · gwrote hi

theorem two_mul_word {n : Nat} : n.toUInt64 + n.toUInt64 = (2 * n).toUInt64 := by
  rw [toUInt64_add]; congr 1; omega

theorem sub_word {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  have h1 := Field.toNat_toUInt64 (a := a) ha
  have h2 := Field.toNat_toUInt64 (a := b) (by omega)
  have h3 := Field.toNat_toUInt64 (a := a - b) (by omega)
  have hle : b.toUInt64 ≤ a.toUInt64 := by rw [UInt64.le_iff_toNat_le, h1, h2]; exact h
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ hle, h1, h2, h3]

/-- **The claim**, the rounds' index and count. -/
theorem claimC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {comb : EW} {values : Array EW}
    {rem depth : Nat} (hc : EWAt s.mem (wd env.work gComb) comb)
    (hv : EWArr s.mem (wd env.work gTr) values) (hvs : values.size = 3)
    (hrem : NatAt s.mem (wd env.work gRem) rem) (hd : NatAt s.mem (wd env.work gD) depth)
    (hrd : rem ≤ depth) (hd64 : depth < 64) :
    WP claimC s (fun s' ↦ EWAt s'.mem (wd env.work gClaim) (polyEval values comb) ∧
      NatAt s'.mem (wd env.work gPI) (2 * rem) ∧ NatAt s'.mem (wd env.work gCnt) (depth - rem) ∧
      s'.reg .r14 = (depth - rem).toUInt64 ∧ Wrote env [gClaimR, gRoundR] s s')
      (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold claimC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (by rsimp) (EWAt.gw0 hc) ?_
  refine gwp_ldw (env := env) (by rsimp) (EWAt.gw1 hc) ?_
  fstep [add_wdisp]; fstep
  refine WP.then (epoly_ew (cs := values) (b := comb) (by rsimp; exact hv) (by rsimp; rw [hvs]; rfl)
    (by rsimp) (by rsimp) (by omega)) fun s1 ⟨h9, h10, hm, hf⟩ ↦ ?_
  have hw1 : Wrote env [gClaimR, gRoundR] s s1 := Wrote.kern (by gwrote hi) hm hf
  have hr1 : s1.reg .rdi = env.ctx := hw1.rdi.trans hrdi
  have hm1 : ∀ k, (hk : k < 85438) → GApart k 1 [gClaimR, gRoundR] → s1.mem (wd env.work k) = s.mem (wd env.work k) :=
    fun k hk hap ↦ hw1.out (by gok3_tac) hk hap
  refine gwp_ldc hr1 (by rw [hw1.ctxw hi (by gok3_tac)]; exact hwp) ?_
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := rem.toUInt64) (by rsimp) ?_ ?_
  · gmem; rw [hm1 gRem (by gomega) (by gap_tac)]; exact hrem.2
  fstep; fstep
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := depth.toUInt64) (by rsimp) ?_ ?_
  · gmem; rw [hm1 gD (by gomega) (by gap_tac)]; exact hd.2
  fstep
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  apply WP.blk_nil
  refine ⟨⟨?_, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ?_, ?_⟩
  · gmem; rw [h9]
  · rw [wd_wd]; gmem; rw [h10]
  · gmem; rw [two_mul_word]
  · gmem; rw [sub_word hrd (by omega)]
  · rsimp; rw [sub_word hrd (by omega)]
  · gwrote hi

/-- **The combiner and the claim.** -/
theorem combC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {values : Array EW}
    {rem depth : Nat} (hv : EWArr s.mem (wd env.work gTr) values) (hvs : values.size = 3)
    (hrem : NatAt s.mem (wd env.work gRem) rem) (hd : NatAt s.mem (wd env.work gD) depth)
    (hrd : rem ≤ depth) (hd64 : depth < 64) :
    WP combC s (fun s' ↦ ∃ comb t', Model.sampleChallenge.run t = some (comb, t') ∧
      CodeRel env t' s' ∧ EWAt s'.mem (wd env.work gComb) comb ∧
      EWAt s'.mem (wd env.work gClaim) (polyEval values comb) ∧
      NatAt s'.mem (wd env.work gPI) (2 * rem) ∧ NatAt s'.mem (wd env.work gCnt) (depth - rem) ∧
      s'.reg .r14 = (depth - rem).toUInt64 ∧ Step3 env allRegs [gCombR, gClaimR, gRoundR] s s')
      (fun _ ↦ False) := by
  unfold combC
  refine WP.then (sampleTo_spec (r := gCombR) (by gok3) (by gomega) (by gomega) h hi)
    fun s1 ⟨comb, t1, hrun, h1, hc, hst⟩ ↦ ?_
  have hi1 := hi.step3 (by gok3_tac) hst h.rdi
  refine WP.mono (claimC_spec h1 hi1 hc (hv.congr (n := 6) (by gsame hst, hi) (by omega)) hvs
    (NatAt.gkeep hrem (by gsame hst, hi)) (NatAt.gkeep hd (by gsame hst, hi)) hrd hd64)
    (fun s2 ⟨hcl, hpi, hcnt, h14, hw⟩ ↦ ⟨comb, t1, hrun, h1.wrote3 hi1 (by gok3_tac) hw,
      hc.congr (by gsamew hw, hi1), hcl, hpi, hcnt, h14, hst.gtrans hw.step (by simp) (by simp)⟩)
    (fun _ h ↦ h)

end NativeVm.Code.P3
