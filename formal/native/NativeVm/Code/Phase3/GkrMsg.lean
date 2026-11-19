module

public import NativeVm.Code.Phase3.GkrComb

/-!
# A sumcheck round's parts

`msgC_spec`: the round's tail read at `gTail`, the message's head `claim + e · Σ tail` at `gMsg`.
`nextC_spec`: the claim `polyEval message c`, the challenge `c` at the coordinate's place, the
round's index and count stepped.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- Code with no transcript step, then a part's run. -/
theorem Step3.pre {r : List Reg64} {w ws : List Region} {s1 s2 : QState} (hw : Wrote env [] s s1)
    (h : Step3 env r w s1 s2) (hw2 : ∀ q ∈ w, q ∈ ws) : Step3 env allRegs ws s s2 :=
  hw.step.gtrans h (by simp) hw2

theorem msg_head (claim e x : EW) : x * e + claim = claim + e * x := by
  rw [← NativeVm.Equiv.EW.toE_inj]
  simp only [NativeVm.Equiv.EW.toE_add, NativeVm.Equiv.EW.toE_mul]
  ring

theorem natAt_le4 {n : Nat} (h : n ≤ 4) : n < 2 ^ 64 := by omega

/-- **A round's message.** -/
theorem msgC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {N j : Nat} {e claim : EW}
    (hN : NatAt s.mem (wd env.work gN) N) (hN4 : N ≤ 4) (hj : j < 64)
    (hpi : NatAt s.mem (wd env.work gPI) (2 * j)) (he : EWAt s.mem (wd env.work (gP + 2 * j)) e)
    (hc : EWAt s.mem (wd env.work gClaim) claim) (ho : EWArr s.mem (wd env.work gOnes) gones4) :
    WP msgC s (fun s' ↦ ∃ tail t', (readScalars N).run t = some (tail, t') ∧ CodeRel env t' s' ∧
      tail.size = N ∧ EWArr s'.mem (wd env.work gTail) tail ∧
      EWAt s'.mem (wd env.work gMsg) (claim + e * sumE tail) ∧
      Step3 env allRegs [gTailR, gMsgR] s s')
      (fun s' ↦ (readScalars N).run t = none ∧ Step3 env allRegs [gTailR, gMsgR] s s') := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold msgC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (v := N.toUInt64) (by rsimp) hN.2 ?_
  refine WP.then (WP.mono (readsTo_spec (r := gTailR) (by gok3) (by gomega) (by gomega)
      ((h.setReg3 (by decide) _).setReg3 (by decide) _) hi (by rsimp))
    (fun _ h ↦ h) (fun s2 ⟨hn, hst⟩ ↦ ⟨hn, Step3.pre (by gwrote hi) hst (by simp)⟩))
    fun s1 ⟨tail, t1, hrun, h1, hsz, htail, hst⟩ ↦ ?_
  have hst1 : Step3 env allRegs [gTailR] s s1 := Step3.pre (by gwrote hi) hst (by simp)
  have hi1 := hi.step3 (by gok3_tac) hst1 hrdi
  have hr1 : s1.reg .rdi = env.ctx := hst1.rdi.trans hrdi
  have hwp1 : s1.mem (wd env.ctx ctxWork) = some env.work := h1.workPtr3
  have hN1 := NatAt.gkeep hN (by gsame hst1, hi)
  have ho1 : EWArr s1.mem (wd env.work gOnes) gones4 := ho.congr (n := 8) (by gsame hst1, hi) (by decide)
  have hpi1 := NatAt.gkeep hpi (by gsame hst1, hi)
  have he1 : EWAt s1.mem (wd env.work (gP + 2 * j)) e := he.congr (by gsame hst1, hi)
  have hc1 : EWAt s1.mem (wd env.work gClaim) claim := hc.congr (by gsame hst1, hi)
  refine gwp_ldc hr1 hwp1 ?_
  fstep
  refine gwp_ldw (env := env) (v := N.toUInt64) (by rsimp) hN1.2 ?_
  fstep [add_wdisp]; fstep [add_wdisp]
  refine WP.then (edot_sum (xs := tail) (by rsimp; exact htail) (by rsimp; exact ho1) (by omega)
    (by rsimp; rw [hsz])) fun s2 ⟨h9, h10, hm2, hf2⟩ ↦ ?_
  have hw2 : Wrote env [gMsgR] s1 s2 := Wrote.kern (by gwrote hi1) hm2 hf2
  have hr2 : s2.reg .rdi = env.ctx := hw2.rdi.trans hr1
  have hmem2 : ∀ k, s2.mem k = s1.mem k := fun k ↦ by rw [hm2]; rfl
  refine gwp_ldc hr2 (by rw [hmem2]; exact hwp1) ?_
  refine gwp_ldw (env := env) (v := (2 * j).toUInt64) (by rsimp) (by rsimp; rw [hmem2]; exact hpi1.2) ?_
  refine gwp_ldx (env := env) (i := 2 * j) (v := e.c0) (by rsimp) (by rsimp) ?_ ?_
  · rsimp; rw [hmem2, Nat.add_comm]; exact EWAt.gw0 he1
  refine gwp_ldx (env := env) (i := 2 * j) (v := e.c1) (by rsimp) (by rsimp) ?_ ?_
  · rsimp; rw [hmem2, show 2 * j + (gP + 1) = gP + 2 * j + 1 by omega]; exact EWAt.gw1 he1
  refine WP.then (emul_ew (a := sumE tail) (b := e) (by rsimp; exact h9) (by rsimp; exact h10)
    (by rsimp) (by rsimp)) fun s3 ⟨h9', h10', hm3, hf3⟩ ↦ ?_
  have hw3 : Wrote env [gMsgR] s1 s3 := Wrote.kern (by gwrote hi1) hm3 hf3
  have hr3 : s3.reg .rdi = env.ctx := hw3.rdi.trans hr1
  have hmem3 : ∀ k, (hk : k < 85438) → GApart k 1 [gMsgR] →
      s3.mem (wd env.work k) = s1.mem (wd env.work k) :=
    fun k hk hap ↦ hw3.out (by gok3_tac) hk hap
  refine gwp_ldc hr3 (by rw [hw3.ctxw hi1 (by gok3_tac)]; exact hwp1) ?_
  refine gwp_ldw (env := env) (v := claim.c0) (by rsimp) ?_ ?_
  · rsimp; rw [hmem3 gClaim (by gomega) (by gap_tac)]; exact EWAt.gw0 hc1
  fstep
  refine gwp_ldw (env := env) (v := claim.c1) (by rsimp) ?_ ?_
  · rsimp; rw [hmem3 (gClaim + 1) (by gomega) (by gap_tac)]; exact EWAt.gw1 hc1
  fstep
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi1
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi1
  refine wp_done_gen fun s4 hs4 ↦ ?_
  have hw4 : Wrote env [gMsgR] s1 s4 := by subst hs4; gwrote hi1
  refine ⟨tail, t1, hrun, h1.wrote3 hi1 (by gok3_tac) hw4, hsz, htail.congr (n := 8)
    (by gsamew hw4, hi1) (by omega), ⟨?_, ?_⟩, hst1.gtrans hw4.step (by simp) (by simp)⟩
  · subst hs4; gmem; simp only [h9', ← msg_head]; rfl
  · subst hs4; rw [wd_wd]; gmem; simp only [h10', ← msg_head]; rfl

theorem add_two_word (n : Nat) : (2 * n).toUInt64 + 2 = (2 * (n + 1)).toUInt64 := by
  rw [show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toUInt64_add]; congr 1

/-- **A round's end.** -/
theorem nextC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {N j cnt : Nat} {c : EW}
    {msg : Array EW} (hch : EWAt s.mem (wd env.work gChal) c)
    (hN : NatAt s.mem (wd env.work gN) N) (hN4 : N ≤ 4)
    (hmsg : EWArr s.mem (wd env.work gMsg) msg) (hms : msg.size = N + 1) (hj : j < 64)
    (hpi : NatAt s.mem (wd env.work gPI) (2 * j)) (hcnt : NatAt s.mem (wd env.work gCnt) (cnt + 1))
    (hc64 : cnt < 64) :
    WP nextC s (fun s' ↦ EWAt s'.mem (wd env.work gClaim) (polyEval msg c) ∧
      EWAt s'.mem (wd env.work (gP + 2 * j)) c ∧ NatAt s'.mem (wd env.work gPI) (2 * (j + 1)) ∧
      NatAt s'.mem (wd env.work gCnt) cnt ∧ s'.reg .r14 = cnt.toUInt64 ∧
      Wrote env [gClaimR, gRoundR, gPtR j 1] s s')
      (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold nextC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (v := c.c0) (by rsimp) (EWAt.gw0 hch) ?_
  refine gwp_ldw (env := env) (v := c.c1) (by rsimp) (EWAt.gw1 hch) ?_
  refine gwp_ldw (env := env) (v := N.toUInt64) (by rsimp) hN.2 ?_
  fstep; fstep [add_wdisp]
  refine WP.then (epoly_ew (cs := msg) (b := c) (by rsimp; exact hmsg)
    (by rsimp; rw [hms, toUInt64_succ]) (by rsimp) (by rsimp) (by omega))
    fun s1 ⟨h9, h10, hm1, hf1⟩ ↦ ?_
  have hw1 : Wrote env [gClaimR, gRoundR, gPtR j 1] s s1 := Wrote.kern (by gwrote hi) hm1 hf1
  have hr1 : s1.reg .rdi = env.ctx := hw1.rdi.trans hrdi
  have h11 : s1.reg .r11 = c.c0 := by rw [hf1 .r11 (by decide)]; rsimp
  have h12 : s1.reg .r12 = c.c1 := by rw [hf1 .r12 (by decide)]; rsimp
  have hmem1 : ∀ a, s1.mem a = s.mem a := fun a ↦ by rw [hm1]; rfl
  refine gwp_ldc hr1 (by rw [hw1.ctxw hi (by gok3_tac)]; exact hwp) ?_
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := (2 * j).toUInt64) (by rsimp) ?_ ?_
  · gmem; rw [hmem1]; exact hpi.2
  refine gwp_stx (env := env) (i := 2 * j) (by rsimp) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_stx (env := env) (i := 2 * j) (by rsimp) (by rsimp) ?_ ?_
  · gex hi
  fstep
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := (cnt + 1).toUInt64) (by rsimp) ?_ ?_
  · gmem; rw [hmem1]; exact hcnt.2
  fstep
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine wp_done_gen fun s2 hs2 ↦ ?_
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ?_, ?_⟩ <;> subst hs2
  · gmem; rw [h9]
  · rw [wd_wd]; gmem; rw [h10]
  · rw [Nat.add_comm]; gmem; rw [h11]
  · rw [wd_wd, show gP + 2 * j + 1 = 2 * j + (gP + 1) by omega]; gmem; rw [h12]
  · gmem; rw [add_two_word]
  · gmem; rw [Field.toUInt64_succ_sub]
  · rsimp; rw [Field.toUInt64_succ_sub]
  · gwrote hi

end NativeVm.Code.P3
