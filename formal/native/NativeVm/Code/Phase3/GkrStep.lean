module

public import NativeVm.Code.Phase3.GkrSumcheck
public import NativeVm.Code.Phase3.GkrY

/-!
# A step of the walk

`stepC_spec`: `stepC` from remaining depth `rem > 0` against `gkrStep (gkrStepOf rem) last`: the
trees' values at `treeR`, the point at `pointR` from element `rem - step`, `rem - step` at `gRem`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- The regions a step writes. -/
def stepWs : List Region := [pointR, treeR, gA, gB]

theorem EWArr.gappend {mem : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {xs ys : Array EW}
    (hx : EWArr mem (wd w a) xs) (hy : EWArr mem (wd w (a + 2 * xs.size)) ys) :
    EWArr mem (wd w a) (xs ++ ys) := by
  refine EWArr.gof fun i hi ↦ ?_
  rw [Array.size_append] at hi
  rw [Array.getElem_append]
  split
  · exact EWArr.gget hx (by omega)
  · have := EWArr.gget hy (i := i - xs.size) (by omega)
    rwa [show a + 2 * xs.size + 2 * (i - xs.size) = a + 2 * i by omega] at this

/-- **A step.** -/
theorem stepC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {rem depth : Nat}
    {st : GkrStateW} (last : Bool) (hrem0 : 0 < rem) (hrd : rem ≤ depth) (hd64 : depth < 64)
    (hrem : NatAt s.mem (wd env.work gRem) rem) (hd : NatAt s.mem (wd env.work gD) depth)
    (ho : EWArr s.mem (wd env.work gOnes) gones4) (hv : EWArr s.mem (wd env.work gTr) st.values)
    (hvs : st.values.size = 3) (hpt : EWArr s.mem (wd env.work (gP + 2 * rem)) st.point)
    (hps : st.point.size = depth - rem) :
    WP stepC s (fun s' ↦ ∃ st' t', (gkrStep (gkrStepOf rem) last st).run t = some (st', t') ∧
      CodeRel env t' s' ∧ NatAt s'.mem (wd env.work gRem) (rem - gkrStepOf rem) ∧
      EWArr s'.mem (wd env.work gTr) st'.values ∧ st'.values.size = 3 ∧
      EWArr s'.mem (wd env.work (gP + 2 * (rem - gkrStepOf rem))) st'.point ∧
      st'.point.size = depth - (rem - gkrStepOf rem) ∧ Step3 env allRegs stepWs s s')
      (fun s' ↦ (gkrStep (gkrStepOf rem) last st).run t = none ∧ Step3 env allRegs stepWs s s') := by
  have h0 : Step3 env allRegs stepWs s s := Step3.refl _ _ _ _
  unfold stepC
  -- step and 2^step
  refine WP.then (WP.mono (setStepC_spec h hi hrem) (fun _ h ↦ h) (fun _ h ↦ h.elim))
    fun s1 ⟨hst1, hN1, hw1⟩ ↦ ?_
  have hsr := gkrStepOf_le hrem0
  have hsc := gkrStepOf_cases rem
  rw [gkrStep_eq (by omega)]
  generalize gkrStepOf rem = step at hsr hsc hst1 hN1 ⊢
  have hp4 : 2 ^ step ≤ 4 := by rcases hsc with rfl | rfl <;> decide
  have h1 := h.wrote3 hi (by gok3_tac) hw1
  have hi1 := hi.step3 (by gok3_tac) hw1.step h.rdi
  have f1 : Step3 env allRegs stepWs s s1 := h0.into hw1.step (by unfold stepWs; gwithin_tac)
  -- the combiner and the claim
  refine WP.then (WP.mono (combC_spec h1 hi1 (hv.congr (n := 6) (by gsamew hw1, hi) (by omega)) hvs
      (NatAt.gkeep hrem (by gsamew hw1, hi)) (NatAt.gkeep hd (by gsamew hw1, hi)) hrd hd64)
      (fun _ h ↦ h) (fun _ h ↦ h.elim))
    fun s2 ⟨comb, t1, hrc, h2, hcb2, hcl2, hpi2, hcnt2, h142, hst2⟩ ↦ ?_
  have hi2 := hi1.step3 (by gok3_tac) hst2 h1.rdi
  have f2 := f1.into hst2 (by unfold stepWs; gwithin_tac)
  -- the rounds
  have hI : RInv env inp s2 rem (2 ^ step) st.point 0 (#[], polyEval st.values comb) t1 s2 := by
    refine ⟨h2, hi2, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, hcl2, rfl, ?_, ?_, Step3.refl _ _ _ _⟩
    · exact NatAt.gkeep hN1 (by gsame hst2, hi1)
    · exact ((ho.congr (n := 8) (by gsame f1, hi) (by decide))).congr (n := 8) (by gsame hst2, hi1)
        (by decide)
    · rw [Nat.add_zero]; exact hpi2
    · rw [hps, Nat.sub_zero]; exact hcnt2
    · rw [hps, Nat.sub_zero]; exact h142
    · exact fun i hi' ↦ absurd hi' (by simp)
    · intro i hi' _
      have := EWArr.gget ((hpt.congr (n := 2 * st.point.size) (by gsamew hw1, hi) (by omega)).congr
        (n := 2 * st.point.size) (by gsame hst2, hi1) (by omega)) hi'
      rwa [show gP + 2 * rem + 2 * i = gP + 2 * (rem + i) by omega] at this
  have hcap : rem + st.point.size ≤ 64 := by omega
  refine WP.then (WP.mono (roundsC_spec hcap hp4 (polyEval st.values comb) t1 s2 hI) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨by unfold gkrStepM; rw [Refines.run_bind_some hrc, Refines.run_bind_none hn],
      f2.into hst (by unfold roundWs stepWs; gwithin_tac)⟩)) fun s3 ⟨r, t2, hrs, hJ⟩ ↦ ?_
  have f3 := f2.into hJ.frame (by unfold roundWs stepWs; gwithin_tac)
  have hcb3 : EWAt s3.mem (wd env.work gComb) comb := hcb2.congr (by gsame hJ.frame, hi2)
  -- the children
  refine WP.then (WP.mono (childC_spec hJ.rel hJ.inp hJ.nN hp4 hJ.ones hcb3 hJ.claim) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨by unfold gkrStepM; rw [Refines.run_bind_some hrc, Refines.run_bind_some hrs,
      Refines.run_bind_none hn], f3.into hst (by unfold stepWs; gwithin_tac)⟩))
    fun s4 ⟨c, t3, hrch, h4, hs0, hs1, hs2, hc0, hc1, hc2, hst4⟩ ↦ ?_
  have hi3 := hJ.inp
  have hi4 := hi3.step3 (by gok3_tac) hst4 hJ.rel.rdi
  have f4 := f3.into hst4 (by unfold stepWs; gwithin_tac)
  have hstep4 : NatAt s4.mem (wd env.work gStep) step :=
    NatAt.gkeep (NatAt.gkeep (NatAt.gkeep hst1 (by gsame hst2, hi1)) (by gsame hJ.frame, hi2))
      (by gsame hst4, hi3)
  have hrem4 : NatAt s4.mem (wd env.work gRem) rem :=
    NatAt.gkeep (NatAt.gkeep (NatAt.gkeep (NatAt.gkeep hrem (by gsamew hw1, hi)) (by gsame hst2, hi1))
      (by gsame hJ.frame, hi2)) (by gsame hst4, hi3)
  -- y, the values, the point
  refine WP.mono (yC_spec h4 hi4 hsc hsr (by omega) hstep4 (NatAt.gkeep hJ.nN (by gsame hst4, hi3))
      hrem4 hc0 hc1 hc2 hs0 hs1 hs2)
    (fun s5 ⟨y, t4, hry, h5, hys, htr, hrem5, hy5, hst5⟩ ↦ ⟨⟨#[multilinearEval c.1 y, multilinearEval c.2.1 y,
      multilinearEval c.2.2 y], y ++ r.1⟩, t4, ?_, h5, hrem5, htr, rfl, ?_, ?_,
      f4.into hst5 (by unfold stepWs; gwithin_tac)⟩) (fun _ h ↦ h.elim)
  · unfold gkrStepM
    rw [Refines.run_bind_some hrc, Refines.run_bind_some hrs, Refines.run_bind_some hrch,
      Refines.run_bind_some hry]
    rfl
  · refine EWArr.gappend hy5 ?_
    have hx := (hJ.xs.congr (n := 2 * st.point.size) (by gsame hst4, hi3) (by rw [hJ.size])).congr
      (n := 2 * st.point.size) (by gsame hst5, hi4) (by rw [hJ.size])
    rwa [hys, show gP + 2 * (rem - step) + 2 * step = gP + 2 * rem by omega]
  · simp only [Array.size_append, hys, hJ.size, hps]
    omega

end NativeVm.Code.P3
