module

public import NativeVm.Code.Phase3.GkrChildren

/-!
# A step's end

`mleC_spec`: child `j`'s value at `y` at `treeR`'s element `j`. `copyC_spec`: `rem -= step`, `y`
before the point. `yC_spec`: `y` sampled, the trees' values, the point.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- **Child `j`'s value at `y`.** -/
theorem mleC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {j step : Nat}
    {c y : Array EW} (hj : j < 3) (hs : step ≤ 2) (hys : y.size = step)
    (hN : NatAt s.mem (wd env.work gN) (2 ^ step)) (hc : EWArr s.mem (wd env.work (gChild j)) c)
    (hcs : c.size = 2 ^ step) (hy : EWArr s.mem (wd env.work gY) y) :
    WP (mleC j) s (fun s' ↦ EWAt s'.mem (wd env.work (gTr + 2 * j)) (multilinearEval c y) ∧
      Wrote env [gMleR, gTrR j] s s') (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  have hp4 : 2 ^ step ≤ 4 := by interval_cases step <;> decide
  unfold mleC
  refine gwp_ldc hrdi hwp ?_
  fstep; fstep
  refine gwp_ldw (env := env) (v := (2 ^ step).toUInt64) (by rsimp) (by rsimp; exact hN.2) ?_
  fstep [add_wdisp]; fstep [add_wdisp]; fstep [add_wdisp]
  refine WP.then (emle_ew (env := env) (a := gChild j) (b := gMle) (c := gY) (mle := c) (y := y)
    (by rsimp) (by rsimp) (by rsimp) hc hy (by rsimp; rw [hcs]) (by rw [hcs, hys]) (by omega)
    (fun k hk ↦ by rsimp; exact gsome hi (by gomega) (by gomega)) (by gomega) (by gomega)
    (by gomega) (by gomega) (by gomega)) fun s1 ⟨h9, h10, hw1⟩ ↦ ?_
  have hw1' : Wrote env [gMleR, gTrR j] s s1 :=
    (Wrote.gwithin (Wrote.trans (by gwrote hi) hw1) (by gwithin_tac))
  refine gwp_ldc (hw1'.rdi.trans hrdi) (by rw [hw1'.ctxw hi (by gok3_tac)]; exact hwp) ?_
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine wp_done_gen fun s2 hs2 ↦ ?_
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> subst hs2
  · gmem; rw [h9]
  · rw [wd_wd]; gmem; rw [h10]
  · gwrote hi

/-- **`rem -= step`, `y` before the point.** -/
theorem copyC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {rem step : Nat}
    {y : Array EW} (hs : step = 1 ∨ step = 2) (hsr : step ≤ rem) (hr64 : rem ≤ 64)
    (hys : y.size = step) (hrem : NatAt s.mem (wd env.work gRem) rem)
    (hst : NatAt s.mem (wd env.work gStep) step) (hy : EWArr s.mem (wd env.work gY) y) :
    WP copyC s (fun s' ↦ NatAt s'.mem (wd env.work gRem) (rem - step) ∧
      EWArr s'.mem (wd env.work (gP + 2 * (rem - step))) y ∧
      Wrote env [gRemR, gPtR (rem - step) step] s s') (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  have y0 := EWArr.gget hy (i := 0) (by omega)
  unfold copyC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (v := rem.toUInt64) (by rsimp) hrem.2 ?_
  refine gwp_ldw (env := env) (v := step.toUInt64) (by rsimp) hst.2 ?_
  fstep
  rw [sub_word hsr (by omega)]
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  fstep
  rw [two_mul_word]
  refine gwp_ldw (env := env) (v := y[0].c0) (by rsimp) ?_ ?_
  · gmem; exact EWAt.gw0 y0
  refine gwp_stx (env := env) (i := 2 * (rem - step)) (by rsimp) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := y[0].c1) (by rsimp) ?_ ?_
  · gmem; exact EWAt.gw1 y0
  refine gwp_stx (env := env) (i := 2 * (rem - step)) (by rsimp) (by rsimp) ?_ ?_
  · gex hi
  apply WP.blk_cons
  apply WP.ite
  rcases hs with rfl | rfl
  · rw [show (Cond.cmp .eq .rcx (.imm 2)).eval _ = false by
      simp only [cond_eq, rhs_imm]; rsimp; decide]
    refine WP.skip (WP.blk_nil ?_)
    refine ⟨⟨by omega, ?_⟩, EWArr.gof fun i hi' ↦ ?_, ?_⟩
    · gmem
    · obtain rfl : i = 0 := by omega
      refine EWAt.gof ?_ ?_
      · rw [Nat.mul_zero, Nat.add_zero, Nat.add_comm]; gmem
      · rw [Nat.mul_zero, Nat.add_zero, show gP + 2 * (rem - 1) + 1 = 2 * (rem - 1) + (gP + 1) by omega]
        gmem
    · gwrote hi
  · have y1 := EWArr.gget hy (i := 1) (by omega)
    rw [show (Cond.cmp .eq .rcx (.imm 2)).eval _ = true by
      simp only [cond_eq, rhs_imm]; rsimp; decide]
    refine gwp_ldw (env := env) (v := y[1].c0) (by rsimp) ?_ ?_
    · gmem; exact EWAt.gw0 y1
    refine gwp_stx (env := env) (i := 2 * (rem - 2)) (by rsimp) (by rsimp) ?_ ?_
    · gex hi
    refine gwp_ldw (env := env) (v := y[1].c1) (by rsimp) ?_ ?_
    · gmem; exact EWAt.gw1 y1
    refine gwp_stx (env := env) (i := 2 * (rem - 2)) (by rsimp) (by rsimp) ?_ ?_
    · gex hi
    refine WP.blk_nil (WP.blk_nil ⟨⟨by omega, ?_⟩, EWArr.gof fun i hi' ↦ ?_, ?_⟩)
    · gmem
    · have hi2 : i = 0 ∨ i = 1 := by omega
      rcases hi2 with rfl | rfl
      · refine EWAt.gof ?_ ?_
        · rw [Nat.mul_zero, Nat.add_zero, Nat.add_comm]; gmem
        · rw [Nat.mul_zero, Nat.add_zero,
            show gP + 2 * (rem - 2) + 1 = 2 * (rem - 2) + (gP + 1) by omega]
          gmem
      · refine EWAt.gof ?_ ?_
        · rw [show gP + 2 * (rem - 2) + 2 * 1 = 2 * (rem - 2) + (gP + 2) by omega]; gmem
        · rw [show gP + 2 * (rem - 2) + 2 * 1 + 1 = 2 * (rem - 2) + (gP + 3) by omega]; gmem
    · gwrote hi

/-- **`y`, the trees' values, the point.** -/
theorem yC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {rem step : Nat}
    {c0 c1 c2 : Array EW} (hs : step = 1 ∨ step = 2) (hsr : step ≤ rem) (hr64 : rem ≤ 64)
    (hst : NatAt s.mem (wd env.work gStep) step) (hN : NatAt s.mem (wd env.work gN) (2 ^ step))
    (hrem : NatAt s.mem (wd env.work gRem) rem)
    (hc0 : EWArr s.mem (wd env.work (gChild 0)) c0) (hc1 : EWArr s.mem (wd env.work (gChild 1)) c1)
    (hc2 : EWArr s.mem (wd env.work (gChild 2)) c2) (hs0 : c0.size = 2 ^ step)
    (hs1 : c1.size = 2 ^ step) (hs2 : c2.size = 2 ^ step) :
    WP yC s (fun s' ↦ ∃ y t', (sampleChallenges step).run t = some (y, t') ∧ CodeRel env t' s' ∧
      y.size = step ∧
      EWArr s'.mem (wd env.work gTr)
        #[multilinearEval c0 y, multilinearEval c1 y, multilinearEval c2 y] ∧
      NatAt s'.mem (wd env.work gRem) (rem - step) ∧
      EWArr s'.mem (wd env.work (gP + 2 * (rem - step))) y ∧
      Step3 env allRegs [gRemR, gPtR (rem - step) step, treeR, gB] s s') (fun _ ↦ False) := by
  have hs2' : step ≤ 2 := by omega
  have hp4 : 2 ^ step ≤ 4 := by interval_cases step <;> decide
  unfold yC
  refine gwp_ldc h.rdi h.workPtr3 ?_
  refine gwp_ldw (env := env) (v := step.toUInt64) (by rsimp) hst.2 ?_
  refine WP.then (WP.mono (samplesTo_spec (n := step) (r := gYR) (by gok3) (by gomega) (by gomega)
      ((h.setReg3 (by decide) _).setReg3 (by decide) _) hi (by rsimp)) (fun _ h ↦ h)
      (fun _ h ↦ h.elim)) fun s1 ⟨y, t1, hrun, h1, hys, hy, hst1⟩ ↦ ?_
  have f1 : Step3 env allRegs [gYR] s s1 := Step3.pre (by gwrote hi) hst1 (by simp)
  have hi1 := hi.step3 (by gok3_tac) f1 h.rdi
  have hN1 := NatAt.gkeep hN (by gsame f1, hi)
  refine WP.then (WP.mono (mleC_spec (j := 0) h1 hi1 (by omega) hs2' hys hN1
      (hc0.congr (n := 8) (by gsame f1, hi) (by omega)) hs0 hy) (fun _ h ↦ h) (fun _ h ↦ h.elim))
    fun s2 ⟨hv0, hw2⟩ ↦ ?_
  have h2 := h1.wrote3 hi1 (by gok3_tac) hw2
  have hi2 := hi1.step3 (by gok3_tac) hw2.step h1.rdi
  refine WP.then (WP.mono (mleC_spec (j := 1) h2 hi2 (by omega) hs2' hys
      (NatAt.gkeep hN1 (by gsamew hw2, hi1))
      ((hc1.congr (n := 8) (by gsame f1, hi) (by omega)).congr (n := 8) (by gsamew hw2, hi1)
        (by omega)) hs1 (hy.congr (n := 4) (by gsamew hw2, hi1) (by omega)))
      (fun _ h ↦ h) (fun _ h ↦ h.elim)) fun s3 ⟨hv1, hw3⟩ ↦ ?_
  have h3 := h2.wrote3 hi2 (by gok3_tac) hw3
  have hi3 := hi2.step3 (by gok3_tac) hw3.step h2.rdi
  refine WP.then (WP.mono (mleC_spec (j := 2) h3 hi3 (by omega) hs2' hys
      (NatAt.gkeep (NatAt.gkeep hN1 (by gsamew hw2, hi1)) (by gsamew hw3, hi2))
      (((hc2.congr (n := 8) (by gsame f1, hi) (by omega)).congr (n := 8) (by gsamew hw2, hi1)
        (by omega)).congr (n := 8) (by gsamew hw3, hi2) (by omega)) hs2
      ((hy.congr (n := 4) (by gsamew hw2, hi1) (by omega)).congr (n := 4) (by gsamew hw3, hi2)
        (by omega)))
      (fun _ h ↦ h) (fun _ h ↦ h.elim)) fun s4 ⟨hv2, hw4⟩ ↦ ?_
  have h4 := h3.wrote3 hi3 (by gok3_tac) hw4
  have hi4 := hi3.step3 (by gok3_tac) hw4.step h3.rdi
  have hw24 : Wrote env [gMleR, treeR] s1 s4 :=
    ((hw2.gwithin (by gwithin_tac)).trans (hw3.gwithin (by gwithin_tac))).trans
      (hw4.gwithin (by gwithin_tac))
  have hy4 : EWArr s4.mem (wd env.work gY) y := hy.congr (n := 4) (by gsamew hw24, hi1) (by omega)
  refine WP.mono (copyC_spec h4 hi4 hs hsr hr64 hys
      (NatAt.gkeep (NatAt.gkeep hrem (by gsame f1, hi)) (by gsamew hw24, hi1))
      (NatAt.gkeep (NatAt.gkeep hst (by gsame f1, hi)) (by gsamew hw24, hi1)) hy4)
    (fun s5 ⟨hrem5, hpt5, hw5⟩ ↦ ⟨y, t1, hrun, h4.wrote3 hi4 (by gok3_tac) hw5, hys, ?_, hrem5,
      hpt5, ?_⟩) (fun _ h ↦ h.elim)
  · refine ewarr3 ?_ ?_ ?_
    · exact ((hv0.congr (by gsamew hw3, hi2)).congr (by gsamew hw4, hi3)).congr (by gsamew hw5, hi4)
    · exact (hv1.congr (by gsamew hw4, hi3)).congr (by gsamew hw5, hi4)
    · exact hv2.congr (by gsamew hw5, hi4)
  · exact ((Step3.refl env allRegs _ s).into f1 (by gwithin_tac) |>.into hw24.step (by gwithin_tac))
      |>.into hw5.step (by gwithin_tac)

end NativeVm.Code.P3
