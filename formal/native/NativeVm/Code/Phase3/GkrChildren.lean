module

public import NativeVm.Code.Phase3.GkrChild

/-!
# A step's children, together

`childC_spec`: `childC` against `childM`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s s0 : QState}

/-- A run inside the regions of a run so far. -/
theorem Step3.into {W w : List Region} {r : List Reg64} {s' : QState}
    (h0 : Step3 env allRegs W s0 s) (h : Step3 env r w s s') (hw : ∀ q ∈ w, ∃ q' ∈ W, Within q q') :
    Step3 env allRegs W s0 s' :=
  h0.trans ((h.gwithin hw).gall)

theorem ewarr3 {mem : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {x y z : EW}
    (hx : EWAt mem (wd w a) x) (hy : EWAt mem (wd w (a + 2)) y) (hz : EWAt mem (wd w (a + 4)) z) :
    EWArr mem (wd w a) #[x, y, z] := by
  refine EWArr.gof fun i hi ↦ ?_
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
  interval_cases i
  · simpa using hx
  · simpa using hy
  · simpa using hz

/-- **The children and their check.** -/
theorem childC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {N : Nat} {comb claim : EW}
    (hN : NatAt s.mem (wd env.work gN) N) (hN4 : N ≤ 4)
    (ho : EWArr s.mem (wd env.work gOnes) gones4) (hcb : EWAt s.mem (wd env.work gComb) comb)
    (hcl : EWAt s.mem (wd env.work gClaim) claim) :
    WP childC s (fun s' ↦ ∃ r t', (childM N claim comb).run t = some (r, t') ∧ CodeRel env t' s' ∧
      r.1.size = N ∧ r.2.1.size = N ∧ r.2.2.size = N ∧
      EWArr s'.mem (wd env.work (gChild 0)) r.1 ∧ EWArr s'.mem (wd env.work (gChild 1)) r.2.1 ∧
      EWArr s'.mem (wd env.work (gChild 2)) r.2.2 ∧ Step3 env allRegs [gB] s s')
      (fun s' ↦ (childM N claim comb).run t = none ∧ Step3 env allRegs [gB] s s') := by
  have h0 : Step3 env allRegs [gB] s s := Step3.refl _ _ _ _
  unfold childC
  refine WP.then (WP.mono (rdChildC_spec (j := 0) h hi hN hN4 (by omega)) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨by unfold childM; rw [Refines.run_bind_none hn],
      h0.into hst (by gwithin_tac)⟩)) fun s1 ⟨c0, t1, hr0, h1, hs0, hc0, hst1⟩ ↦ ?_
  have hi1 := hi.step3 (by gok3_tac) hst1 h.rdi
  have f1 := h0.into hst1 (by gwithin_tac)
  have hN1 := NatAt.gkeep hN (by gsame hst1, hi)
  refine WP.then (WP.mono (rdChildC_spec (j := 1) h1 hi1 hN1 hN4 (by omega)) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨by unfold childM; rw [Refines.run_bind_some hr0, Refines.run_bind_none hn],
      f1.into hst (by gwithin_tac)⟩)) fun s2 ⟨c1, t2, hr1, h2, hs1, hc1, hst2⟩ ↦ ?_
  have hi2 := hi1.step3 (by gok3_tac) hst2 h1.rdi
  have f2 := f1.into hst2 (by gwithin_tac)
  have hN2 := NatAt.gkeep hN1 (by gsame hst2, hi1)
  refine WP.then (WP.mono (rdChildC_spec (j := 2) h2 hi2 hN2 hN4 (by omega)) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨by unfold childM; rw [Refines.run_bind_some hr0, Refines.run_bind_some hr1,
      Refines.run_bind_none hn], f2.into hst (by gwithin_tac)⟩))
    fun s3 ⟨c2, t3, hr2, h3, hs2, hc2, hst3⟩ ↦ ?_
  have hi3 := hi2.step3 (by gok3_tac) hst3 h2.rdi
  have f3 := f2.into hst3 (by gwithin_tac)
  have hN3 := NatAt.gkeep hN2 (by gsame hst3, hi2)
  have ho3 : EWArr s3.mem (wd env.work gOnes) gones4 :=
    ((ho.congr (n := 8) (by gsame hst1, hi) (by decide)).congr (n := 8) (by gsame hst2, hi1)
      (by decide)).congr (n := 8) (by gsame hst3, hi2) (by decide)
  have hc0' : EWArr s3.mem (wd env.work (gChild 0)) c0 :=
    (hc0.congr (n := 8) (by gsame hst2, hi1) (by omega)).congr (n := 8) (by gsame hst3, hi2) (by omega)
  have hc1' : EWArr s3.mem (wd env.work (gChild 1)) c1 :=
    hc1.congr (n := 8) (by gsame hst3, hi2) (by omega)
  refine WP.then (WP.mono (prodC_spec (j := 0) h3 hi3 hN3 hN4 (by omega) ho3 hc0' hs0) (fun _ h ↦ h) (fun _ h ↦ h.elim))
    fun s4 ⟨hp0, hw4⟩ ↦ ?_
  have h4 := h3.wrote3 hi3 (by gok3_tac) hw4
  have hi4 := hi3.step3 (by gok3_tac) hw4.step h3.rdi
  refine WP.then (WP.mono (prodC_spec (j := 1) h4 hi4 (NatAt.gkeep hN3 (by gsamew hw4, hi3)) hN4 (by omega)
    (ho3.congr (n := 8) (by gsamew hw4, hi3) (by decide))
    (hc1'.congr (n := 8) (by gsamew hw4, hi3) (by omega)) hs1) (fun _ h ↦ h) (fun _ h ↦ h.elim)) fun s5 ⟨hp1, hw5⟩ ↦ ?_
  have h5 := h4.wrote3 hi4 (by gok3_tac) hw5
  have hi5 := hi4.step3 (by gok3_tac) hw5.step h4.rdi
  refine WP.then (WP.mono (prodC_spec (j := 2) h5 hi5
    (NatAt.gkeep (NatAt.gkeep hN3 (by gsamew hw4, hi3)) (by gsamew hw5, hi4)) hN4 (by omega)
    ((ho3.congr (n := 8) (by gsamew hw4, hi3) (by decide)).congr (n := 8) (by gsamew hw5, hi4)
      (by decide))
    ((hc2.congr (n := 8) (by gsamew hw4, hi3) (by omega)).congr (n := 8) (by gsamew hw5, hi4)
      (by omega)) hs2) (fun _ h ↦ h) (fun _ h ↦ h.elim)) fun s6 ⟨hp2, hw6⟩ ↦ ?_
  have h6 := h5.wrote3 hi5 (by gok3_tac) hw6
  have hi6 := hi5.step3 (by gok3_tac) hw6.step h5.rdi
  have hw46 : Wrote env [gProdR] s3 s6 :=
    ((hw4.gwithin (by gwithin_tac)).trans (hw5.gwithin (by gwithin_tac))).trans (hw6.gwithin (by gwithin_tac))
  have hcb6 : EWAt s6.mem (wd env.work gComb) comb :=
    hcb.congr (by gsame f3, hi) |>.congr (by gsamew hw46, hi3)
  have hcl6 : EWAt s6.mem (wd env.work gClaim) claim :=
    hcl.congr (by gsame f3, hi) |>.congr (by gsamew hw46, hi3)
  have hps : EWArr s6.mem (wd env.work gProd) #[prodE c0, prodE c1, prodE c2] := by
    refine ewarr3 ?_ ?_ ?_
    · exact (hp0.congr (by gsamew hw5, hi4)).congr (by gsamew hw6, hi5)
    · exact hp1.congr (by gsamew hw6, hi5)
    · exact hp2
  have f6 : Step3 env allRegs [gB] s s6 := f3.into hw46.step (by gwithin_tac)
  refine WP.mono (checkC_spec h6 hcb6 hcl6 hps rfl) (fun s7 ⟨hb, hw7⟩ ↦ ?_) (fun s7 ⟨hb, hw7⟩ ↦ ?_)
  · refine ⟨(c0, c1, c2), t3, ?_, h6.wrote3 hi6 (by gok3_tac) hw7, hs0, hs1,
      hs2, ?_, ?_, ?_, f6.into hw7.step (by gwithin_tac)⟩
    · unfold childM
      rw [Refines.run_bind_some hr0, Refines.run_bind_some hr1, Refines.run_bind_some hr2,
        Refines.run_bind_some (by rw [Refines.require_run, hb]; rfl)]
      rfl
    · exact (((hc0'.congr (n := 8) (by gsamew hw46, hi3) (by omega))).congr (n := 8)
        (by gsamew hw7, hi6) (by dsimp only; omega))
    · exact ((hc1'.congr (n := 8) (by gsamew hw46, hi3) (by omega))).congr (n := 8)
        (by gsamew hw7, hi6) (by dsimp only; omega)
    · exact ((hc2.congr (n := 8) (by gsamew hw46, hi3) (by omega))).congr (n := 8)
        (by gsamew hw7, hi6) (by dsimp only; omega)
  · refine ⟨?_, f6.into hw7.step (by gwithin_tac)⟩
    unfold childM
    rw [Refines.run_bind_some hr0, Refines.run_bind_some hr1, Refines.run_bind_some hr2,
      Refines.run_bind_none (by rw [Refines.require_run, hb]; rfl)]

end NativeVm.Code.P3
