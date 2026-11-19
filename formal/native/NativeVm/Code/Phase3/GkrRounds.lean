module

public import NativeVm.Code.Phase3.GkrMsg

/-!
# The sumcheck's rounds

`roundsC` runs the equality-mode sumcheck over the point at `pointR` from element `rem`: round `k`
reads coordinate `rem + k`, and leaves its challenge there (`RInv`: after `k` rounds, the
challenges so far at elements `rem ..`, the coordinates still to read after them). `roundC_spec`
is a round against `roundF`, `roundsC_spec` the loop against `sumcheck` (`Refines.foldlM`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

/-- The regions the rounds write. -/
def roundWs (rem n : Nat) : List Region := [gPtR rem n, gClaimR, gRoundR, gMsgR, gTailR, gChalR]

/-- **After `k` rounds** from `s0`, accumulator `acc`, the transcript at `t`. -/
structure RInv (env : Env) (inp : Input) (s0 : QState) (rem N : Nat) (point : Array EW) (k : Nat)
    (acc : Array EW × EW) (t : TState) (s : QState) : Prop where
  rel : CodeRel env t s
  inp : Inputs env inp s.mem
  kn : k ≤ point.size
  nN : NatAt s.mem (wd env.work gN) N
  ones : EWArr s.mem (wd env.work gOnes) gones4
  pi : NatAt s.mem (wd env.work gPI) (2 * (rem + k))
  cnt : NatAt s.mem (wd env.work gCnt) (point.size - k)
  r14 : s.reg .r14 = (point.size - k).toUInt64
  claim : EWAt s.mem (wd env.work gClaim) acc.2
  size : acc.1.size = k
  xs : EWArr s.mem (wd env.work (gP + 2 * rem)) acc.1
  rest : ∀ i (hi : i < point.size), k ≤ i → EWAt s.mem (wd env.work (gP + 2 * (rem + i))) point[i]
  frame : Step3 env allRegs (roundWs rem point.size) s0 s

variable {env : Env} {inp : Input} {s0 : QState} {rem N : Nat} {point : Array EW}

theorem Step3.ext {W w : List Region} {r : List Reg64} {s s' : QState}
    (h0 : Step3 env allRegs W s0 s) (h : Step3 env r w s s') (hw : ∀ q ∈ w, q ∈ W) :
    Step3 env allRegs W s0 s' :=
  h0.trans (h.gall.mono (fun _ h ↦ h) hw)

theorem EWArr.gpush {mem : UInt64 → Option UInt64} {w : UInt64} {a : Nat} {xs : Array EW} {x : EW}
    (h : EWArr mem (wd w a) xs) (hx : EWAt mem (wd w (a + 2 * xs.size)) x) :
    EWArr mem (wd w a) (xs.push x) :=
  ewarr_push h (by rw [wd_wd]; exact hx)

/-- **A round.** -/
theorem roundC_spec (hcap : rem + point.size ≤ 64) (hN4 : N ≤ 4) {k : Nat} (hk : k < point.size)
    (acc : Array EW × EW) :
    Refines (RInv env inp s0 rem N point k acc) roundC (roundF (N + 1) acc (some point[k]))
      (fun acc' t' s' ↦ RInv env inp s0 rem N point (k + 1) acc' t' s')
      (fun s' ↦ Step3 env allRegs (roundWs rem point.size) s0 s') := by
  intro t s hI
  have hj : rem + k < 64 := by omega
  unfold roundC
  refine WP.then (WP.mono (msgC_spec hI.rel hI.inp hI.nN hN4 hj hI.pi (hI.rest k hk le_rfl) hI.claim
      hI.ones) (fun _ h ↦ h)
    (fun s' ⟨hn, hst⟩ ↦ ⟨roundF_none hn, hI.frame.ext hst (by simp [roundWs])⟩))
    fun s1 ⟨tail, t1, hrun1, h1, hsz, htail, hm0, hst1⟩ ↦ ?_
  have hi := hI.inp
  have hi1 := hi.step3 (by gok3_tac) hst1 hI.rel.rdi
  refine WP.then (WP.mono (sampleTo_spec (r := gChalR) (by gok3) (by gomega) (by gomega) h1 hi1)
    (fun _ h ↦ h) (fun _ h ↦ h.elim)) fun s2 ⟨c, t2, hrun2, h2, hch, hst2⟩ ↦ ?_
  have hi2 := hi1.step3 (by gok3_tac) hst2 h1.rdi
  have hN2 := NatAt.gkeep (NatAt.gkeep hI.nN (by gsame hst1, hi)) (by gsame hst2, hi1)
  have hmsg : EWArr s2.mem (wd env.work gMsg) (#[acc.2 + point[k] * sumE tail] ++ tail) := by
    refine EWArr.gcons_iff.mpr ⟨hm0.congr (by gsame hst2, hi1), ?_⟩
    exact htail.congr (n := 8) (by gsame hst2, hi1) (by omega)
  have hpi2 := NatAt.gkeep (NatAt.gkeep hI.pi (by gsame hst1, hi)) (by gsame hst2, hi1)
  have hcnt2 := NatAt.gkeep (NatAt.gkeep hI.cnt (by gsame hst1, hi)) (by gsame hst2, hi1)
  rw [show point.size - k = (point.size - k - 1) + 1 by omega] at hcnt2
  refine WP.mono (nextC_spec h2 hi2 hch hN2 hN4 hmsg (by simp; omega) hj hpi2 hcnt2 (by omega))
    (fun s3 ⟨hcl, hpt, hpi3, hcnt3, h14, hw3⟩ ↦ ?_) (fun _ h ↦ h.elim)
  have hst3 := hw3.step
  refine ⟨_, t2, roundF_run (by omega) hrun1 hrun2, ⟨h2.wrote3 hi2 (by gok3_tac) hw3,
    hi2.step3 (by gok3_tac) hst3 h2.rdi, by omega, ?_, ?_, ?_, ?_, ?_, hcl, ?_, ?_, ?_, ?_⟩⟩
  · exact NatAt.gkeep hN2 (by gsame hst3, hi2)
  · exact ((hI.ones.congr (n := 8) (by gsame hst1, hi) (by decide)).congr (n := 8)
      (by gsame hst2, hi1) (by decide)).congr (n := 8) (by gsame hst3, hi2) (by decide)
  · rw [show rem + (k + 1) = rem + k + 1 by omega]; exact hpi3
  · rw [show point.size - (k + 1) = point.size - k - 1 by omega]; exact hcnt3
  · rw [show point.size - (k + 1) = point.size - k - 1 by omega]; exact h14
  · simp [hI.size]
  · have hx := ((hI.xs.congr (n := 2 * k) (by gsame hst1, hi) (by rw [hI.size])).congr (n := 2 * k)
      (by gsame hst2, hi1) (by rw [hI.size])).congr (n := 2 * k) (by gsame hst3, hi2)
      (by rw [hI.size])
    refine EWArr.gpush hx ?_
    rw [hI.size, show gP + 2 * rem + 2 * k = gP + 2 * (rem + k) by omega]
    exact hpt
  · intro i hi' hki
    exact (((hI.rest i hi' (by omega)).congr (by gsame hst1, hi)).congr (by gsame hst2, hi1)).congr
      (by gsame hst3, hi2)
  · exact ((hI.frame.ext hst1 (by simp [roundWs])).ext hst2 (by simp [roundWs])).ext
      (hst3.gwithin (ws' := roundWs rem point.size) (by unfold roundWs; gwithin_tac)) (fun _ h ↦ h)

end NativeVm.Code.P3
