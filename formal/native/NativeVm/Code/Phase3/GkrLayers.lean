module

public import NativeVm.Code.Phase3.GkrStep

/-!
# The walk's start and its loop

`initC_spec`: the trees' first values `[shared, shared, count]`, the ones, `rem := depth`.
`layersC_spec`: the walk's loop against `gkrLayers`, by `LInv` (the remaining depth `rem` at `gRem`
and in `r14`, the trees' values and the point of the walk so far, and the whole run's outcome is
the outcome of the layers left) with `rem` as the variant.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- The regions the walk writes. -/
def gkrWs : List Region := [pointR, treeR, countR, tmpR]

/-- **The walk's start.** -/
theorem initC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {shared count : EW}
    {depth : Nat} (hsh : EWAt s.mem (wd env.work gTr) shared)
    (hct : EWAt s.mem (wd env.work gCt) count) (hd : NatAt s.mem (wd env.work gD) depth) :
    WP initC s (fun s' ↦ EWArr s'.mem (wd env.work gTr) #[shared, shared, count] ∧
      EWArr s'.mem (wd env.work gOnes) gones4 ∧ NatAt s'.mem (wd env.work gRem) depth ∧
      s'.reg .r14 = depth.toUInt64 ∧ Wrote env [treeR, gOnesR, gRemR] s s') (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold initC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (v := shared.c0) (by rsimp) (EWAt.gw0 hsh) ?_
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := shared.c1) (by rsimp) ?_ ?_
  · gmem; exact EWAt.gw1 hsh
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := count.c0) (by rsimp) ?_ ?_
  · gmem; exact EWAt.gw0 hct
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_ldw (env := env) (v := count.c1) (by rsimp) ?_ ?_
  · gmem; exact EWAt.gw1 hct
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  iterate 8
    refine wp_storei (eval_work (env := env) (by rsimp) _) ?_ ?_
    · gex hi
  refine gwp_ldw (env := env) (v := depth.toUInt64) (by rsimp) ?_ ?_
  · gmem; exact hd.2
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine wp_done_gen fun s1 hs1 ↦ ?_
  refine ⟨EWArr.gof fun i hi' ↦ ?_, EWArr.gof fun i hi' ↦ ?_, ⟨hd.1, ?_⟩, ?_, ?_⟩ <;> subst hs1
  · simp only [List.size_toArray, List.length_cons, List.length_nil] at hi'
    interval_cases i <;> refine EWAt.gof ?_ ?_ <;> gmem <;> simp [EWAt.gw0 hsh, EWAt.gw1 hsh]
  · simp only [gones4, List.size_toArray, List.length_cons, List.length_nil] at hi'
    interval_cases i <;> refine EWAt.gof ?_ ?_ <;> gmem <;> rfl
  · gmem
  · rsimp
  · gwrote hi

/-- The walk's result from its final state. -/
def gkrOut (count : EW) (p : GkrStateW × TState) : (EW × Array EW × Array EW) × TState :=
  ((count, p.1.point, p.1.values), p.2)

/-- **The walk's loop invariant** from `s0`, the run from `t0`. -/
def LInv (env : Env) (inp : Input) (s0 : QState) (t0 : TState) (depth : Nat) (count : EW)
    (s : QState) : Prop :=
  ∃ rem st t, rem ≤ depth ∧ CodeRel env t s ∧ Inputs env inp s.mem ∧
    NatAt s.mem (wd env.work gRem) rem ∧ s.reg .r14 = rem.toUInt64 ∧
    NatAt s.mem (wd env.work gD) depth ∧ EWArr s.mem (wd env.work gOnes) gones4 ∧
    EWArr s.mem (wd env.work gTr) st.values ∧ st.values.size = 3 ∧
    EWArr s.mem (wd env.work (gP + 2 * rem)) st.point ∧ st.point.size = depth - rem ∧
    EWAt s.mem (wd env.work gCt) count ∧ Step3 env allRegs gkrWs s0 s ∧
    (verifyGkrGrandProducts depth).run t0 = ((gkrLayers rem st).run t).map (gkrOut count)

theorem gkrLayers_zero (st : GkrStateW) (t : TState) : (gkrLayers 0 st).run t = some (st, t) := by
  rw [gkrLayers]; rfl

/-- **The walk's loop.** -/
theorem layersC_spec {s0 : QState} {t0 : TState} {depth : Nat} {count : EW} (hd64 : depth < 64)
    (hI : LInv env inp s0 t0 depth count s) :
    WP layersC s
      (fun s' ↦ ∃ r t', (verifyGkrGrandProducts depth).run t0 = some (r, t') ∧ CodeRel env t' s' ∧
        EWAt s'.mem (countR.at env.work) r.1 ∧ r.2.1.size = depth ∧
        EWArr s'.mem (pointR.at env.work) r.2.1 ∧ r.2.2.size = 3 ∧
        EWArr s'.mem (treeR.at env.work) r.2.2 ∧ Step3 env allRegs gkrWs s0 s')
      (fun s' ↦ (verifyGkrGrandProducts depth).run t0 = none ∧ Step3 env allRegs gkrWs s0 s') := by
  unfold layersC
  refine WP.loop (LInv env inp s0 t0 depth count) (fun s ↦ (s.reg .r14).toNat) hI ?_ ?_
  · intro s ⟨rem, st, t, hrd, h, hi, hrem, h14, hd, ho, hv, hvs, hpt, hps, hct, hfr, hres⟩ hc
    have hrem0 : 0 < rem := by
      rcases Nat.eq_zero_or_pos rem with e | e
      · subst e; rw [cond_ne, rhs_imm, h14] at hc; exact absurd hc (by decide)
      · exact e
    rw [gkrLayers_pos hrem0] at hres
    refine WP.then (WP.mono (stepC_spec (last := decide (rem = gkrStepOf rem)) h hi hrem0 hrd hd64
        hrem hd ho hv hvs hpt hps) (fun _ h ↦ h)
      (fun s' ⟨hn, hst⟩ ↦ ⟨by rw [hres, Refines.run_bind_none hn]; rfl,
        hfr.into hst (by unfold stepWs gkrWs; gwithin_tac)⟩))
      fun s1 ⟨st', t1, hr1, h1, hrem1, hv1, hvs1, hpt1, hps1, hst1⟩ ↦ ?_
    have hsr := gkrStepOf_le hrem0
    have hs1 : 1 ≤ gkrStepOf rem := by rcases gkrStepOf_cases rem with e | e <;> omega
    refine gwp_ldc h1.rdi h1.workPtr3 ?_
    refine gwp_ldw (env := env) (v := (rem - gkrStepOf rem).toUInt64) (by rsimp) hrem1.2 ?_
    apply WP.blk_nil
    have hi1 := hi.step3 (ws := stepWs) (by unfold stepWs; gok3_tac) hst1 h.rdi
    refine ⟨⟨rem - gkrStepOf rem, st', t1, by omega, h1.setReg3 (by decide) _ |>.setReg3 (by decide) _,
      hi1, hrem1, by rsimp, NatAt.gkeep hd (by gsame hst1, hi), ho.congr (n := 8) (by gsame hst1, hi)
      (by decide), hv1, hvs1, hpt1, hps1, hct.congr (by gsame hst1, hi),
      (hfr.into hst1 (by unfold stepWs gkrWs; gwithin_tac)).into (Wrote.step (ws := []) (by gwrote hi1))
        (gwithin_nil _), ?_⟩, ?_⟩
    · rw [hres, Refines.run_bind_some hr1]
    · rsimp
      rw [h14, Field.toNat_toUInt64 (by omega), Field.toNat_toUInt64 (by omega)]
      omega
  · intro s ⟨rem, st, t, hrd, h, hi, hrem, h14, hd, ho, hv, hvs, hpt, hps, hct, hfr, hres⟩ hc
    have hrem0 : rem = 0 := by
      have : s.reg .r14 = 0 := by simpa [Cond.eval, Rhs.eval, Field.int64Zero_toUInt64] using hc
      rw [h14] at this
      exact Field.toUInt64_eq_zero (by omega) this
    subst hrem0
    rw [gkrLayers_zero] at hres
    refine ⟨(count, st.point, st.values), t, hres, h, hct, by simpa using hps, ?_, hvs, hv, hfr⟩
    simpa [Region.at] using hpt

end NativeVm.Code.P3
