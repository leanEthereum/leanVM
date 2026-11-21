module

public import NativeVm.Code.Phase3.GkrMsg

/-!
# A step's children

`childC_spec`: the three children read at `gChild j`, their products at `gProd`, checked against the
claim (`childM`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- **Child `j` read.** -/
theorem rdChildC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {N j : Nat}
    (hN : NatAt s.mem (wd env.work gN) N) (hN4 : N ≤ 4) (hj : j < 3) :
    WP (rdChildC j) s (fun s' ↦ ∃ c t', (readScalars N).run t = some (c, t') ∧ CodeRel env t' s' ∧
      c.size = N ∧ EWArr s'.mem (wd env.work (gChild j)) c ∧ Step3 env allRegs [gChildR j] s s')
      (fun s' ↦ (readScalars N).run t = none ∧ Step3 env allRegs [gChildR j] s s') := by
  unfold rdChildC
  refine gwp_ldc h.rdi h.workPtr3 ?_
  refine gwp_ldw (env := env) (v := N.toUInt64) (by rsimp) hN.2 ?_
  refine WP.mono (readsTo_spec (r := gChildR j) (by gok3) (by gomega) (by gomega)
      ((h.setReg3 (by decide) _).setReg3 (by decide) _) hi (by rsimp))
    (fun s2 ⟨c, t', hrun, h', hsz, hc, hst⟩ ↦ ⟨c, t', hrun, h', hsz, hc,
      Step3.pre (by gwrote hi) hst (by simp)⟩)
    (fun s2 ⟨hn, hst⟩ ↦ ⟨hn, Step3.pre (by gwrote hi) hst (by simp)⟩)

/-- **Child `j`'s product.** -/
theorem prodC_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) {N j : Nat} {c : Array EW}
    (hN : NatAt s.mem (wd env.work gN) N) (hN4 : N ≤ 4) (hj : j < 3)
    (ho : EWArr s.mem (wd env.work gOnes) gones4) (hc : EWArr s.mem (wd env.work (gChild j)) c)
    (hcs : c.size = N) :
    WP (prodC j) s (fun s' ↦ EWAt s'.mem (wd env.work (gProd + 2 * j)) (prodE c) ∧
      Wrote env [gPrdR j] s s') (fun _ ↦ False) := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold prodC
  refine gwp_ldc hrdi hwp ?_
  fstep
  refine gwp_ldw (env := env) (v := N.toUInt64) (by rsimp) hN.2 ?_
  fstep [add_wdisp]; fstep [add_wdisp]
  refine WP.then (eeq_prod (xs := c) (by rsimp; exact hc) (by rsimp; exact ho) (by omega)
    (by rsimp; rw [hcs])) fun s1 ⟨h9, h10, hm1, hf1⟩ ↦ ?_
  have hw1 : Wrote env [gPrdR j] s s1 := Wrote.kern (by gwrote hi) hm1 hf1
  refine gwp_ldc (hw1.rdi.trans hrdi) (by rw [hw1.ctxw hi (by gok3_tac)]; exact hwp) ?_
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine gwp_stw (env := env) (by rsimp) ?_ ?_
  · gex hi
  refine wp_done_gen fun s2 hs2 ↦ ?_
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> subst hs2
  · gmem; rw [h9]
  · rw [wd_wd, show gProd + 2 * j + 1 = gProd + 2 * j + 1 from rfl]; gmem; rw [h10]
  · gwrote hi

theorem beq_limbs {a b : EW} : (a == b) = true ↔ a.c0 = b.c0 ∧ a.c1 = b.c1 := by
  rw [beq_iff_eq]; cases a; cases b; simp

/-- **The check** `claim == polyEval products comb`. -/
theorem checkC_spec (h : CodeRel env t s) {comb claim : EW}
    {ps : Array EW} (hcb : EWAt s.mem (wd env.work gComb) comb)
    (hcl : EWAt s.mem (wd env.work gClaim) claim) (hps : EWArr s.mem (wd env.work gProd) ps)
    (hpss : ps.size = 3) :
    WP checkC s (fun s' ↦ (claim == polyEval ps comb) = true ∧ Wrote env [] s s')
      (fun s' ↦ (claim == polyEval ps comb) = false ∧ Wrote env [] s s') := by
  have hrdi := h.rdi
  have hwp := h.workPtr3
  unfold checkC
  refine gwp_ldc hrdi hwp ?_
  refine gwp_ldw (env := env) (v := comb.c0) (by rsimp) (EWAt.gw0 hcb) ?_
  refine gwp_ldw (env := env) (v := comb.c1) (by rsimp) (EWAt.gw1 hcb) ?_
  fstep [add_wdisp]; fstep
  refine WP.then (epoly_ew (cs := ps) (b := comb) (by rsimp; exact hps) (by rsimp; rw [hpss]; rfl)
    (by rsimp) (by rsimp) (by omega)) fun s1 ⟨h9, h10, hm1, hf1⟩ ↦ ?_
  have hw1 : Wrote env [] s s1 := Wrote.kern (by gwrote h) hm1 hf1
  have hmem1 : ∀ a, s1.mem a = s.mem a := fun a ↦ by rw [hm1]; rfl
  refine gwp_ldc (hw1.rdi.trans hrdi) (by rw [hmem1]; exact hwp) ?_
  refine gwp_ldw (env := env) (v := claim.c0) (by rsimp) (by rsimp; rw [hmem1]; exact EWAt.gw0 hcl) ?_
  by_cases e0 : (polyEval ps comb).c0 = claim.c0
  · refine wp_failIf (by simp only [cond_ne, rhs_reg]; rsimp; rw [h9, e0]; simp) ?_
    refine gwp_ldw (env := env) (v := claim.c1) (by rsimp) (by rsimp; rw [hmem1]; exact EWAt.gw1 hcl) ?_
    by_cases e1 : (polyEval ps comb).c1 = claim.c1
    · refine wp_failIf (by simp only [cond_ne, rhs_reg]; rsimp; rw [h10, e1]; simp) ?_
      exact WP.blk_nil ⟨beq_limbs.mpr ⟨e0.symm, e1.symm⟩, by gwrote h⟩
    · refine wp_failIf_fail (by simp only [cond_ne, rhs_reg]; rsimp; rw [h10]; simpa using e1) ?_
      refine ⟨?_, by gwrote h⟩
      cases hb : (claim == polyEval ps comb)
      · rfl
      · exact absurd (beq_limbs.mp hb).2.symm e1
  · refine wp_failIf_fail (by simp only [cond_ne, rhs_reg]; rsimp; rw [h9]; simpa using e0) ?_
    refine ⟨?_, by gwrote h⟩
    cases hb : (claim == polyEval ps comb)
    · rfl
    · exact absurd (beq_limbs.mp hb).1.symm e0

end NativeVm.Code.P3
