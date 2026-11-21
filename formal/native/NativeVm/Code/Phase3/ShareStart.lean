module

public import NativeVm.Code.Phase3.ShareRound

/-!
# The bytecode share: the start

`shStart` reads the share into `shareR`, copies it into the claim and sets up the rounds' loop
(`shStart_spec`: `shInv 0 (#[], share)`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- **The start.** -/
theorem shStart_spec (h : CodeRel env t s) (hi : Inputs env inp s.mem) :
    WP shStart s
      (fun s' ↦ ∃ share t', Model.readScalar.run t = some (share, t') ∧
        shInv env inp s share 0 (#[], share) t' s')
      (fun s' ↦ Model.readScalar.run t = none ∧ Step3 env allRegs shW s s') := by
  unfold shStart
  refine WP.blk_cons (WP.mono (readTo_spec (r := shareR) (k := shareR.off) (by sh_reg) le_rfl
    (by sh_reg) h hi) (fun s1 ⟨x, t1, hr1, hc1, he1, hs1⟩ ↦ ?_)
    (fun s1 ⟨hr1, hs1⟩ ↦ ⟨hr1, sh_step hs1 (by sh_reg)⟩))
  have hok1 : ∀ r ∈ [shareR], Ok3 r := by sh_reg
  have hi1 : Inputs env inp s1.mem := hi.step3 hok1 hs1 h.rdi
  obtain ⟨x0, x1⟩ := he1
  rw [wd_wd] at x1
  refine wp_load (eval_cw hc1.rdi _) hc1.workPtr3 ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact x0) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact x1) ?_
  refine sh_storePair (r := shClaimR) (a := shClaimW) (by sh_reg) le_rfl (by sh_reg)
    (eval_work (by rsimp) _) (eval_work (by rsimp) _) hi1 fun s2 hw2 he2 hreg2 ↦ ?_
  have hok2 : ∀ r ∈ [shClaimR], Ok3 r := by sh_reg
  have hc2 : CodeRel env t1 s2 :=
    (((hc1.setReg3 (r := .r11) (by decide) _).setReg3 (r := .r9) (by decide) _).setReg3
      (r := .r10) (by decide) _).wrote3 hi1 hok2 hw2
  have hs2 : Step3 env allRegs [shClaimR] s1 s2 :=
    (((Wrote.refl env [shClaimR] s1).setReg (r := .r11) (by decide) _ |>.setReg (r := .r9)
      (by decide) _ |>.setReg (r := .r10) (by decide) _).trans hw2).step
  have hi2 : Inputs env inp s2.mem := hi1.step3 hok2 hs2 hc1.rdi
  fstep
  refine wp_reg rfl (WP.blk_nil ⟨x, t1, hr1, ?_, hi2, rfl, fun _ h ↦ absurd h (by simp), ?_, ?_, ?_,
    ?_, ?_⟩)
  · exact (hc2.setReg3 (r := .r13) (by decide) _).setReg3 (r := .r14) (by decide) _
  · rsimp at he2; exact he2
  · rsimp; rfl
  · rsimp
    exact eval_work (by rsimp; rw [hreg2]; rsimp) _
  · rsimp; exact ewat_keep hs2 hi1 hok2 (q := shareR) (by sh_reg) (by sh_reg) le_rfl (by sh_reg)
      ⟨x0, by rw [wd_wd]; exact x1⟩
  · refine (sh_step hs1 (by sh_reg)).trans (sh_step hs2 (by sh_reg)) |>.trans ?_
    exact ((Wrote.refl env [tmpR] s2).setReg (r := .r13) (by decide) _
      |>.setReg (r := .r14) (by decide) _).step.mono (fun _ h ↦ h) (by simp)

end NativeVm.Code.P3
