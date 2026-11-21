module

public import NativeVm.Code.Phase3.ShareBase
public import NativeVm.Field.Mle

/-!
# The bytecode share: the check

`shCheck`: the weights' multilinear extension at the slot (`emle`, its work area `shFoldR`) times
the value, against the claim: `bytecodeShare`'s `claim == dot (eqKernel slot) weights * value`
(`share_dot_eqKernel`). It writes `shFoldR` alone (`shCheck_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code NativeVm.Equiv

variable {env : Env} {inp : Input} {t : TState} {s : QState}

theorem ew_wd (p : UInt64) (k : Nat) : ew p k = wd p k := rfl

/-- **The check.** -/
theorem shCheck_spec {weights slot : Array EW} {claim value : EW} {P F : QState → Prop}
    (hrdi : s.reg .rdi = env.ctx) (hwk : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem)
    (hw : EWArr s.mem (wd env.work wR.off) weights) (hws : weights.size = 16)
    (hs : EWArr s.mem (wd env.work slotR.off) slot) (hss : slot.size = 4)
    (hcl : EWAt s.mem (wd env.work shClaimW) claim) (hv : EWAt s.mem (wd env.work valueR.off) value)
    (hP : ∀ s', (claim == dot (eqKernel slot) weights * value) = true → Wrote env [shFoldR] s s' →
      P s')
    (hF : ∀ s', (claim == dot (eqKernel slot) weights * value) = false → Wrote env [shFoldR] s s' →
      F s') :
    WP shCheck s P F := by
  have hww := workWords_lt hi
  have hdl := dataEnd_le inp.bytecode.size
  rw [dataEnd_eq] at hdl
  have hsome : ∀ k < 85438, (s.mem (wd env.work k)).isSome := fun k hk ↦ hi.workSome k (by omega)
  obtain ⟨v0, v1⟩ := hv
  obtain ⟨l0, l1⟩ := hcl
  rw [wd_wd] at v1 l1
  unfold shCheck
  refine wp_load (eval_cw hrdi _) hwk ?_
  refine wp_reg rfl (wp_reg rfl (wp_reg rfl (wp_reg rfl ?_)))
  rw [EWArr_iff_EArr] at hw hs
  refine wp_then' (emle_spec (mle := weights.toList.map EW.toE) (point := slot.toList.map EW.toE)
    (src := wd env.work wR.off) (work := wd env.work shFoldW) (pt := wd env.work slotR.off)
    (by rsimp; exact eval_work (by rsimp) _) (by rsimp; exact eval_work (by rsimp) _)
    (by rsimp; exact eval_work (by rsimp) _) hw hs (by rsimp; simp [hws]) (by simp [hws, hss])
    (by simp [hss]) (fun k hk ↦ ?_) (fun k j l l' _ hj hl hl' ↦ ?_) (fun k hk j hj ↦ ?_))
    fun u ⟨e1, e2, e3⟩ ed ↦ ?_
  · simp only [List.length_map, Array.length_toList, hws] at hk
    rw [ew_wd, wd_wd]; exact hsome _ (by sh_reg)
  · simp only [List.length_map, Array.length_toList, hws] at hj
    rw [ew_wd, ew_wd, wd_wd, wd_wd, Ne, wd_inj (by sh_reg) (by sh_reg)]; sh_reg
  · simp only [List.length_map, Array.length_toList, hws, hss] at hk hj
    rw [ew_wd, ew_wd, wd_wd, wd_wd, Ne, wd_inj (by sh_reg) (by sh_reg)]; sh_reg
  simp only [List.length_map, Array.length_toList, hws, QState.setReg_mem] at e2 ed
  have hkeep : ∀ a, ¬ shFoldR.In env.work a → u.mem a = s.mem a := fun a ha ↦
    e2 a fun k hk e ↦ ha ⟨k, by sh_reg, by rw [e, ew_wd, wd_wd]⟩
  have hk : ∀ k, k < shFoldW ∨ shFoldW + 16 ≤ k → k < 2 ^ 61 →
      u.mem (wd env.work k) = s.mem (wd env.work k) := fun k hk hk' ↦
    hkeep _ fun ⟨j, hj, e⟩ ↦ by rw [wd_inj hk' (by sh_reg_at)] at e; sh_reg_at
  have urdi : u.reg .rdi = env.ctx := by rw [e3 .rdi (by decide)]; rsimp; exact hrdi
  have hwu : Wrote env [shFoldR] s u := ⟨by rw [urdi, hrdi], fun a ha ↦ hkeep a (ha _ (by simp)),
    fun a ↦ by rw [ed]⟩
  refine wp_load (eval_cw urdi _) (by
    rw [hkeep _ fun ⟨j, hj, e⟩ ↦ hi.ctx_ne_work (by lay_omega) (by sh_reg_at) e]; exact hwk) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _)
    (by rsimp; rw [hk _ (by sh_reg) (by sh_reg)]; exact v0) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _)
    (by rsimp; rw [hk _ (by sh_reg) (by sh_reg)]; exact v1) ?_
  refine WP.then (emul_spec _) fun w ⟨a1, m1, f1⟩ ↦ ?_
  rsimp at a1 m1
  have wsi : w.reg .rsi = env.work := by rw [f1 .rsi (by decide)]; rsimp
  have wrdi : w.reg .rdi = env.ctx := by rw [f1 .rdi (by decide)]; rsimp; exact urdi
  have hww' : Wrote env [shFoldR] s w :=
    hwu.trans ⟨by rw [wrdi, urdi], fun a _ ↦ by rw [m1], fun a ↦ by rw [m1]⟩
  have hX : eOf (w.reg .r9) (w.reg .r10) = (dot (eqKernel slot) weights * value).toE := by
    rw [a1, e1, EW.toE_mul, share_dot_eqKernel hss hws, toE_multilinearEval]
    rfl
  have hb := sh_check_iff (v := claim) hX
  refine wp_load (eval_work wsi _) (by rw [m1, hk _ (by sh_reg) (by sh_reg)]; exact l0) ?_
  by_cases h0 : w.reg .r9 = claim.c0
  · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ?_
    refine wp_load (eval_work (by rsimp; exact wsi) _)
      (by rsimp; rw [m1, hk _ (by sh_reg) (by sh_reg)]; exact l1) ?_
    by_cases h1 : w.reg .r10 = claim.c1
    · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) (WP.blk_nil ?_)
      exact hP _ (hb.mpr ⟨h0, h1⟩) (hww'.setReg (r := .rax) (by decide) _ |>.setReg (r := .rax) (by decide) _)
    · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) ?_
      exact hF _ (Bool.eq_false_iff.mpr fun e ↦ h1 (hb.mp e).2)
        (hww'.setReg (r := .rax) (by decide) _ |>.setReg (r := .rax) (by decide) _)
  · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ?_
    exact hF _ (Bool.eq_false_iff.mpr fun e ↦ h0 (hb.mp e).1) (hww'.setReg (r := .rax) (by decide) _)

end NativeVm.Code.P3
