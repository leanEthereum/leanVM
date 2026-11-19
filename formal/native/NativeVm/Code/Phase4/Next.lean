module

public import NativeVm.Code.Phase4.Frames

/-!
# The tables' loop's bookkeeping and the final check

`termsInitC_spec`: the loop's start (`final = 0` at `oFIN`, the widths at `oWID`, the first table's
index and addresses); `nextC_spec`: the next table's index and addresses; `checkC_spec`: the code
fails exactly when `final ≠ claim`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- **The loop's start.** -/
theorem termsInitC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s) :
    WP termsInitC s (fun s' ↦ EWAt s'.mem (wd env.work oFIN) 0 ∧
      (∀ i < 6, s'.mem (wd env.work (oWID + i)) = some (widths.getD i 0).toUInt64) ∧
      s'.mem (wd env.work oTIX) = some (0 : Nat).toUInt64 ∧
      s'.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * 0)) ∧
      s'.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * 0)) ∧
      s'.reg .rcx = (0 : Nat).toUInt64 ∧
      Wr env.work (fun j ↦ (oFIN ≤ j ∧ j < oFIN + 2) ∨ (oTIX ≤ j ∧ j < oWID + 6)) s s' ∧
      RegsFrame arrRegs s s') E := by
  unfold termsInitC
  wst; wst; wst; wst; wst; wst; wst; wst; wst
  wst; wst; wst; wst; wst; wst
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  refine ⟨EWAt.of (by memw; rfl) (by memw; rfl), fun i hi ↦ ?_, by memw; rfl, by memw,
    by memw, by rsimp; rfl, by wr_tac, by rfw⟩
  interval_cases i <;> (memw; rfl)

/-- **The next table**: its index in `oTIX` and `rcx`, its forms' and its entry's addresses. -/
theorem nextC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) (hws : WS env s) {k : Nat}
    (hix : s.mem (wd env.work oTIX) = some k.toUInt64)
    (hfp : s.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * k)))
    (hep : s.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * k))) :
    WP nextC s (fun s' ↦ s'.mem (wd env.work oTIX) = some (k + 1).toUInt64 ∧
      s'.mem (wd env.work oFPTR) = some (wd env.work (oB + formsStride * (k + 1))) ∧
      s'.mem (wd env.work oEPTR) = some (wd env.work (oE + eS * (k + 1))) ∧
      s'.reg .rcx = (k + 1).toUInt64 ∧
      Wr env.work (fun j ↦ oTIX ≤ j ∧ j < oTIX + 3) s s' ∧ RegsFrame arrRegs s s') E := by
  have hix' := hix
  have hfp' := hfp
  have hep' := hep
  wnorm at hix' hfp' hep'
  unfold nextC
  wst; wst; wst; wst; wst; wst; wst; wst; wst; wst
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  refine ⟨by memw; rw [toUInt64_succ], by memw; rw [Nat.mul_add_one], by memw; rw [Nat.mul_add_one],
    by rsimp; rw [toUInt64_succ], by wr_tac, by rfw⟩

/-- `EW`'s `==`, limb by limb. -/
theorem ew_beq (a b : EW) : (a == b) = (a.c0 == b.c0 && a.c1 == b.c1) := by
  cases a; cases b; rfl

/-- **`require (final == claim)`**: the code ends normally exactly when `final == claim`, writing
no word. -/
theorem checkC_spec (hrdi : s.reg .rdi = env.ctx)
    (hctx : s.mem (wd env.ctx ctxWork) = some (wd env.work 0)) {fin claim : EW}
    (hf : EWAt s.mem (wd env.work oFIN) fin) (hc : EWAt s.mem (wd env.work oCLM) claim) :
    WP checkC s (fun s' ↦ (fin == claim) = true ∧ s'.mem = s.mem ∧ RegsFrame arrRegs s s')
      (fun s' ↦ (fin == claim) = false ∧ s'.mem = s.mem ∧ RegsFrame arrRegs s s') := by
  obtain ⟨hf0, hf1⟩ := hf
  obtain ⟨hc0, hc1⟩ := hc
  wnorm at hf0 hf1 hc0 hc1
  unfold checkC
  wst; wst; wst
  by_cases h0 : fin.c0 = claim.c0
  · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ?_
    wst; wst
    by_cases h1 : fin.c1 = claim.c1
    · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) ?_
      refine wp_done_gen fun s' hs' ↦ ?_
      subst hs'
      exact ⟨by rw [ew_beq, h0, h1]; simp, by rsimp, by rfw⟩
    · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) ?_
      exact ⟨by rw [ew_beq]; simp [h1], by rsimp, by rfw⟩
  · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ?_
    exact ⟨by rw [ew_beq]; simp [h0], by rsimp, by rfw⟩

end NativeVm.Code.P4
