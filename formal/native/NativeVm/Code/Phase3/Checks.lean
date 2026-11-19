module

public import NativeVm.Code.Phase3.Common

/-!
# Phase 3's checks and its grind

`checkDepth`: the push side's depth from `depthR` into `rsi`, rejected unless below `64`;
`grindBus`: the grind of `busGrindingBits depth = depth - 3` bits, none below `4`;
`checkCount`: the count root at `countR` rejected when zero.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters
open LeanVM.Protocol.Verifier (busGrindingBits)

variable {env : Env} {inp : Input} {t : TState} {s : QState}

theorem busGrindingBits_eq (d : Nat) : busGrindingBits d = d - 3 := by
  unfold busGrindingBits LeanVM.Protocol.Compile.grindingBits LeanVM.Protocol.Compile.securityBits
  rcases d with _ | d
  · rfl
  · have h1 : ¬ 2 ^ (d + 1) ≤ 1 := by
      have := Nat.one_lt_two_pow (n := d + 1) (by omega); omega
    have h2 : (2 ^ (d + 1) - 1).log2 = d :=
      (Nat.log2_eq_iff (by have := Nat.one_lt_two_pow (n := d + 1) (by omega); omega)).mpr
        ⟨by have := Nat.one_le_two_pow (n := d); rw [Nat.pow_succ]; omega, by omega⟩
    simp only [h1, ↓reduceIte, h2]

/-- The depth into `rsi`; reject unless it is below `64`. -/
def checkDepth : Stmt := blk [I (.load .r11 (cw ctxWork)),
  I (.load .rsi (at_ .r11 (wdisp depthR.off))), failIf (.cmp .geu .rsi (.imm 64))]

theorem checkDepth_spec {d : Nat} (h : CodeRel env t s)
    (hd : NatAt s.mem (depthR.at env.work) d) :
    WP checkDepth s
      (fun s' ↦ d < 64 ∧ s'.reg .rsi = d.toUInt64 ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .rsi] s s')
      (fun s' ↦ ¬ d < 64 ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .rsi] s s') := by
  unfold checkDepth
  refine wp_load (eval_cw h.rdi ctxWork) h.workPtr3 ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rw [← Region.at.eq_def]; exact hd.2) ?_
  by_cases hlt : d < 64
  · refine wp_failIf ?_ (WP.blk_nil ⟨hlt, by rsimp, rfl, by rf_tac⟩)
    rw [cond_geu, rhs_imm]
    rsimp
    simp only [decide_eq_false_iff_not]
    show ¬ (64 : Nat).toUInt64 ≤ d.toUInt64
    rw [toUInt64_le (by norm_num) hd.1]
    omega
  · refine wp_failIf_fail ?_ ⟨hlt, rfl, by rf_tac⟩
    rw [cond_geu, rhs_imm]
    rsimp
    simp only [decide_eq_true_eq]
    show (64 : Nat).toUInt64 ≤ d.toUInt64
    exact (toUInt64_le (by norm_num) hd.1).mpr (by omega)

/-- `grind (depth - 3)`, the depth in `rsi`: no grind below `4`. -/
def grindBus : Stmt :=
  .ite (.cmp .geu .rsi (.imm 4)) (blk [I (.subi .rsi 3), Transcript.grind]) .skip

theorem grindBus_spec {d : Nat} (h : CodeRel env t s) (hd : d < 64)
    (hrsi : s.reg .rsi = d.toUInt64) :
    WP grindBus s
      (fun s' ↦ ∃ t', (grind (busGrindingBits d)).run t = some ((), t') ∧ CodeRel env t' s' ∧
        Step3 env clobbers [] s s')
      (fun s' ↦ (grind (busGrindingBits d)).run t = none ∧ Step3 env clobbers [] s s') := by
  rw [busGrindingBits_eq]
  unfold grindBus
  refine WP.ite ?_
  rw [cond_geu, rhs_imm, hrsi, show ((4 : Int64).toUInt64) = (4 : Nat).toUInt64 from rfl]
  by_cases h4 : 4 ≤ d
  · simp only [decide_eq_true ((toUInt64_le (by norm_num) (by omega)).mpr h4), ↓reduceIte]
    refine wp_reg rfl ?_
    have hc : CodeRel env t (s.setReg .rsi (s.reg .rsi - (3 : Int64).toUInt64)) :=
      h.setReg3 (by decide) _
    have hr : (s.setReg .rsi (s.reg .rsi - (3 : Int64).toUInt64)).reg .rsi = (d - 3).toUInt64 := by
      rsimp
      rw [hrsi, show d = (d - 3) + 3 by omega, ← toUInt64_add, show d - 3 + 3 - 3 = d - 3 by omega]
      exact UInt64.add_sub_cancel _ _
    have h0 : Step3 env clobbers [] s (s.setReg .rsi (s.reg .rsi - (3 : Int64).toUInt64)) :=
      ⟨by rsimp, fun r hr ↦ by
        have : r ≠ .rsi := fun e ↦ hr (by simp [e, clobbers])
        simp [this], fun _ _ _ ↦ rfl, fun _ ↦ rfl⟩
    refine WP.blk_cons (WP.mono (WP.frame (grindM_spec hc (by omega) (by omega) hr)) ?_ ?_)
    · rintro s' ⟨⟨t', hrun, hc', hk⟩, hdom, -⟩
      exact WP.blk_nil ⟨t', hrun, hc', h0.trans (Step3.ofKeeps hk hdom)⟩
    · rintro s' ⟨⟨hrun, hk⟩, hdom, -⟩
      exact ⟨hrun, h0.trans (Step3.ofKeeps hk hdom)⟩
  · simp only [decide_eq_false (fun h' ↦ h4 ((toUInt64_le (by norm_num) (by omega)).mp h')),
      Bool.false_eq_true, ↓reduceIte]
    rw [show d - 3 = 0 by omega]
    exact WP.skip ⟨t, grind_zero_run t, h, Step3.refl _ _ _ _⟩

/-- Reject a zero count root. -/
def checkCount : Stmt := blk [I (.load .r11 (cw ctxWork)),
  I (.load .rax (at_ .r11 (wdisp countR.off))), I (.load .rcx (at_ .r11 (wdisp (countR.off + 1)))),
  I (.or .rax .rcx), failIf (.cmp .eq .rax (.imm 0))]

theorem checkCount_spec {c : EW} (h : CodeRel env t s) (hc : EWAt s.mem (countR.at env.work) c) :
    WP checkCount s
      (fun s' ↦ (c != 0) = true ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .rax, .rcx] s s')
      (fun s' ↦ (c != 0) = false ∧ s'.mem = s.mem ∧ RegsFrame [.r11, .rax, .rcx] s s') := by
  unfold checkCount
  rw [Region.at, EWAt, wd_wd] at hc
  refine wp_load (eval_cw h.rdi ctxWork) h.workPtr3 ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) hc.1 ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) hc.2 ?_
  refine wp_reg rfl ?_
  have hz : (c != 0) = !(c.c0 ||| c.c1 == 0) := by
    rcases c with ⟨c0, c1⟩
    have e : ((⟨c0, c1⟩ : EW) == 0) = (c0 ||| c1 == 0) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, UInt64.or_eq_zero_iff]
      constructor
      · intro h; cases h; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; rfl
    rw [bne, e]
  by_cases h0 : c.c0 ||| c.c1 = 0
  · refine wp_failIf_fail ?_ ⟨by rw [hz, h0]; rfl, rfl, by rf_tac⟩
    rw [cond_eq, rhs_imm]; rsimp; rw [h0]; rfl
  · refine wp_failIf ?_ (WP.blk_nil ⟨by rw [hz]; simp [h0], rfl, by rf_tac⟩)
    rw [cond_eq, rhs_imm]; rsimp; simpa using h0

end NativeVm.Code.P3
