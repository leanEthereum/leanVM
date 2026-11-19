module

public import NativeVm.Code.Phase3.BcMleWord
public import NativeVm.Code.Phase3.BcMlePrep

/-!
# The bytecode's multilinear extension: the stream

`bcStream` runs `bcWord` over the bytecode's first `2^m` words, `m = |point'|`, then loads the
stack's level `m`: the fold tree's root (`bcStream_spec`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code
open LeanVM.Parameters

variable {env : Env} {inp : Input} {s0 s : QState}

/-- **The stream**: `A` is the root of the fold tree of the first `2^m` words. -/
theorem bcStream_spec {pt : Array EW} {logB d : Nat} {F : QState → Prop}
    (hw : Wrote env [tmpR] s0 s) (hi : Inputs env inp s0.mem) (hrdi : s0.reg .rdi = env.ctx)
    (hwk : s0.mem (wd env.ctx ctxWork) = some env.work)
    (hl : NatAt s0.mem (wd env.work (layoutR.off + 1)) logB)
    (hdw : NatAt s0.mem (wd env.work depthR.off) d)
    (hm : pt.size = min logB d + 4) (hm34 : pt.size ≤ 34) (hbc : 2 ^ pt.size ≤ inp.bytecode.size)
    (h14 : s.reg .r14 = (2 ^ pt.size).toUInt64) (hpt : EWArr s.mem (wd env.work bcPtW) pt) :
    WP bcStream s (fun s' ↦ Wrote env [tmpR] s0 s' ∧
      eOf (s'.reg .r9) (s'.reg .r10) =
        bcNode (bcL inp.bytecode) (pt.toList.map EW.toE) pt.size 0) F := by
  set m := pt.size with hm_def
  have hww := bc_work_le hi
  have hpm : 2 ^ m ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hm34
  unfold bcStream
  refine wp_load (eval_cw (hw.rdi.trans hrdi) _) (by rw [bc_ctx hw hi (by lay_omega)]; exact hi.bcPtr) ?_
  fstep
  apply WP.blk_cons
  apply WP.loop (fun u ↦ ∃ i ≤ 2 ^ m, Wrote env [tmpR] s0 u ∧ u.reg .r13 = wd inp.bcA i ∧
      u.reg .rbp = i.toUInt64 ∧ u.reg .r14 = (2 ^ m - i).toUInt64 ∧
      EWArr u.mem (wd env.work bcPtW) pt ∧
      BcStack u.mem env.work (bcL inp.bytecode) (pt.toList.map EW.toE) m i)
    (fun u ↦ (u.reg .r14).toNat)
  · refine ⟨0, Nat.zero_le _, hw.setReg (r := .r13) (by decide) _ |>.setReg (r := .rbp) (by decide) _,
      ?_, ?_, ?_, hpt, fun l _ hb ↦ ?_⟩ <;> rsimp
    · rw [wd_zero]
    · rfl
    · exact h14
    · rw [Nat.zero_div] at hb; exact absurd hb (by decide)
  · rintro u ⟨i, hi', uw, u13, ubp, u14, upt, ust⟩ hc
    rw [cond_ne, rhs_imm, u14, int64Zero_toUInt64, bne_iff_ne, ne_eq] at hc
    have hlt : i < 2 ^ m := by
      by_contra h'
      exact hc (by rw [show 2 ^ m - i = 0 by omega]; rfl)
    refine WP.mono (bcWord_spec uw hi hrdi hwk hm_def.symm hm34 hbc hlt u13 ubp u14 upt ust)
      (fun u' ⟨w', r13', bp', r14', pt', st'⟩ ↦ ⟨⟨i + 1, hlt, w', r13', bp', r14', pt', st'⟩, ?_⟩)
      (fun _ h ↦ h)
    rw [r14', u14, Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
    omega
  · rintro u ⟨i, hi', uw, u13, ubp, u14, upt, ust⟩ hc
    rw [cond_ne, rhs_imm, u14, int64Zero_toUInt64, bne_eq_false_iff_eq] at hc
    have hi2 : i = 2 ^ m := by
      have := toUInt64_eq_zero (show 2 ^ m - i < 2 ^ 64 by omega) hc
      omega
    subst hi2
    refine wp_then (bcMin_spec (uw.rdi.trans hrdi) (by rw [bc_ctx uw hi (by lay_omega)]; exact hwk)
      (hl.congr (bc_out uw (by bc_omega) (by bc_omega)))
      (hdw.congr (bc_out uw (by bc_omega) (by bc_omega)))) fun v ⟨vm, vax, _, vf⟩ ↦ ?_
    have vrdi : v.reg .rdi = env.ctx := (vf .rdi (by simp)).trans (uw.rdi.trans hrdi)
    have vw : Wrote env [tmpR] s0 v := ⟨vrdi.trans hrdi.symm, fun a ha ↦ by rw [vm]; exact uw.mem a ha,
      fun a ↦ by rw [vm]; exact uw.dom a⟩
    fstep; fstep
    refine wp_load (eval_cw (by rsimp; exact vrdi) _)
      (by rsimp; rw [bc_ctx vw hi (by lay_omega)]; exact hwk) ?_
    fstep; fstep
    have hv4 : v.reg .rax + 4 = m.toUInt64 := by rw [vax, hm, ← toUInt64_add]; rfl
    have h16 : m.toUInt64 * 16 = (8 * (2 * m)).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mul, Transcript.toNat_toUInt64 (by omega), Transcript.toNat_toUInt64 (by omega)]
      rw [show (16 : UInt64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega)]
      omega
    have haddr : env.work + (wdisp bcStW).toUInt64 + m.toUInt64 <<< 4 =
        wd env.work (bcStW + 2 * m) := by
      rw [Field.shl4, h16]
      exact wd_add env.work bcStW (2 * m)
    have hsi := fun (u : QState) (h : u.reg .rsi = env.work + (wdisp bcStW).toUInt64 + m.toUInt64 <<< 4) ↦
      h.trans haddr
    obtain ⟨w0, w1⟩ := ust m le_rfl (by rw [Nat.div_self (by positivity)])
    rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega)), Nat.mul_zero] at w0 w1
    rw [wd_wd] at w1
    refine wp_load (bc_eval0 (hsi _ (by rsimp; rw [hv4]))) (by rsimp; rw [vm]; exact w0) ?_
    refine wp_load (bc_eval8 (hsi _ (by rsimp; rw [hv4]))) (by rsimp; rw [vm]; exact w1) ?_
    refine WP.blk_nil ⟨?_, ?_⟩
    · exact vw.setReg (r := .rax) (by decide) _ |>.setReg (r := .rax) (by decide) _
        |>.setReg (r := .rsi) (by decide) _ |>.setReg (r := .rsi) (by decide) _
        |>.setReg (r := .rsi) (by decide) _ |>.setReg (r := .r9) (by decide) _
        |>.setReg (r := .r10) (by decide) _
    · rsimp
      exact eOf_lanes _

end NativeVm.Code.P3
