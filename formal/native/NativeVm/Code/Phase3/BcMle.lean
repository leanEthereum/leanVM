module

public import NativeVm.Code.Phase3.BcMleStream

/-!
# The bytecode's multilinear extension: `computedBytecodeValue`

`bc_spec`: `bcCode` checks `computedBytecodeValue inp.bytecode point' value`,
`point' = point[0 .. logBytecode) ++ slot`. The extension is the fold tree's root over the first
`2^|point'|` words when the bytecode has that many and `0` otherwise (`multilinearEval_eq_node`);
`bcPrep`, then the branch on the bytecode's size, then the stream (`bcStream_spec`), then the check.
The code writes `tmpR` alone and runs no transcript step.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code NativeVm.Equiv
open LeanVM.Parameters
open LeanVM.Protocol.Verifier (busBits)

variable {env : Env} {inp : Input} {t : TState} {s : QState}

/-- The extension at `point'` through `toE`: the fold tree's root, or `0`. -/
theorem bc_mle_toE (bc : Array UInt64) (pt : Array EW) :
    (multilinearEval (bc.map EW.ofK) pt).toE =
      if 2 ^ pt.size ≤ bc.size then bcNode (bcL bc) (pt.toList.map EW.toE) pt.size 0 else 0 := by
  rw [toE_multilinearEval, ← bcL, multilinearEval_eq_node]
  simp [bcL]

theorem bc_check_iff {x v : EW} {a b : UInt64} (h : eOf a b = x.toE) :
    (x == v) = true ↔ a = v.c0 ∧ b = v.c1 := by
  obtain ⟨rfl, rfl⟩ := eOf_eq_toE.mp h
  rw [beq_iff_eq]
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; cases x; cases v; simp_all

/-- **`computedBytecodeValue`**. -/
theorem bc_spec {layout : LayoutW} {rate : Nat}
    {point slot : Array EW} {value : EW} (h : CodeRel env t s) (hi : Inputs env inp s.mem)
    (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hdw : NatAt s.mem (depthR.at env.work) point.size) (hps : point.size < 64)
    (hp : EWArr s.mem (pointR.at env.work) point)
    (hs : EWArr s.mem (slotR.at env.work) slot) (hss : slot.size = busBits)
    (hv : EWAt s.mem (valueR.at env.work) value) :
    WP bcCode s
      (fun s' ↦ ∃ t', (computedBytecodeValue inp.bytecode
          (point.extract 0 layout.logBytecode ++ slot) value).run t = some ((), t') ∧
        CodeRel env t' s' ∧ Step3 env allRegs [tmpR] s s')
      (fun s' ↦ (computedBytecodeValue inp.bytecode
          (point.extract 0 layout.logBytecode ++ slot) value).run t = none ∧
        Step3 env allRegs [tmpR] s s') := by
  set pt := point.extract 0 layout.logBytecode ++ slot with hpt_def
  have hww := bc_work_le hi
  have hrdi := h.rdi
  have hwk := h.workPtr3
  have hlb : NatAt s.mem (wd env.work (layoutR.off + 1)) layout.logBytecode := by
    have := hl.logBytecode; rwa [Region.at, wd_wd] at this
  have hss4 : slot.size = 4 := hss
  have hptsz : pt.size = min layout.logBytecode point.size + 4 := by
    simp [hpt_def, hss4]
  have hlb30 := hl.logBytecodeBound
  have hm34 : pt.size ≤ 34 := by rw [hptsz]; omega
  have hok : ∀ r ∈ [tmpR], Ok3 r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ok3_sreg (by decide)
  have hrun : ∀ b : Bool, (Model.require b).run t = if b then some ((), t) else none :=
    fun b ↦ Refines.require_run b t
  have hmle := bc_mle_toE inp.bytecode pt
  unfold bcCode computedBytecodeValue
  refine wp_then (bcPrep_spec (Wrote.refl env [tmpR] s) hi hrdi hwk hlb hlb30 hdw hps hp hs hss4)
    fun s1 ⟨w1, r14, pt1⟩ ↦ ?_
  have r1 : s1.reg .rdi = env.ctx := w1.rdi.trans hrdi
  refine wp_load (eval_cw r1 _) (by rw [bc_ctx w1 hi (by lay_omega)]; exact hi.bcLen.2) ?_
  apply WP.blk_cons
  apply WP.ite
  rw [cond_ltu, rhs_reg]
  rsimp
  have hp64 : 2 ^ pt.size < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp only [r14]
  -- after the branch: `A` is the extension, the run wrote only `tmpR`
  suffices H : ∀ s2, Wrote env [tmpR] s s2 →
      eOf (s2.reg .r9) (s2.reg .r10) = (multilinearEval (inp.bytecode.map EW.ofK) pt).toE →
      WP (blk [bcCheck]) s2
        (fun s' ↦ ∃ t', (Model.require (multilinearEval (inp.bytecode.map EW.ofK) pt == value)).run t =
          some ((), t') ∧ CodeRel env t' s' ∧ Step3 env allRegs [tmpR] s s')
        (fun s' ↦ (Model.require (multilinearEval (inp.bytecode.map EW.ofK) pt == value)).run t =
          none ∧ Step3 env allRegs [tmpR] s s') by
    split
    · rename_i hlt
      refine wp_reg rfl (wp_reg rfl (WP.blk_nil (H _ ?_ ?_)))
      · exact w1.setReg (r := .rbx) (by decide) _ |>.setReg (r := .r9) (by decide) _
          |>.setReg (r := .r10) (by decide) _
      · have hlt' : ¬ 2 ^ pt.size ≤ inp.bytecode.size := by
          have := (toUInt64_lt hi.bcLen.1 hp64).mp (of_decide_eq_true hlt)
          omega
        rsimp
        simp only [hmle, hlt', ↓reduceIte, eOf_zero]
    · rename_i hge
      have hge' : 2 ^ pt.size ≤ inp.bytecode.size := by
        by_contra hc
        exact hge (decide_eq_true ((toUInt64_lt hi.bcLen.1 hp64).mpr (by omega)))
      refine WP.mono (bcStream_spec (w1.setReg (r := .rbx) (by decide) _) hi hrdi hwk hlb hdw hptsz
        hm34 hge' (by rsimp; exact r14) (by rsimp; exact pt1))
        (fun s2 ⟨w2, v2⟩ ↦ H s2 w2 (by simp only [v2, hmle, hge', ↓reduceIte])) (fun _ h ↦ h)
  intro s2 w2 v2
  have r2 : s2.reg .rdi = env.ctx := w2.rdi.trans hrdi
  have hb := bc_check_iff (v := value) v2
  obtain ⟨hv0, hv1⟩ := hv
  rw [Region.at] at hv0 hv1
  rw [wd_wd] at hv1
  have hv0' := (bc_out w2 (k := valueR.off) (by bc_omega) (by bc_omega)).trans hv0
  have hv1' := (bc_out w2 (k := valueR.off + 1) (by bc_omega) (by bc_omega)).trans hv1
  show WP bcCheck s2 _ _
  unfold bcCheck
  refine wp_load (eval_cw r2 _) (by rw [bc_ctx w2 hi (by lay_omega)]; exact hwk) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact hv0') ?_
  have wA : ∀ v, Wrote env [tmpR] s ((s2.setReg .r11 env.work).setReg .rax v) := fun v ↦
    w2.setReg (r := .r11) (by decide) _ |>.setReg (r := .rax) (by decide) _
  by_cases h0 : s2.reg .r9 = value.c0
  · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ?_
    refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact hv1') ?_
    by_cases h1 : s2.reg .r10 = value.c1
    · refine wp_failIf (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) (WP.blk_nil ⟨t, ?_, ?_, ?_⟩)
      · rw [hrun, hb.mpr ⟨h0, h1⟩]; rfl
      · exact h.wrote3 hi hok ((wA _).setReg (r := .rax) (by decide) _)
      · exact ((wA _).setReg (r := .rax) (by decide) _).step
    · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h1]) ⟨?_, ?_⟩
      · rw [hrun, show (multilinearEval (inp.bytecode.map EW.ofK) pt == value) = false from
          Bool.eq_false_iff.mpr fun e ↦ h1 (hb.mp e).2]; rfl
      · exact ((wA _).setReg (r := .rax) (by decide) _).step
  · refine wp_failIf_fail (by rw [cond_ne, rhs_reg]; rsimp; simp [h0]) ⟨?_, ?_⟩
    · rw [hrun, show (multilinearEval (inp.bytecode.map EW.ofK) pt == value) = false from
        Bool.eq_false_iff.mpr fun e ↦ h0 (hb.mp e).1]; rfl
    · exact (wA _).step

end NativeVm.Code.P3
