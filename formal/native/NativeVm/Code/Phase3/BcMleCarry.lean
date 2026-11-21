module

public import NativeVm.Code.Phase3.BcMleBase
public import NativeVm.Code.Phase3.BcMleMath

/-!
# The bytecode's multilinear extension: one carry

`bcCarry` at stack level `l` (`rsi`): `A := S[l] + (S[l] + A)·r_l`, the coordinate `r_l` the point's
copy's element `l` (`bcCarry_spec`); it writes no memory.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code
open LeanVM.Parameters

/-- The element `x` of `E` in the words at `p`, `wd p 1`, as lanes. -/
def SAt (mem : UInt64 → Option UInt64) (p : UInt64) (x : E) : Prop :=
  mem p = some (x.limb 0).lane ∧ mem (wd p 1) = some (x.limb 1).lane

variable {env : Env} {s : QState}

/-- **One carry**: `A := (A + S) · r + S`, `S` at `rsi` (level `l` of the stack), `r` element `l` of
the point's copy; `rsi` moves to the next level, `r15` halves. -/
theorem bcCarry_spec {l c : Nat} {S : E} {r : EW} {F : QState → Prop}
    (hsi : s.reg .rsi = wd env.work (bcStW + 2 * l)) (hS : SAt s.mem (wd env.work (bcStW + 2 * l)) S)
    (hr : EWAt s.mem (wd env.work (bcPtW + 2 * l)) r) (h15 : s.reg .r15 = c.toUInt64)
    (hc : c < 2 ^ 64) :
    WP bcCarry s (fun s' ↦ s'.mem = s.mem ∧
      eOf (s'.reg .r9) (s'.reg .r10) = (eOf (s.reg .r9) (s.reg .r10) + S) * r.toE + S ∧
      s'.reg .rsi = wd env.work (bcStW + 2 * (l + 1)) ∧ s'.reg .r15 = (c / 2).toUInt64 ∧
      RegsFrame [.rax, .rbx, .rcx, .rdx, .r8, .r9, .r10, .r11, .r12, .rsi, .r15] s s') F := by
  obtain ⟨S0, S1⟩ := hS
  obtain ⟨r0, r1⟩ := hr
  rw [wd_wd] at S1 r1
  unfold bcCarry
  refine wp_load (eval_wd hsi 72) (by rw [show bcStW + 2 * l + 72 = bcPtW + 2 * l by unfold bcStW bcPtW; omega]; exact r0) ?_
  refine wp_load (eval_wd (by rsimp; exact hsi) 73)
    (by rsimp; rw [show bcStW + 2 * l + 73 = bcPtW + 2 * l + 1 by unfold bcStW bcPtW; omega]; exact r1) ?_
  refine wp_load (bc_eval0 (by rsimp; exact hsi)) (by rsimp; exact S0) ?_
  fstep
  refine wp_load (bc_eval8 (by rsimp; exact hsi)) (by rsimp; exact S1) ?_
  fstep
  refine WP.then (emul_spec _) fun t ⟨e1, e2, e3⟩ ↦ ?_
  rsimp at e1 e2
  have tsi : t.reg .rsi = wd env.work (bcStW + 2 * l) := by
    rw [e3 .rsi (by decide)]; rsimp; exact hsi
  have t15 : t.reg .r15 = c.toUInt64 := by rw [e3 .r15 (by decide)]; rsimp; exact h15
  refine wp_load (bc_eval0 tsi) (by rw [e2]; exact S0) ?_
  fstep
  refine wp_load (bc_eval8 (by rsimp; exact tsi)) (by rsimp; rw [e2]; exact S1) ?_
  fstep; fstep; fstep; fdone
  refine ⟨e2, ?_, ?_, ?_, ?_⟩
  · rw [eOf_add, e1, eOf_add, eOf_lanes, ← eOf_lanes S]
    rfl
  · rw [tsi, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]
    congr 1
  · rw [t15]
    exact Field.shr1_toUInt64 hc
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11⟩ := hq
    simp only [QState.setReg_reg, q1, q6, q7, q10, q11, ↓reduceIte]
    rw [e3 q (by simp [eRegs, q1, q2, q3, q4, q5, q6, q7])]
    simp only [QState.setReg_reg, q1, q6, q7, q8, q9, ↓reduceIte]

end NativeVm.Code.P3
