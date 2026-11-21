module

public import NativeVm.Code.Phase3.ShareBase

/-!
# The bytecode share: a round after its challenge

`shRoundTail`: from the challenge `x` in `A`, the claim moves to the round polynomial's value at `x`
(`sh_poly`), `r14` to the next challenge's words, `r13` counts down (`shRest_spec`). It writes the
claim's words alone.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code

variable {env : Env} {inp : Input} {s : QState}

theorem ew_eta {x : EW} {a b : UInt64} (h : eOf a b = x.toE) : (⟨a, b⟩ : EW) = x := by
  obtain ⟨rfl, rfl⟩ := eOf_eq_toE.mp h
  rfl

theorem eOf_toE (x : EW) : eOf x.c0 x.c1 = x.toE := rfl

theorem wrote_of_mem {ws : List Region} {s s' : QState} (hm : s'.mem = s.mem)
    (hr : s'.reg .rdi = s.reg .rdi) : Wrote env ws s s' :=
  ⟨hr, fun _ _ ↦ by rw [hm], fun _ ↦ by rw [hm]⟩

/-- **The round's tail.** -/
theorem shRest_spec {k : Nat} {x cl c tt : EW} {P F : QState → Prop}
    (hrdi : s.reg .rdi = env.ctx) (hwk : s.mem (wd env.ctx ctxWork) = some env.work)
    (hi : Inputs env inp s.mem) (h9 : s.reg .r9 = x.c0) (h10 : s.reg .r10 = x.c1)
    (h13 : s.reg .r13 = (4 - k).toUInt64) (h14 : s.reg .r14 = wd env.work (slotR.off + 2 * k))
    (hk : k < 4) (hcl : EWAt s.mem (wd env.work shClaimW) cl)
    (hc : EWAt s.mem (wd env.work shConstW) c) (htt : EWAt s.mem (wd env.work shTailW) tt)
    (hP : ∀ s', Wrote env [shClaimR] s s' → s'.reg .rdi = s.reg .rdi →
      EWAt s'.mem (wd env.work shClaimW) (polyEval #[c, cl + sumE #[tt], tt] x) →
      s'.reg .r13 = (4 - (k + 1)).toUInt64 →
      s'.reg .r14 = wd env.work (slotR.off + 2 * (k + 1)) → P s') :
    WP (blk shRoundTail) s P F := by
  obtain ⟨c0, c1⟩ := hc
  obtain ⟨l0, l1⟩ := hcl
  obtain ⟨t0, t1⟩ := htt
  rw [wd_wd] at c1 l1 t1
  unfold shRoundTail
  fstep; fstep
  refine wp_load (eval_cw (by rsimp; exact hrdi) _) (by rsimp; exact hwk) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact t0) ?_
  refine wp_load (eval_work (env := env) (by rsimp) _) (by rsimp; exact t1) ?_
  refine WP.then (emul_spec _) fun u1 ⟨a1, m1, f1⟩ ↦ ?_
  rsimp at a1
  have u1si : u1.reg .rsi = env.work := by rw [f1 .rsi (by decide)]; rsimp
  have u111 : u1.reg .r11 = x.c0 := by rw [f1 .r11 (by decide)]; rsimp; exact h9
  have u112 : u1.reg .r12 = x.c1 := by rw [f1 .r12 (by decide)]; rsimp; exact h10
  refine wp_load (eval_work u1si _) (by rw [m1]; exact l0) ?_
  fstep
  refine wp_load (eval_work (by rsimp; exact u1si) _) (by rsimp; rw [m1]; exact l1) ?_
  fstep
  refine wp_load (eval_work (by rsimp; exact u1si) _) (by rsimp; rw [m1]; exact t0) ?_
  fstep
  refine wp_load (eval_work (by rsimp; exact u1si) _) (by rsimp; rw [m1]; exact t1) ?_
  fstep
  refine WP.then (emul_spec _) fun u2 ⟨a2, m2, f2⟩ ↦ ?_
  rsimp at a2 m2
  have u2si : u2.reg .rsi = env.work := by rw [f2 .rsi (by decide)]; rsimp; exact u1si
  have u2r : ∀ q, q = .rdi ∨ q = .r13 ∨ q = .r14 → u2.reg q = s.reg q := by
    rintro q (rfl | rfl | rfl) <;>
      (rw [f2 _ (by decide)]; rsimp; rw [f1 _ (by decide)]; rsimp)
  refine wp_load (eval_work u2si _) (by rw [m2, m1]; exact c0) ?_
  fstep
  refine wp_load (eval_work (by rsimp; exact u2si) _) (by rsimp; rw [m2, m1]; exact c1) ?_
  fstep
  have hi2 : Inputs env inp u2.mem := by rw [m2, m1]; exact hi
  refine sh_storePair (r := shClaimR) (a := shClaimW) (by sh_reg) le_rfl (by sh_reg)
    (eval_work (by rsimp; exact u2si) _) (eval_work (by rsimp; exact u2si) _) hi2
    fun s' hw he hreg ↦ ?_
  fstep; fstep; fdone
  have hE : eOf (u2.reg .r9 ^^^ c.c0) (u2.reg .r10 ^^^ c.c1) =
      (polyEval #[c, cl + sumE #[tt], tt] x).toE := by
    rw [eOf_add, a2, eOf_add, eOf_add, a1, sh_poly, u111, u112, h9, h10]
    simp only [eOf_toE]
  rsimp at he hreg
  refine hP _ ?_ ?_ ?_ ?_ ?_
  · refine ((wrote_of_mem ?_ ?_).trans hw).setReg (r := .r14) (by decide) _
      |>.setReg (r := .r13) (by decide) _
    · rsimp; rw [m2, m1]; rsimp
    · rsimp; exact u2r _ (.inl rfl)
  · rsimp; rw [hreg]; rsimp; exact u2r _ (.inl rfl)
  · rsimp; rw [ew_eta hE] at he; exact he
  · rsimp; rw [hreg]; rsimp
    rw [u2r _ (.inr (.inl rfl)), h13, show 4 - k = (4 - (k + 1)) + 1 by omega, toUInt64_succ_sub]
  · rsimp; rw [hreg]; rsimp
    rw [u2r _ (.inr (.inr rfl)), h14, show (16 : UInt64) = (8 * 2 : Nat).toUInt64 from rfl, wd_add]
    congr 1

end NativeVm.Code.P3
