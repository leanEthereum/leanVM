module

public import NativeVm.Code.Phase4.Kernels

/-!
# Stepping phase 4's straight-line code

Phase 4's code addresses the working area through registers holding `wd w j` (`w` the area's
address) and displacements `wdisp k` (`wa r k`), so every address is `wd w (j + k)`. `wst` runs
the instruction at the head of a block: a load or a store through such a register
(`wp_ldA`, `wp_stA`), `lea` and `addi` of `wdisp k` (`wp_leaA`, `wp_addiA`), a load of the area's
address from the context (`wp_ldCtx`), or any register instruction (`fstep`). Memory reads through
the stores so far reduce by `memw` (`mem_setMem_ne`, `mem_setMem_eq`, the offsets compared by
`omega`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field

variable {s : QState} {P E : QState → Prop} {xs : List Stmt}

/-- The bound of an offset `wd` keeps apart. -/
abbrev wdB : Nat := 2305843009213693952

theorem wdB_eq : wdB = 2 ^ 61 := rfl

theorem mem_setMem_ne {w : UInt64} {j k : Nat} (v : UInt64) (h : j ≠ k) (hj : j < 2305843009213693952)
    (hk : k < 2305843009213693952) : (s.setMem (wd w k) v).mem (wd w j) = s.mem (wd w j) :=
  mem_setMem_wd v hj hk h

theorem mem_setMem_eq {w : UInt64} {j k : Nat} (v : UInt64) (h : j = k) :
    (s.setMem (wd w k) v).mem (wd w j) = some v := by
  subst h; exact mem_setMem_self v

theorem isSome_setMem (a v b : UInt64) (h : (s.mem b).isSome) : ((s.setMem a v).mem b).isSome := by
  rw [QState.setMem_mem]; split <;> simp_all

theorem wp_leaA {d r : Reg64} {w : UInt64} {j k : Nat} (hr : s.reg r = wd w j)
    (h : WP (blk xs) (s.setReg d (wd w (j + k))) P E) : WP (blk (I (.lea d (wa r k)) :: xs)) s P E :=
  wp_reg (by simp only [QInstr.step]; rw [eval_wd hr k]) h

theorem wp_addiA {r : Reg64} {w : UInt64} {j k : Nat} (hr : s.reg r = wd w j)
    (h : WP (blk xs) (s.setReg r (wd w (j + k))) P E) :
    WP (blk (I (.addi r (wdisp k)) :: xs)) s P E :=
  wp_reg (by simp only [QInstr.step]; rw [hr, wdisp_toUInt64, wd_add]) h

/-- The working area's address, from the context. -/
theorem wp_ldCtx {env : Env} {d : Reg64} (hrdi : s.reg .rdi = env.ctx)
    (hw : s.mem (wd env.ctx ctxWork) = some (wd env.work 0))
    (h : WP (blk xs) (s.setReg d (wd env.work 0)) P E) :
    WP (blk (I (.load d (cw ctxWork)) :: xs)) s P E :=
  wp_load (eval_cw hrdi _) hw h

theorem wd_zero_eq (w : UInt64) : wd w 0 = w := wd_zero w

/-- `n` elements of two words from `wd w j`, as a byte offset `n · 16` added. -/
theorem shl4_add {w : UInt64} {j n : Nat} :
    n.toUInt64 <<< (4 : Nat).toUInt64 + wd w j = wd w (j + 2 * n) := by
  rw [toUInt64_shl _ _ (by omega), ← wd_add, UInt64.add_comm]
  congr 2
  omega

/-- The discharger of `memw`. -/
macro "p4omega" : tactic => `(tactic| first
  | omega
  | ((simp only [oL, oB, oBP, oBT, oE, oC, oS, oXP, oCLM, oFIN, oMSG, oPT, oWT, oCV, oTOT, oSUM,
      oNR, oTIX, oFPTR, oEPTR, oWID, fW, formsStride, eS, evOff, cW, cV]) <;> omega))

/-- Offsets in normal form: the offsets' names unfolded, `wd` of `wd` merged, literals summed. -/
macro "wnorm" : tactic => `(tactic| (
  simp only [wd_wd, Nat.add_assoc, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero,
    Nat.reduceAdd, Nat.reduceMul, oL, oB, oBP, oBT, oE, oC, oS, oXP, oCLM, oFIN, oMSG, oPT, oWT,
    oCV, oTOT, oSUM, oNR, oTIX, oFPTR, oEPTR, oWID, fW, formsStride, eS, evOff, cW, cV]))

/-- `wnorm` at hypotheses. -/
macro "wnorm" " at" h:(ppSpace colGt ident)+ : tactic => `(tactic| (
  simp only [wd_wd, Nat.add_assoc, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero,
    Nat.reduceAdd, Nat.reduceMul, oL, oB, oBP, oBT, oE, oC, oS, oXP, oCLM, oFIN, oMSG, oPT, oWT,
    oCV, oTOT, oSUM, oNR, oTIX, oFPTR, oEPTR, oWID, fW, formsStride, eS, evOff, cW, cV] at $h*))

/-- Reduce a memory read through register updates and stores to the working area. -/
macro "memw" : tactic => `(tactic| (
  simp (disch := p4omega) only [QState.setReg_mem, QState.setMem_reg, mem_setMem_eq, mem_setMem_ne,
    QState.setReg_reg, reduceCtorEq, ite_true, ite_false, wd_wd, Nat.add_assoc, Nat.mul_zero, Nat.mul_one, Nat.zero_add, Nat.add_zero, Nat.reduceAdd,
    Nat.reduceMul, oL, oB, oBP, oBT, oE, oC, oS, oXP, oCLM, oFIN, oMSG, oPT, oWT,
    oCV, oTOT, oSUM, oNR, oTIX, oFPTR, oEPTR, oWID, fW, formsStride, eS, evOff, cW, cV]))

/-- A register's value through register updates. -/
macro "regw" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | (rsimp <;> first | with_reducible rfl | with_reducible assumption))

/-- A word's value, for a load. -/
macro "valw" : tactic => `(tactic| (
  try memw
  first | with_reducible assumption | with_reducible exact congrArg some rfl))

/-- A word exists, for a store. -/
macro "somew" : tactic => `(tactic| (
  repeat (first | with_reducible apply isSome_setMem | rw [QState.setReg_mem])
  first
    | with_reducible assumption
    | (apply_assumption <;> p4omega)))

/-- Peel register updates and stores off a `RegsFrame` goal. -/
macro "rfw" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine rf_setMem ?_ _ _
    | with_reducible refine rf_setReg ?_ (by decide) _)
  first | with_reducible exact rf_refl _ _ | assumption))

/-- A word's value at the end of a block. -/
macro "fin_w" : tactic => `(tactic| (
  (try simp only [List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ])
  memw <;> first | with_reducible rfl | with_reducible assumption))

/-- The end of a block. -/
macro "wdone" : tactic => `(tactic| apply WP.blk_nil)

/-- An element at `wd w j` from its two words. -/
theorem EWAt.of {mem : UInt64 → Option UInt64} {w : UInt64} {j : Nat} {x : EW}
    (h0 : mem (wd w j) = some x.c0) (h1 : mem (wd w (j + 1)) = some x.c1) : EWAt mem (wd w j) x :=
  ⟨h0, by rw [wd_wd]; exact h1⟩

/-- An instruction on registers only. -/
def isRegOp : QInstr → Bool
  | .load _ _ | .store _ _ | .storei _ _ | .lea _ _ => false
  | _ => true

/-- A guard: the instruction at the head is on registers only. -/
theorem wp_regGuard {i : QInstr} (_ : isRegOp i = true) (h : WP (blk (I i :: xs)) s P E) :
    WP (blk (I i :: xs)) s P E := h

/-- A load of the working area's address from the context. -/
def isCtxLoad : QInstr → Bool
  | .load _ a => a.base == .rdi
  | _ => false

theorem wp_ctxGuard {i : QInstr} (_ : isCtxLoad i = true) (h : WP (blk (I i :: xs)) s P E) :
    WP (blk (I i :: xs)) s P E := h

/-- The context's word `ctxWork` through stores to the working area. -/
theorem mem_setMem_ctx {env : Env} (h4 : Env4 env) {k : Nat} (hk : k < 85438) (v : UInt64) :
    (s.setMem (wd env.work k) v).mem (wd env.ctx ctxWork) = s.mem (wd env.ctx ctxWork) := by
  rw [QState.setMem_mem, ite_eq_right]
  exact (h4.ctxNe k ctxWork (by rw [dataEnd_val]; exact hk) (by decide)).symm

/-- **One instruction** at the head of a block. -/
macro "wst" : tactic => `(tactic| first
  | (refine wp_ctxGuard (by decide) ?_
     refine wp_ldCtx (by regw) (by
       (try simp (disch := p4omega) only [QState.setReg_mem, QState.setMem_reg,
         mem_setMem_ctx (by assumption)])
       with_reducible assumption) ?_)
  | (refine wp_ldA (by regw) (by valw) ?_)
  | (refine wp_stA (by regw) (by somew) ?_)
  | (refine wp_stiA (by regw) (by somew) ?_)
  | (refine wp_leaA (by regw) ?_)
  | (refine wp_addiA (by regw) ?_)
  | (refine wp_regGuard (by decide) ?_; fstep))


/-! ## What straight-line code writes -/

/-- `s'` is `s` but at the working area's words `W`. -/
def Wr (w : UInt64) (W : Nat → Prop) (s s' : QState) : Prop :=
  ∀ a, (∀ k, W k → a ≠ wd w k) → s'.mem a = s.mem a

theorem Wr.refl (w : UInt64) (W : Nat → Prop) (s : QState) : Wr w W s s := fun _ _ ↦ rfl

theorem Wr.trans {w : UInt64} {W : Nat → Prop} {s₁ s₂ s₃ : QState} (h : Wr w W s₁ s₂)
    (h' : Wr w W s₂ s₃) : Wr w W s₁ s₃ := fun a ha ↦ (h' a ha).trans (h a ha)

theorem Wr.mono {w : UInt64} {W V : Nat → Prop} {s s' : QState} (h : Wr w W s s')
    (hWV : ∀ k, W k → V k) : Wr w V s s' := fun a ha ↦ h a fun k hk ↦ ha k (hWV k hk)

theorem Wr.setMem {w : UInt64} {W : Nat → Prop} {s s' : QState} (h : Wr w W s s') {k : Nat}
    (hk : W k) (v : UInt64) : Wr w W s (s'.setMem (wd w k) v) := fun a ha ↦ by
  rw [QState.setMem_mem, ite_eq_right (ha k hk)]
  exact h a ha

theorem Wr.setReg {w : UInt64} {W : Nat → Prop} {s s' : QState} (h : Wr w W s s') (r : Reg64)
    (v : UInt64) : Wr w W s (s'.setReg r v) := h

/-- A word outside `W` is kept. -/
theorem Wr.word {w : UInt64} {W : Nat → Prop} {s s' : QState} (h : Wr w W s s') {j : Nat}
    (hj : j < 2305843009213693952) (hW : ∀ k, W k → j ≠ k ∧ k < 2305843009213693952) : s'.mem (wd w j) = s.mem (wd w j) :=
  h _ fun k hk e ↦ (hW k hk).1 ((wd_inj hj (hW k hk).2).mp e)

/-- Peel stores and register updates off a `Wr` goal. -/
macro "wr_tac" : tactic => `(tactic| (
  repeat (first
    | with_reducible refine Wr.setReg ?_ _ _
    | with_reducible refine Wr.setMem ?_ (by p4omega) _)
  try exact Wr.refl _ _ _))

end NativeVm.Code.P4
