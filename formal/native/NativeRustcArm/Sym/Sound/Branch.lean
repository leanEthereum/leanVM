module

public import NativeRustcArm.Sym.Operand

/-!
# Branches, `ADRP` and `NOP` are sound

`OpOk` for `B`, `B.cond`, `CBZ`/`CBNZ`, `TBZ`/`TBNZ` (a conditional exit on Kraken's condition),
`BL` (the return address in X30, which the symbolic state forgets), `RET` (to X30), `ADRP` of a
label, possibly plus a constant, and `NOP`.
-/

namespace NativeRustcArm.Sym

public section

variable [Labels] {env : Env} {S S' : SState} {x : Exit} {m : MachineData} {w : RegWidth}

/-- A conditional branch on `b`, which the symbolic condition `c` is. -/
theorem branch_ok {c : SBool} {t : ConstExpr} (b : Bool) (hb : c.eval env = b) (hm : Match env S m)
    (h : Step.branch c t S = some (S', x)) (p : Std.Rco Int64) :
    (if b then Effects.done ⟨m, t.evalBranchTarget p⟩ else Effects.done ⟨m, p.upper⟩).All
      (fun st => Match env S' st.data ∧ PcOk env x p.upper st) := by
  simp only [Step.branch, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨l, hl, rfl, rfl⟩ := h
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    refine ⟨hm, ?_⟩ <;> simp only [PcOk, hb, Bool.false_eq_true, ite_false, ite_true, target_spec hl p]

theorem ok_B (t : ConstExpr) : OpOk env (.B t) := by
  intro S S' x m p _ hm h
  change (do let l ← target t; some (S, Exit.jump l)) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨l, hl, rfl, rfl⟩ := h
  exact (show (Effects.done ⟨m, t.evalBranchTarget p⟩).All _ from ⟨hm, target_spec hl p⟩)

theorem ok_B_cond (cond : CondCode) (t : ConstExpr) : OpOk env (.B_cond cond t) := by
  intro S S' x m p _ hm h
  change (do let f ← S.flags; Step.branch (condSym cond f) t S) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨f, hf, h⟩ := h
  exact branch_ok (cond.interp m.status) (by rw [eval_condSym, hm.flagsEq hf]) hm h p

theorem ok_CBZ (r : RegOrZr w) (t : ConstExpr) : OpOk env (.CBZ r t) := by
  intro S S' x m p _ hm h
  change (do let a ← S.getZr r; Step.branch (mkCmp .eq w a (.lit 0)) t S) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  exact branch_ok (m.regs.getRegOrZr r == 0) (by
    rw [eval_mkCmp, hm.getZr ha]
    simp only [CmpOp.apply, Sym.eval, low_zero]
    rfl) hm h p

theorem ok_CBNZ (r : RegOrZr w) (t : ConstExpr) : OpOk env (.CBNZ r t) := by
  intro S S' x m p _ hm h
  change (do let a ← S.getZr r; Step.branch (mkNot (mkCmp .eq w a (.lit 0))) t S) =
    some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  exact branch_ok (m.regs.getRegOrZr r != 0) (by
    rw [eval_mkNot, eval_mkCmp, hm.getZr ha]
    simp only [CmpOp.apply, Sym.eval, low_zero]
    rfl) hm h p

theorem ok_TBZ (r : RegOrZr w) (bit : Nat) (t : ConstExpr) : OpOk env (.TBZ r bit t) := by
  intro S S' x m p _ hm h
  change (do let a ← S.getZr r; Step.branch (mkNot (mkBit w a bit)) t S) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  exact branch_ok ((m.regs.getRegOrZr r).getLsbD bit == false) (by
    rw [eval_mkNot, eval_mkBit, hm.getZr ha]
    cases (low w (a.eval env)).getLsbD bit <;> rfl) hm h p

theorem ok_TBNZ (r : RegOrZr w) (bit : Nat) (t : ConstExpr) : OpOk env (.TBNZ r bit t) := by
  intro S S' x m p _ hm h
  change (do let a ← S.getZr r; Step.branch (mkBit w a bit) t S) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, h⟩ := h
  exact branch_ok ((m.regs.getRegOrZr r).getLsbD bit == true) (by
    rw [eval_mkBit, hm.getZr ha]
    cases (low w (a.eval env)).getLsbD bit <;> rfl) hm h p

theorem ok_BL (t : ConstExpr) : OpOk env (.BL t) := by
  intro S S' x m p _ hm h
  change (do let l ← target t; some (S.setReg .X30 none, Exit.call l)) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨l, hl, rfl, rfl⟩ := h
  exact (show (Effects.done ⟨{ m with regs := (m.regs.setRegOrZr RegOrZr.X30
      (BitVec.ofInt 64 p.upper.toInt)) }, t.evalBranchTarget p⟩).All _ from
    ⟨hm.setX .X30 (fun _ h => nomatch h), target_spec hl p, retOf_bl _ _⟩)

theorem ok_RET (r : RegOrZr .W64) : OpOk env (.RET r) := by
  intro S S' x m p _ hm h
  obtain ⟨b, w'⟩ := r
  cases b with
  | XZR => cases h
  | reg r =>
    cases r <;> try cases h
    exact (show (Effects.done ⟨m, Int64.ofInt (low .W64 m.regs.X30.toBitVec).toInt⟩).All _ from
      ⟨hm, by simp only [PcOk, retOf, low_W64]⟩)

theorem ok_ADRP (dst : RegOrZr .W64) (t : ConstExpr) : OpOk env (.ADRP dst t) := by
  intro S S' x m p _ hm h
  change (do let a ← labelAddr t; fall (S.setZr dst (.bin .and .W64 a (.lit pageMask)))) =
    some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a, ha, rfl, rfl⟩ := h
  have hv : (Sym.bin .and .W64 a (.lit pageMask)).eval env =
      ext .W64 (BitVec.ofInt 64 (t.interp p).toInt &&& ~~~0xFFF#64) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, ofInt_toInt64,
      labelAddr_spec (env := env) ha p]
    rfl
  cases t with
  | label l => exact done_fall (hm.setZr dst hv)
  | add t₁ t₂ => exact done_fall (hm.setZr dst hv)
  | _ => cases ha

theorem ok_NOP : OpOk env (.NOP : Operation w) :=
  fun _ _ _ _ _ _ hm h => by
    cases h
    exact done_fall hm

end

end NativeRustcArm.Sym
