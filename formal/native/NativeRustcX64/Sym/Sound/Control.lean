module

public import NativeRustcX64.Sym.Operand

/-!
# Stack and control instructions are sound

`OpOk` for `PUSH`, `POP`, `Jcc` (a conditional exit on Kraken's condition), `JMP`, `CALL` (the
return address pushed: the environment's `ret`, which the exit's `retOf` reads back), `RET` (to
the address popped), `NOP` and alignment padding.
-/

namespace NativeRustcX64.Sym

public section

theorem relTarget_eq {t : RelRegOrMem} {l : Label} (h : relTarget t = some l) :
    t = .rel (.sub (.label l) .after_current_instruction) := by
  unfold relTarget at h
  split at h
  · cases h
    rfl
  · cases h

theorem SState.reg_setReg_of {S : SState} {r : Reg64} {u : Sym} (hu : S.reg r = some u)
    (v : Sym) : (S.setReg r (some v)).reg r = some v := by
  unfold SState.reg SState.setReg at *
  have : r.idx < S.regs.length := by
    rcases Nat.lt_or_ge r.idx S.regs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hu
      cases hu
  show ((S.regs.set r.idx (some v))[r.idx]?).getD none = some v
  rw [List.getElem?_set_self this]
  rfl

theorem SState.storeAt_reg {S S' : SState} {a u : Sym} {n : Nat} (h : S.storeAt a n u = some S')
    (r : Reg64) : S'.reg r = S.reg r := by
  unfold SState.storeAt at h
  cases hacc : S.access a n with
  | none =>
    rw [hacc] at h
    cases hs : S.slots a n with
    | none => rw [hs] at h; cases h
    | some q =>
      rw [hs] at h
      cases h
      rfl
  | some ro =>
    rw [hacc] at h
    cases h
    rfl

/-- A stack address below a value is not an indexed access. -/
theorem slots_mkSub64 (S : SState) (a : Sym) (c n : Nat) :
    S.slots (mkSub64 a (.lit (c + 1))) n = none := by
  unfold mkSub64
  split
  · rfl
  · split
    · split <;> rfl
    · rw [ite_neg (by simp)]
      split <;> rfl

theorem rel_target [Labels] (l : Label) (p : Std.Rco Int64) :
    Int64.ofBitVec
      (p.upper + (ConstExpr.sub (.label l) .after_current_instruction).interp p).toBitVec =
      Labels.label l := by
  show Int64.ofBitVec (p.upper + (Labels.label l - p.upper)).toBitVec = _
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]

variable [Labels] {env : Env} {w : Width}

omit [Labels] in
theorem asLabel_eq {v : Sym} {l : Label} (h : asLabel v = some l) : v = .label l := by
  cases v <;> cases h
  rfl

/-- An indirect target is accepted only with a proof that the operand is the label's address. -/
theorem Match.target {S : SState} {m : MachineData} (hm : Match env S m) (hwf : env.WF)
    {t : RelRegOrMem} {l : Label} (h : S.target t = some l) (p : Std.Rco Int64)
    {ret : BitVec 64 → MachineData → Effects} {post : MachineState → Prop}
    (hret : (ret (Labels.label l).toBitVec m).All post) :
    (t.interp m p ret).All post := by
  cases t with
  | rel c =>
    obtain he := relTarget_eq h
    cases he
    show (ret (p.upper + (Labels.label l - p.upper)).toBitVec m).All post
    rw [Int64.add_comm, Int64.sub_add_cancel]
    exact hret
  | reg r =>
    simp only [SState.target, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hl⟩ := h
    obtain rfl := asLabel_eq hl
    show (ret (m.regs.get r) m).All post
    rw [hm.getR hv, low_W64]
    exact hret
  | mem a =>
    simp only [SState.target, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hl⟩ := h
    obtain rfl := asLabel_eq hl
    exact hm.readRM hwf hv p hret

theorem ok_push (src : Operand w) : OpOk env (.push src) := by
  intro S S' x m p hwf hm h _
  change Step.push src S = some (S', x) at h
  simp only [Step.push, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨v, hv, sp, hsp, S₁, hS, rfl, rfl⟩ := h
  have hsp' : (mkSub64 sp (.lit w.bytes)).eval env = m.regs.get64 .rsp - w.bytesv := by
    rw [eval_mkSub64, ← hm.regs .rsp sp hsp]
    rfl
  unfold Operation.interp
  refine hm.readOp hwf hv p ?_
  exact store_All (hm.set64 .rsp fun _ h => by cases h; exact hsp') hwf hsp' hS rfl
    fun _ hm' => done_fall hm'

theorem ok_pop (dst : Dst w) : OpOk env (.pop dst) := by
  intro S S' x m p hwf hm h _
  change Step.pop dst S = some (S', x) at h
  simp only [Step.pop, Option.bind_eq_bind, Option.bind_eq_some_iff, fall, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨sp, hsp, v, hv, S₁, hS, rfl, rfl⟩ := h
  unfold Operation.interp
  refine load_All hm hwf (hm.regs .rsp sp hsp).symm hv fun hlt => ?_
  have hm₁ := hm.set64 .rsp (v := some (mkAdd64 sp (.lit w.bytes)))
    (x := m.regs.get64 .rsp + w.bytesv) fun _ h => by
      cases h
      rw [eval_mkAdd64, ← hm.regs .rsp sp hsp]
      rfl
  exact hm₁.writeDst hwf hS (ext_low_of_lt w hlt).symm p fun _ hm' => done_fall hm'

theorem ok_jcc (cc : CondCode) (l : Label) : OpOk env (.jcc cc l : Operation w) := by
  intro S S' x m p hwf hm h _
  change (do let c ← condSym cc S.flags; some (S, Exit.cond c l)) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨c, hc, rfl, rfl⟩ := h
  have := eval_condSym env hm.flags hc
  unfold Operation.interp
  show Effects.All _ (if cc.interp m.status then _ else _)
  split
  · exact ⟨hm, by simp only [PcOk, *, ite_true]⟩
  · exact ⟨hm, by simp only [PcOk, *, ite_false, Bool.false_eq_true]⟩

theorem ok_jmp (t : RelRegOrMem) : OpOk env (.jmp t : Operation w) := by
  intro S S' x m p hwf hm h _
  change (do let l ← S.target t; some (S, Exit.jump l)) = some (S', x) at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨l, hl, rfl, rfl⟩ := h
  unfold Operation.interp
  exact hm.target hwf hl p ⟨hm, Int64.ofBitVec_toBitVec _⟩

theorem ok_call (t : RelRegOrMem) : OpOk env (.call t : Operation w) := by
  intro S S' x m p hwf hm h hret
  change Step.call t S = some (S', x) at h
  simp only [Step.call, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨l, hl, sp, hsp, S₁, hS, rfl, rfl⟩ := h
  have hr := hret l rfl
  have hsp' : (mkSub64 sp (.lit 8)).eval env = m.regs.get64 .rsp - Width.W64.bytesv := by
    rw [eval_mkSub64, ← hm.regs .rsp sp hsp]
    rfl
  unfold Operation.interp
  refine hm.target hwf hl p ?_
  refine store_All (hm.set64 .rsp fun _ h => by cases h; exact hsp') hwf hsp' hS
    (x := p.upper.toBitVec) (by rw [low_W64]; exact hr) fun m₂ hm₂ => ?_
  refine ⟨hm₂, Int64.ofBitVec_toBitVec _, ?_⟩
  have hreg : S₁.reg .rsp = some (mkSub64 sp (.lit 8)) := by
    rw [SState.storeAt_reg hS, SState.reg_setReg_of hsp]
  have hb : bytesOf env.ret 0 8 = env.ret := by
    apply BitVec.eq_of_toNat_eq
    simp only [bytesOf, BitVec.toNat_ofNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    have := env.ret.isLt
    omega
  obtain ⟨hl8, -⟩ := hm₂.loadOne hwf
    (SState.storeAt_loadOne hS (slots_mkSub64 _ _ _ _) (by decide)) (by decide)
  rw [← hm₂.regs .rsp _ hreg, eval_mkBytes] at hl8
  change _ = some ((bytesOf env.ret 0 8).toNat : Int) at hl8
  rw [hb] at hl8
  rw [retOf_of_loadInt hl8, hr, Int64.ofBitVec_toBitVec]

theorem ok_ret : OpOk env (.ret : Operation w) := by
  intro S S' x m p hwf hm h _
  change Step.ret S = some (S', x) at h
  simp only [Step.ret, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨sp, hsp, a, ha, rfl, rfl⟩ := h
  unfold Operation.interp
  refine load_All (w := .W64) hm hwf (hm.regs .rsp sp hsp).symm ha fun _ => ?_
  refine ⟨hm.set64 .rsp (x := m.regs.get64 .rsp + 8) fun _ h => ?_, ?_⟩
  · cases h
    rw [eval_mkAdd64, ← hm.regs .rsp sp hsp]
    rfl
  · show Int64.ofBitVec (low .W64 (a.eval env)) = _
    rw [low_W64]

theorem ok_nop (n : Nat) : OpOk env (.nop n : Operation w) := by
  intro S S' x m p _ hm h _
  cases h
  exact done_fall hm

theorem ok_nopalign (a : Nat) (pad : Option Nat) : OpOk env (.nopalign a pad : Operation w) := by
  intro S S' x m p _ hm h _
  cases h
  exact done_fall hm

end

end NativeRustcX64.Sym
