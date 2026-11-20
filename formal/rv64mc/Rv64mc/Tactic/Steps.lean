/-
  Rv64mc.Tactic.Steps

  The rules `rv_sym` (`Rv64mc.Tactic.Sym`) applies, one per instruction form of RISC-V's Lprog (`rvIsa`), each in
  the form its result is computed in: a register's new value and a memory's new contents are given, with the
  equation that says what the operation computes, so that the executor states the next state itself and no `simp`
  runs over the goal. A load's or a store's check is not a hypothesis of what follows: an operation whose check
  fails traps, and a trap is safe.

  ## Main results

  * `step_set`, `step_ld`, `step_load`, `step_sd`, `step_store`: the operations
  * `step_cmp`: a branch on a comparison, its outcomes as propositions
  * `absorb`: a register file that a fact gives a register of, as that register written
  * `callee_indirect`, `callee_direct`: a call reaches the callee a link fact names
-/

import LprogRiscV.Lsym

namespace Rv64mc.Tactic

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

variable {p : Lprog rvIsa.Op rvIsa.Reg} {E : Type} {c : Context rvIsa E} {G : State rvIsa → Prop} {n : Nat}
  {Q : State rvIsa → Prop} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
  {fd : Lfundef rvIsa.Op rvIsa.Reg} {fn pc : Nat} {rv top : Word}

/-- A register written with the value `v` of its expression. -/
theorem step_set {rd : Reg} {e : Lprog.Expr Reg} (v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.set rd e))) (hv : e.eval regs = v)
    (h : rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs rd v, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.opn hf hi (by subst hv; rfl) h

/-- A doubleword load at `x`, which reads `v`. -/
theorem step_ld {rd : Reg} {a : Lprog.Expr Reg} (x v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.load rd .b8 false a))) (ha : a.eval regs = x) (hv : m.getMem x = v)
    (h : rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, updReg regs rd v, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine SafeN.opn' hf hi (fun r' m' he => ?_)
  simp only [rvIsa, Isa.ofOps, Op.eval, ha] at he
  cases hl : rvMem.load .b8 x m with
  | none => simp [hl] at he
  | some v' =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have : m.getMem x = v' := by simp only [rvMem] at hl; split at hl <;> simp_all
    simpa [← this, hv] using h

/-- A load of any width at `x`: what follows holds for every value it may read. -/
theorem step_load {rd : Reg} {w : Width} {s : Bool} {a : Lprog.Expr Reg} (x : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.load rd w s a))) (ha : a.eval regs = x)
    (h : ∀ v, rvMem.load w x m = some v →
      rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest,
        updReg regs rd (if s then (UnOp.sext w).eval v else v), m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine SafeN.opn' hf hi (fun r' m' he => ?_)
  simp only [rvIsa, Isa.ofOps, Op.eval, ha] at he
  cases hl : rvMem.load w x m with
  | none => simp [hl] at he
  | some v =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h v hl

/-- A doubleword store of `v` at `x`. -/
theorem step_sd {a e : Lprog.Expr Reg} (x v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.store .b8 a e))) (ha : a.eval regs = x) (hv : e.eval regs = v)
    (h : rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m.setMem x v⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine SafeN.opn' hf hi (fun r' m' he => ?_)
  simp only [rvIsa, Isa.ofOps, Op.eval, ha, hv] at he
  cases hl : rvMem.store .b8 x v m with
  | none => simp [hl] at he
  | some m'' =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have : m'' = m.setMem x v := by simp only [rvMem] at hl; split at hl <;> simp_all
    simpa [this] using h

/-- A store of any width: what follows holds for every memory it may leave. -/
theorem step_store {w : Width} {a e : Lprog.Expr Reg} (x v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.store w a e))) (ha : a.eval regs = x) (hv : e.eval regs = v)
    (h : ∀ m', rvMem.store w x v m = some m' → rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m'⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine SafeN.opn' hf hi (fun r' m' he => ?_)
  simp only [rvIsa, Isa.ofOps, Op.eval, ha, hv] at he
  cases hl : rvMem.store w x v m with
  | none => simp [hl] at he
  | some m'' =>
    simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h _ hl

/-- What a comparison of a branch says when it holds (`pos`) and when it does not (`neg`). -/
def cmpProp (op : String) (x y : Word) : Prop × Prop :=
  if op = "eq" then (x = y, x ≠ y)
  else if op = "ne" then (x ≠ y, x = y)
  else if op = "lt" then (x.slt y = true, x.slt y = false)
  else if op = "ge" then (x.slt y = false, x.slt y = true)
  else if op = "ltu" then (x < y, y ≤ x)
  else if op = "geu" then (y ≤ x, x < y)
  else (False, False)

theorem cmpEval_true {op : String} {x y : Word} (h : cmpEval op x y = some true) : (cmpProp op x y).1 := by
  unfold cmpEval at h; unfold cmpProp
  repeat' split
  all_goals first
    | simp_all; done
    | simp_all [BitVec.ult_iff_lt]; done
    | simp_all [Lprog.ult_eq_false, BitVec.not_lt]

theorem cmpEval_false {op : String} {x y : Word} (h : cmpEval op x y = some false) : (cmpProp op x y).2 := by
  unfold cmpEval at h; unfold cmpProp
  repeat' split
  all_goals first
    | simp_all; done
    | simp_all [BitVec.ult_iff_lt]; done
    | simp_all [Lprog.ult_eq_false, BitVec.not_lt]

/-- **A branch on a comparison** of operands that read `x` and `y`: the branch taken where the comparison holds,
    the next instruction where it does not, each with what the comparison then says (`cmpProp`). -/
theorem step_cmp {op : String} {a b : LOperand Reg} {l : LLabel} (j : Nat) (x y : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcond (.cmp op a b) l)) (hl : labelIdx fd.body l = some j)
    (ha : operandVal regs a = some x) (hb : operandVal regs b = some y) (hs : (cmpEval op x y).isSome)
    (ht : (cmpProp op x y).1 → rvIsa.SafeN p c G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : (cmpProp op x y).2 → rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  have hc : rvIsa.cond (.cmp op a b) regs m = cmpEval op x y := by
    simp [condEval, ha, hb]
  cases hv : cmpEval op x y with
  | none => simp [hv] at hs
  | some v =>
    rw [hv] at hc
    cases v
    · exact SafeN.cond hf hi hc hl (fun h => nomatch h) (fun _ => hn (cmpEval_false hv))
    · exact SafeN.cond hf hi hc hl (fun _ => ht (cmpEval_true hv)) (fun h => nomatch h)

theorem step_label {kd : LabelKind} {l : LLabel} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Llabel kd l))
    (h : rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.label hf hi h

theorem step_skip (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn .skip))
    (h : rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.opn hf hi rfl h

theorem step_goto {l : LLabel} (j : Nat) (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lgoto l))
    (hl : labelIdx fd.body l = some j) (h : rvIsa.SafeN p c G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.goto hf hi hl h

/-- A call through the callee's contract, the stack pointer and link register as RISC-V names them. -/
theorem step_call {ret : Word} {tgt : Target Reg} {f : Nat}
    {Pre : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    {Post : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt)) (hcon : rvIsa.Contract p c f Pre Post)
    (hc : rvIsa.callee p regs tgt = some f) (hpre : Pre ret (regs .x2) (updReg regs .x1 ret) m)
    (hk : ∀ r' m', Post ret (regs .x2) (updReg regs .x1 ret) m r' m' →
      rvIsa.SafeN p c G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.call_contract hf hi hcon hc hpre hk

/-- A tail call through the callee's contract. -/
theorem step_tail {tgt : Target Reg} {f : Nat}
    {Pre : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    {Post : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt)) (hcon : rvIsa.Contract p c f Pre Post)
    (hc : rvIsa.callee p regs tgt = some f) (hsp : regs .x2 = top) (hpre : Pre rv top regs m)
    (hk : ∀ r' m', Post rv top regs m r' m' → rvIsa.SafeN p c G n Q ⟨rest, r', m'⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.tail_contract hf hi hcon hc hsp hpre hk

theorem step_ret (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lret) (hra : regs .x1 = rv)
    (hsp : regs .x2 = top) (h : rvIsa.SafeN p c G n Q ⟨rest, regs, m⟩) :
    rvIsa.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.ret hf hi hra hsp h

/-- A register file that reads `v` at `r` is the one with `r` written `v`. -/
theorem absorb {st : List Frame} {R : Reg → Word} {r : Reg} {v : Word} (h : R r = v)
    (k : rvIsa.SafeN p c G n Q ⟨st, updReg R r v, m⟩) : rvIsa.SafeN p c G n Q ⟨st, R, m⟩ := by
  have e : updReg R r v = R := by
    funext r'; simp only [updReg]; split <;> simp_all
  rwa [e] at k

/-- A call through `e` reaches the function at `idx` if `e` reads its entry. -/
theorem callee_indirect {e : Lprog.Expr Reg} {idx : Nat} {entry : Word} (ha : (p[idx]?).map (·.addr) = some entry)
    (he : e.eval regs = entry) : rvIsa.callee p regs (.indirect e [idx]) = some idx := by
  simp [Isa.callee, Isa.addrAt, ha, he, List.find?]

/-- A direct call reaches a function of the program. -/
theorem callee_direct {idx : Nat} {entry : Word} (ha : (p[idx]?).map (·.addr) = some entry) :
    rvIsa.callee p regs (.direct idx) = some idx := by
  have : idx < p.length := by
    cases h : p[idx]? with
    | none => simp [h] at ha
    | some _ => exact (List.getElem?_eq_some_iff.1 h).1
  simp [Isa.callee, this]

end Rv64mc.Tactic

