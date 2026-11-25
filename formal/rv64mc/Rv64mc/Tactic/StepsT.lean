/-
  Rv64mc.Tactic.StepsT

  The rules `rv_symT` (`Rv64mc.Tactic.SymT`) applies to a total goal `rvIsa.Total p c (WinOk p) Q s`, the judgement
  `HoldsT` asks of a function's body: `Steps.lean`'s rules, one per instruction form, in the same computed-result
  form and with the same binders, over `Total.*` (`Total/Judgement.lean`) with the obligation `WinOk` discharged.
  Where `Steps.lean`'s rules quantify over a load's or store's every result (a fault is safe for `SafeN`), these give
  the result, from three facts about the address: in a window (`inWindow`), aligned for its width, and, for a store,
  over no code. SP1's range check follows from the window (`TotalRv.valid_of_inWindow`). A call or tail call goes
  through a total contract (`Isa.TContract`), with `Q` asked at the callee's stopping states.

  ## Main results

  * `stepT_set`, `stepT_ld`, `stepT_loadw`, `stepT_sd`, `stepT_storew`, `stepT_skip`: the operations
  * `stepT_cmp`, `stepT_label`, `stepT_goto`, `stepT_call`, `stepT_tail`, `stepT_ret`: the other instructions
  * `regsT_eq`: a register file as an equal one
  * `alignedFor_of_mod`, `code_storeMem`, `noCodeAt_of_windows`: the side goals' lemmas
-/

import Rv64mc.Tactic.Steps
import Rv64mc.Tactic.TStep

namespace Rv64mc.Tactic

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

variable {p : Lprog rvIsa.Op rvIsa.Reg} {E : Type} {c : Context rvIsa E} {Q : State rvIsa → Prop}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState} {fd : Lfundef rvIsa.Op rvIsa.Reg} {fn pc : Nat}
  {rv top : Word}

/-! ## The side goals' lemmas -/

/-- SP1's alignment check from the address's number. -/
theorem alignedFor_of_mod {w : Width} {x : Word} (h : x.toNat % w.bytes = 0) : alignedFor w.bytes x = true := by
  cases w <;> simp_all [alignedFor, isAligned8, isAligned4, isAligned2, Width.bytes]

/-- A store of any width keeps the code map. -/
theorem code_storeMem (w : Width) (m : MachineState) (x v : Word) : (storeMem w m x v).code = m.code := by
  cases w <;> simp [storeMem]

/-- **A store in a window hits no code**, in a memory whose code map is the entry's, where `Windows` held. -/
theorem noCodeAt_of_windows {env : Env} {top0 : Word} {m0 M : MachineState} (hw : Windows env top0 m0)
    (hc : M.code = m0.code) {x : Word} {n : Nat} (hx : inWindow x n = true) (hn : 0 < n) : noCodeAt M x n = true := by
  simpa only [RiscvZkvm.Rv64.noCodeAt, hc] using hw.noCodeAt hx hn

/-! ## The operations -/

/-- A register written with the value `v` of its expression. -/
theorem stepT_set {rd : Reg} {e : Lprog.Expr Reg} (v : Word) (R' : Reg → Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.set rd e))) (hv : e.eval regs = v) (hR : updReg regs rd v = R')
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, R', m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  subst hv hR
  exact Total.set hf hi (WinOk.of_set hf hi) h

/-- A load of any width at `x` in a window and aligned for its width, the value as the memory's accessor reads
    it. -/
theorem stepT_loadw {rd : Reg} {w : Width} {s : Bool} {a : Lprog.Expr Reg} (x v : Word) (R' : Reg → Word)
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.load rd w s a))) (ha : a.eval regs = x)
    (hv : (if s then (UnOp.sext w).eval (loadVal w m x) else loadVal w m x) = v) (hR : updReg regs rd v = R')
    (hw : inWindow x w.bytes = true) (hal : x.toNat % w.bytes = 0)
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, R', m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  subst ha hv hR
  have hl : rvMem.load w (a.eval regs) m = some (loadVal w m (a.eval regs)) := by
    simp only [rvMem, TotalRv.valid_of_inWindow hw, alignedFor_of_mod hal, Bool.and_self, ↓reduceIte]
    cases w <;> rfl
  exact Total.opn hf hi (by simp only [rvIsa, Isa.ofOps, Op.eval, hl, Option.map_some])
    (WinOk.of_opn hf hi (by simpa [opWin] using hw)) h

/-- A doubleword load at `x` in a window and 8-byte aligned, which reads `v`. -/
theorem stepT_ld {rd : Reg} {a : Lprog.Expr Reg} (x v : Word) (R' : Reg → Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.load rd .b8 false a))) (ha : a.eval regs = x) (hv : m.getMem x = v)
    (hR : updReg regs rd v = R') (hw : inWindow x 8 = true) (hal : x.toNat % 8 = 0)
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, R', m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  stepT_loadw (w := .b8) (s := false) x v R' hf hi ha hv hR hw hal h

/-- A store of any width of `v` at `x`, in a window, aligned for its width and over no code. -/
theorem stepT_storew {w : Width} {a e : Lprog.Expr Reg} (x v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.store w a e))) (ha : a.eval regs = x) (hv : e.eval regs = v)
    (hw : inWindow x w.bytes = true) (hal : x.toNat % w.bytes = 0) (hnc : noCodeAt m x w.bytes = true)
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, storeMem w m x v⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  subst ha hv
  have hs : rvMem.store w (a.eval regs) (e.eval regs) m = some (storeMem w m (a.eval regs) (e.eval regs)) := by
    simp only [rvMem, TotalRv.valid_of_inWindow hw, alignedFor_of_mod hal, hnc, Bool.and_self, ↓reduceIte]
    cases w <;> rfl
  exact Total.opn hf hi (by simp only [rvIsa, Isa.ofOps, Op.eval, hs, Option.map_some])
    (WinOk.of_opn hf hi (by simpa [opWin] using hw)) h

/-- A doubleword store of `v` at `x`, in a window, 8-byte aligned and over no code. -/
theorem stepT_sd {a e : Lprog.Expr Reg} (x v : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lopn (.store .b8 a e))) (ha : a.eval regs = x) (hv : e.eval regs = v)
    (hw : inWindow x 8 = true) (hal : x.toNat % 8 = 0) (hnc : noCodeAt m x 8 = true)
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m.setMem x v⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  stepT_storew (w := .b8) x v hf hi ha hv hw hal hnc h

theorem stepT_skip (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn .skip))
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.opn hf hi rfl (WinOk.of_opn hf hi trivial) h

/-! ## The other instructions -/

/-- **A branch on a comparison** of operands that read `x` and `y`, as `step_cmp`. -/
theorem stepT_cmp {op : String} {a b : LOperand Reg} {l : LLabel} (j : Nat) (x y : Word) (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcond (.cmp op a b) l)) (hl : labelIdx fd.body l = some j)
    (ha : operandVal regs a = some x) (hb : operandVal regs b = some y) (hs : (cmpEval op x y).isSome)
    (ht : (cmpProp op x y).1 → rvIsa.Total p c (WinOk p) Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : (cmpProp op x y).2 → rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  have hc : rvIsa.cond (.cmp op a b) regs m = cmpEval op x y := by
    simp [condEval, ha, hb]
  cases hv : cmpEval op x y with
  | none => simp [hv] at hs
  | some v =>
    rw [hv] at hc
    cases v
    · exact Total.cond hf hi hc hl (WinOk.of_ne hf hi nofun) (fun h => nomatch h) (fun _ => hn (cmpEval_false hv))
    · exact Total.cond hf hi hc hl (WinOk.of_ne hf hi nofun) (fun _ => ht (cmpEval_true hv)) (fun h => nomatch h)

theorem stepT_label {kd : LabelKind} {l : LLabel} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Llabel kd l))
    (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.label hf hi (WinOk.of_ne hf hi nofun) h

theorem stepT_goto {l : LLabel} (j : Nat) (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lgoto l))
    (hl : labelIdx fd.body l = some j) (h : rvIsa.Total p c (WinOk p) Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.goto hf hi hl (WinOk.of_ne hf hi nofun) h

/-- A call through the callee's total contract: its precondition, `Q` at every state it may end the run in, and the
    run total after the return. -/
theorem stepT_call {ret : Word} {tgt : Target Reg} {f : Nat}
    {Pre : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    {Post Stop : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt))
    (hcon : rvIsa.TContract p c (WinOk p) f Pre Post Stop) (hc : rvIsa.callee p regs tgt = some f)
    (hpre : Pre ret (regs .x2) (updReg regs .x1 ret) m)
    (hstop : ∀ fr st r' m', Stop ret (regs .x2) (updReg regs .x1 ret) m r' m' →
      rvIsa.accept p c ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', Post ret (regs .x2) (updReg regs .x1 ret) m r' m' →
      rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.call_contract hf hi hcon hc (WinOk.of_ne hf hi nofun) hpre hstop hk

/-- A tail call through the callee's total contract. -/
theorem stepT_tail {tgt : Target Reg} {f : Nat}
    {Pre : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    {Post Stop : Word → Word → (rvIsa.Reg → Word) → rvIsa.M → (rvIsa.Reg → Word) → rvIsa.M → Prop}
    (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Ltail tgt))
    (hcon : rvIsa.TContract p c (WinOk p) f Pre Post Stop) (hc : rvIsa.callee p regs tgt = some f)
    (hsp : regs .x2 = top) (hpre : Pre rv top regs m)
    (hstop : ∀ fr st r' m', Stop rv top regs m r' m' → rvIsa.accept p c ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', Post rv top regs m r' m' → rvIsa.Total p c (WinOk p) Q ⟨rest, r', m'⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.tail_contract hf hi hcon hc hsp (WinOk.of_ne hf hi nofun) hpre hstop hk

theorem stepT_ret (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some .Lret) (hra : regs .x1 = rv)
    (hsp : regs .x2 = top) (h : rvIsa.Total p c (WinOk p) Q ⟨rest, regs, m⟩) :
    rvIsa.Total p c (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.ret hf hi hra hsp (WinOk.of_ne hf hi nofun) h

/-- A register file as another equal to it. -/
theorem regsT_eq {st : List Frame} {R R' : Reg → Word} (e : R = R')
    (k : rvIsa.Total p c (WinOk p) Q ⟨st, R', m⟩) : rvIsa.Total p c (WinOk p) Q ⟨st, R, m⟩ := by
  subst e; exact k

end Rv64mc.Tactic
