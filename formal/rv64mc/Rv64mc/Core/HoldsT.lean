/-
  Rv64mc.Core.HoldsT

  The total contract every function of the image is to be proved to satisfy: `Holds`
  (`Core/Holds.lean`) with machine-checked's partial `Isa.Contract` replaced by the total
  `Isa.TContract` (`Total/Contract.lean`), at the statement's machine rather than SP1's.

  * The context is `stmtCtx`, the statement's `step` at an `ECALL`: every `Lext` stops the run,
    and it ends the run (accepts) where `t0 = 0`, the halting `ECALL` that `Halts` asks for. A
    total proof can therefore end the run only at the halting `ECALL`: any other `ECALL` is a
    stop it cannot get past. Its accepting states are every halt, whatever `a0`: what `a0` may
    be there is the contract's `Q` or `Stop`.
  * The obligation at every state is `WinOk`: an operation that loads or stores accesses memory
    wholly inside one of the statement's windows (`inWindow`). `rvIsa`'s memory already checks
    SP1's conditions (`memOkSp1`), and a total proof must show that each operation gives a
    result, so together every access the run makes passes the statement's `memOk`.
  * `HoldsT env p i need Pre Post Out Stop` is `Holds`'s pre- and postcondition, plus `Stop`:
    the registers and memory at which the function may end the whole run, inside the call, at
    the halting `ECALL` (`halt` and every path to it: the allocator's failure, a panic). Its
    precondition adds `Windows`, where the windows lie relative to the stack, the heap, the
    static data and the code, which a total proof needs to discharge `WinOk` and SP1's store
    check (`Windows.stack`, `heap`, `nextAddr`, `data`, `noCodeAt`); its postcondition adds that
    the code map is kept, so that a caller has `Windows` again after the call (`Windows.after`).
    A partial `Holds` needs neither: there, an access outside the windows is a stop, which is
    safe.

  A call through it is `HoldsT.call`. `WinOk` holds at every state that is not at an operation
  (`WinOk.of_ne`), at a register write (`WinOk.of_set`), and at a load or store whose address is
  in a window (`WinOk.of_opn`). `Final/HoldsTWitness.lean` proves a function that stores to and
  loads from its frame total, so `HoldsT` is satisfiable by one that touches memory.

  ## Main definitions

  * `stmtCtx`, `opWin`, `WinOk`, `Windows`, `HoldsT`

  ## Main results

  * `HoldsT.call`, `HoldsT.mono_need`
  * `WinOk.of_ne`, `WinOk.of_opn`, `WinOk.of_set`, `WinOk.nil`
  * `Windows.stack`, `Windows.heap`, `Windows.nextAddr`, `Windows.data`, `Windows.noCodeAt`,
    `Windows.callee`, `Windows.after`
-/

import Rv64mc.Core.Holds
import Rv64mc.EndStatement
import Rv64mc.Total.Contract
import MachineChecked.RiscV.Sym.Core

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV MachineChecked.RiscV.Sym

/-! ## The statement's machine at Lprog -/

/-- **The statement's external calls**: every `ECALL` stops the run, as `step` does, and it ends the run (accepts)
    at the halting one, `t0 = 0`, whatever `a0`. -/
def stmtCtx : Context rvIsa Unit where
  ext _ _ _ o := o = .trap
  accept _ regs _ := regs .x5 = 0

/-- An operation's memory access lies wholly in one of the statement's windows. -/
def opWin : Op Reg → (Reg → Word) → Prop
  | .load _ w _ a, regs => inWindow (a.eval regs) w.bytes = true
  | .store w a _, regs => inWindow (a.eval regs) w.bytes = true
  | _, _ => True

/-- **The obligation at every state**: at a load or a store, the access lies in a window. -/
def WinOk (p : Lprog (Op Reg) Reg) (s : State rvIsa) : Prop :=
  ∀ op, rvIsa.fetch p s = some (.Lopn op) → opWin op s.regs

namespace WinOk

variable {p : Lprog (Op Reg) Reg} {fd : Lfundef (Op Reg) Reg} {fn pc : Nat} {rv top : Word}
  {rest : List Frame} {regs : Reg → Word} {m : MachineState}

/-- At an instruction that is not an operation. -/
theorem of_ne {i : LinstrR (Op Reg) Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some i)
    (hne : ∀ op, i ≠ .Lopn op) : WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  intro op h
  rw [SafeN.fetch_eq (fr := ⟨fn, pc, rv, top⟩) hf hi] at h
  exact absurd (Option.some.inj h) (hne op)

/-- At an operation whose access lies in a window. -/
theorem of_opn {op : Op Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn op))
    (hw : opWin op regs) : WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  intro op' h
  rw [SafeN.fetch_eq (fr := ⟨fn, pc, rv, top⟩) hf hi] at h
  cases h
  exact hw

/-- At a register write. -/
theorem of_set {d : Reg} {e : Expr Reg} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lopn (.set d e))) :
    WinOk p ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  of_opn hf hi trivial

/-- A returned program is at no instruction. -/
theorem nil : WinOk p ⟨[], regs, m⟩ := fun _ h => nomatch h

end WinOk

/-! ## Where the windows lie -/

/-- **Where the windows lie**, as a total contract assumes at entry with stack top `top`: the stack top at most the
    stack window's end and `NEXT`'s address in that window, so the stack between them is in it; `NEXT` at least the
    input and heap window's start and the heap's end at most its end, so the heap from `NEXT` to its end is in it;
    every static data word in a window; and every code word between the two windows, so a store in a window hits no
    code. -/
def Windows (env : Env) (top : Word) (m : MachineState) : Prop :=
  top.toNat ≤ 0xc0000000 ∧ 0xa0000000 ≤ env.nextAddr.toNat ∧ 0x10000000 ≤ (env.next m).toNat ∧
    env.heapEnd.toNat ≤ 0x78000000 ∧ (∀ q ∈ env.data, inWindow q.1 8 = true) ∧ CodeWithin 0x78000000 0xa0000000 m

namespace Windows

variable {env : Env} {top a : Word} {w : Nat} {m : MachineState}

/-- An access within the stack, between `stackLimit` and the stack top, is in a window. -/
theorem stack (h : Windows env top m) (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat + w ≤ top.toNat) :
    inWindow a w = true := by
  have := env.layout
  have := h.1
  have := h.2.1
  simp only [inWindow, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact .inr ⟨by omega, by omega⟩

/-- An access within the heap, from `NEXT` to the heap's end, is in a window. -/
theorem heap (h : Windows env top m) (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + w ≤ env.heapEnd.toNat) :
    inWindow a w = true := by
  have := h.2.2.1
  have := h.2.2.2.1
  simp only [inWindow, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact .inl ⟨by omega, by omega⟩

/-- `NEXT` itself is in a window, below a stack top at least `stackLimit`. -/
theorem nextAddr (h : Windows env top m) (hs : env.stackLimit.toNat ≤ top.toNat) :
    inWindow env.nextAddr 8 = true := by
  have := env.layout
  have := h.1
  have := h.2.1
  simp only [inWindow, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact .inr ⟨by omega, by omega⟩

/-- A static data word is in a window. -/
theorem data (h : Windows env top m) {q : Word × Word} (hq : q ∈ env.data) : inWindow q.1 8 = true :=
  h.2.2.2.2.1 q hq

private theorem align4_toNat (y : Word) : (align4 y).toNat = y.toNat - y.toNat % 4 := by
  have hlow : (y &&& 3#64).toNat = y.toNat % 4 := by
    rw [BitVec.toNat_and]; simp; exact Nat.and_two_pow_sub_one_eq_mod y.toNat 2
  have hdisj : (y &&& ~~~3#64) &&& (y &&& 3#64) = 0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not]
    cases (3#64).getLsbD i <;> cases y.getLsbD i <;> simp
  have hsum : (y &&& ~~~3#64) + (y &&& 3#64) = y := by
    rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, ← BitVec.and_or_distrib_left]
    have : (~~~3#64 ||| 3#64) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes]
  have hle : (y &&& ~~~3#64).toNat ≤ y.toNat := by
    rw [BitVec.toNat_and]; exact Nat.and_le_left
  have h := congrArg BitVec.toNat hsum
  rw [BitVec.toNat_add, hlow] at h
  have hy := y.isLt
  unfold align4
  omega

/-- **A store in a window hits no code**: SP1's `noCodeAt` holds. -/
theorem noCodeAt (h : Windows env top m) (ha : inWindow a w = true) (hw : 0 < w) :
    RiscvZkvm.Rv64.noCodeAt m a w = true := by
  simp only [inWindow, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at ha
  unfold RiscvZkvm.Rv64.noCodeAt
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  simp only [Option.isNone_iff_eq_none]
  have hlo := align4_toNat a
  have hhi := align4_toNat (a + BitVec.ofNat 64 (w - 1))
  have hw1 : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w - 1) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hw1] at hhi
  have hsub : (align4 (a + BitVec.ofNat 64 (w - 1)) - align4 a).toNat
      = (align4 (a + BitVec.ofNat 64 (w - 1))).toNat - (align4 a).toNat := by
    rw [BitVec.toNat_sub]
    have h1 := (align4 a).isLt
    have h2 := (align4 (a + BitVec.ofNat 64 (w - 1))).isLt
    rw [show 2 ^ 64 - (align4 a).toNat + (align4 (a + BitVec.ofNat 64 (w - 1))).toNat
        = ((align4 (a + BitVec.ofNat 64 (w - 1))).toNat - (align4 a).toNat) + 2 ^ 64 by omega]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hsub] at hi
  have hx : (align4 a + BitVec.ofNat 64 (4 * i)).toNat = (align4 a).toNat + 4 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * i) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  cases hc : m.code (align4 a + BitVec.ofNat 64 (4 * i)) with
  | none => rfl
  | some _ =>
    have hb := h.2.2.2.2.2 _ (by rw [hc]; exact Option.some_ne_none _)
    rw [hx] at hb
    omega

/-- At a callee's entry, with a stack top no higher. -/
theorem callee {top' : Word} (h : Windows env top m) (ht : top'.toNat ≤ top.toNat) : Windows env top' m :=
  ⟨by have := h.1; omega, h.2⟩

/-- After a call or a store that keeps the code and does not lower `NEXT`. -/
theorem after {m' : MachineState} (h : Windows env top m) (hc : m'.code = m.code)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) : Windows env top m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, by omega, h4, h5, fun a ha => h6 a (by rw [← hc]; exact ha)⟩

end Windows

/-! ## The contract -/

namespace HoldsT

/-- The precondition of `HoldsT`: `Holds`'s, and where the windows lie. -/
def pre (env : Env) (need : Nat) (Pre : (Reg → Word) → MachineState → Prop) (ret top : Word)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  Holds.pre env need Pre ret top regs m ∧ Windows env top m

/-- The postcondition of `HoldsT`: `Holds`'s, and the code map kept. -/
def post (env : Env) (Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop)
    (Out : (Reg → Word) → MachineState → Word → Prop) (ret top : Word) (regs : Reg → Word) (m : MachineState)
    (r' : Reg → Word) (m' : MachineState) : Prop :=
  Holds.post env Post Out ret top regs m r' m' ∧ m'.code = m.code

end HoldsT

/-- **The total contract of function `i` of `p`**: from its entry with `Pre`, the calling convention's precondition,
    `need` bytes of stack and the windows where `Windows` says, every load and store in a window, the run either
    returns, with `Post`, the calling convention, the memory frame (writing at most `Out` besides its stack and
    allocations), `env.Static` and the code map kept, or ends the run at the halting `ECALL` with a nonempty stack
    and `Stop`; it does not trap, go `wrong` or run forever. -/
def HoldsT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (need : Nat)
    (Pre : (Reg → Word) → MachineState → Prop)
    (Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop)
    (Out : (Reg → Word) → MachineState → Word → Prop := fun _ _ _ => False)
    (Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop := fun _ _ _ _ => False) : Prop :=
  rvIsa.TContract p stmtCtx (WinOk p) i (HoldsT.pre env need Pre) (HoldsT.post env Post Out)
    (fun _ _ regs m r' m' => Stop regs m r' m')

namespace HoldsT

variable {env : Env} {p : Lprog (Op Reg) Reg} {f : Nat} {need : Nat}
  {Pre : (Reg → Word) → MachineState → Prop}
  {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
  {Out : (Reg → Word) → MachineState → Word → Prop}
  {Stop : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}

/-- The contract as `Total/Contract.lean`'s. -/
theorem contract (h : HoldsT env p f need Pre Post Out Stop) :
    rvIsa.TContract p stmtCtx (WinOk p) f (HoldsT.pre env need Pre) (HoldsT.post env Post Out)
      (fun _ _ regs m r' m' => Stop regs m r' m') := h

/-- **A call through a total contract**: the target reaches the callee, the stack has `need` bytes, the invariants,
    `Windows` at the stack pointer and `Pre` hold with `ra` the return address, `Q` holds at every halt with a nonempty
    stack and `Stop`, and the run is total from every state the callee returns in, after the call. -/
theorem call (h : HoldsT env p f need Pre Post Out Stop) {fn pc : Nat} {fd : Lfundef (Op Reg) Reg}
    {ret rv top : Word} {tgt : Target Reg} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    {Q : State rvIsa → Prop} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt))
    (hc : rvIsa.callee p regs tgt = some f) (hstack : env.stackLimit.toNat + need ≤ (regs .x2).toNat)
    (hst : env.Static m) (hnext : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : Pre (updReg regs .x1 ret) m)
    (halign : (regs .x2).toNat % 16 = 0) (hwin : Windows env (regs .x2) m)
    (hstop : ∀ fr st r' m', Stop (updReg regs .x1 ret) m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', AbiRegs (regs .x2) (updReg regs .x1 ret) r' →
      env.Frame (regs .x2) (Out (updReg regs .x1 ret) m) m m' → env.Static m' → m'.code = m.code →
      Post (updReg regs .x1 ret) m r' m' → rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  Total.call_contract hf hi h hc (WinOk.of_ne hf hi nofun)
    ⟨⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, hstack, hst, hnext, hpre, halign⟩, hwin⟩
    hstop fun r' m' ⟨⟨ha, hfr, hs, hp⟩, hc⟩ => hk r' m' ha hfr hs hc hp

/-- **More stack than a contract needs is enough.** -/
theorem mono_need (h : HoldsT env p f need Pre Post Out Stop) {need' : Nat} (hn : need ≤ need') :
    HoldsT env p f need' Pre Post Out Stop :=
  fun Q ret top rest regs m ⟨⟨he, hs, hrest⟩, hw⟩ hstop hk =>
    h Q ret top rest regs m ⟨⟨he, by omega, hrest⟩, hw⟩ hstop hk

end HoldsT

end Rv64mc
