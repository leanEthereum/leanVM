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
    the registers and memory at which the function may end the whole run at the halting `ECALL`,
    in an accepting state with a nonempty stack (`halt` and every path to it: the allocator's
    failure, a panic). Its precondition adds `Windows`, where the windows lie relative to the
    stack, the heap, `NEXT`, the static data and the code, and that `NEXT` and the static data
    words are 8-byte aligned, which a total proof needs to discharge `WinOk` and SP1's checks
    (`Windows.stack`, `stackObj`, `heap`, `heapObj`, `nextAddr`, `data`, `dataSub`, `noCodeAt`);
    its postcondition adds that the code map is kept, so that a caller has `Windows` again after
    the call (`Windows.after`). A partial `Holds` needs neither: there, an access outside the
    windows is a stop, which is safe. `Windows` covers what a function owns; a pointer it is
    passed needs its window and alignment facts in the function's `Pre`.

  A call through it is `HoldsT.call`. `WinOk` holds at every state that is not at an operation
  (`WinOk.of_ne`), at a register write (`WinOk.of_set`), and at a load or store whose address is
  in a window (`WinOk.of_opn`). `Final/HoldsTWitness.lean` proves a function that stores to and
  loads from its frame total, so `HoldsT` is satisfiable by one that touches memory.

  ## Main definitions

  * `stmtCtx`, `opWin`, `WinOk`, `Windows`, `HoldsT`

  ## Main results

  * `HoldsT.call`, `HoldsT.mono_need`
  * `WinOk.of_ne`, `WinOk.of_opn`, `WinOk.of_set`, `WinOk.nil`
  * `inWindow_iff`, `Windows.stack`, `stackObj`, `heap`, `heapObj`, `nextAddr`, `data`, `dataSub`, `noCodeAt`,
    `callee`, `after`
-/

import Rv64mc.Core.Holds
import Rv64mc.EndStatement
import Rv64mc.Total.Contract
import MachineChecked.RiscV.Sym.Exec

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

/-- `inWindow` as linear bounds, for `omega`. -/
theorem inWindow_iff {a : Word} {w : Nat} : inWindow a w = true ↔
    (0x10000000 ≤ a.toNat ∧ a.toNat + w ≤ 0x78000000) ∨ (0xa0000000 ≤ a.toNat ∧ a.toNat + w ≤ 0xc0000000) := by
  simp only [inWindow, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

/-- **Where the windows lie**, as a total contract assumes at entry with stack top `top`. Its facts about `env` are
    constant: the concrete image discharges them by kernel checks (`Final/EndT.lean`). -/
structure Windows (env : Env) (top : Word) (m : MachineState) : Prop where
  /-- The stack top at most the stack window's end. -/
  top_le : top.toNat ≤ 0xc0000000
  /-- `NEXT`'s address at least the stack window's start, so the stack above it is in that window. -/
  nextAddr_ge : 0xa0000000 ≤ env.nextAddr.toNat
  /-- `NEXT`'s address aligned for its 8-byte load and store. -/
  nextAddr_aligned : env.nextAddr.toNat % 8 = 0
  /-- `NEXT` at least the input and heap window's start. -/
  next_ge : 0x10000000 ≤ (env.next m).toNat
  /-- The heap's end at most the input and heap window's end. -/
  heapEnd_le : env.heapEnd.toNat ≤ 0x78000000
  /-- Every static data word in a window and aligned for an 8-byte load. -/
  data_ok : ∀ q ∈ env.data, inWindow q.1 8 = true ∧ q.1.toNat % 8 = 0
  /-- Every code word between the two windows, so a store in a window hits no code. -/
  code_within : CodeWithin 0x78000000 0xa0000000 m

namespace Windows

variable {env : Env} {top a : Word} {w : Nat} {m : MachineState}

/-- An access on the stack, from `stackLimit` to the stack window's end, is in a window: the callee's own frame, or an
    object of a caller's at or above the callee's stack top. -/
theorem stackObj (h : Windows env top m) (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat + w ≤ 0xc0000000) :
    inWindow a w = true := by
  have := env.layout
  have := h.nextAddr_ge
  exact inWindow_iff.2 <| .inr ⟨by omega, by omega⟩

/-- An access within the stack, between `stackLimit` and the stack top, is in a window. -/
theorem stack (h : Windows env top m) (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat + w ≤ top.toNat) :
    inWindow a w = true :=
  h.stackObj hlo (by have := h.top_le; omega)

/-- An access from the input and heap window's start to the heap's end is in a window: the input, an object allocated
    before the call, or the heap from `NEXT` on. -/
theorem heapObj (h : Windows env top m) (hlo : 0x10000000 ≤ a.toNat) (hhi : a.toNat + w ≤ env.heapEnd.toNat) :
    inWindow a w = true := by
  have := h.heapEnd_le
  exact inWindow_iff.2 <| .inl ⟨by omega, by omega⟩

/-- An access within the heap, from `NEXT` to the heap's end, is in a window. -/
theorem heap (h : Windows env top m) (hlo : (env.next m).toNat ≤ a.toNat) (hhi : a.toNat + w ≤ env.heapEnd.toNat) :
    inWindow a w = true :=
  h.heapObj (by have := h.next_ge; omega) hhi

/-- `NEXT` itself is in a window, below a stack top at least `stackLimit`. -/
theorem nextAddr (h : Windows env top m) (hs : env.stackLimit.toNat ≤ top.toNat) :
    inWindow env.nextAddr 8 = true := by
  have := env.layout
  have := h.top_le
  have := h.nextAddr_ge
  exact inWindow_iff.2 <| .inr ⟨by omega, by omega⟩

/-- A static data word is in a window. -/
theorem data (h : Windows env top m) {q : Word × Word} (hq : q ∈ env.data) : inWindow q.1 8 = true :=
  (h.data_ok q hq).1

/-- An access within a static data word is in a window. -/
theorem dataSub (h : Windows env top m) {q : Word × Word} (hq : q ∈ env.data) (hlo : q.1.toNat ≤ a.toNat)
    (hhi : a.toNat + w ≤ q.1.toNat + 8) : inWindow a w = true := by
  have := inWindow_iff.1 (h.data hq)
  exact inWindow_iff.2 (by omega)

/-- **A store in a window hits no code**: SP1's `noCodeAt` holds. From machine-checked's `noCodeAt_of_codeWithin`. -/
theorem noCodeAt (h : Windows env top m) (ha : inWindow a w = true) (hw : 0 < w) :
    RiscvZkvm.Rv64.noCodeAt m a w = true := by
  have := inWindow_iff.1 ha
  exact noCodeAt_of_codeWithin h.code_within a w hw (by omega) (by omega)

/-- At a callee's entry, with a stack top no higher. -/
theorem callee {top' : Word} (h : Windows env top m) (ht : top'.toNat ≤ top.toNat) : Windows env top' m :=
  { h with top_le := by have := h.top_le; omega }

/-- After a call or a store that keeps the code and does not lower `NEXT`. -/
theorem after {m' : MachineState} (h : Windows env top m) (hc : m'.code = m.code)
    (hn : (env.next m).toNat ≤ (env.next m').toNat) : Windows env top m' :=
  { h with
    next_ge := by have := h.next_ge; omega
    code_within := fun a ha => h.code_within a (by rw [← hc]; exact ha) }

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
