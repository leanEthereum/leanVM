/-
  Rv64mc.Core.Holds

  The contract every function of the image is proved to satisfy, over any program `p` and any environment `env`
  (`Core/Env.lean`). `Holds env p i need Pre Post Out` is machine-checked's `Isa.Contract` of function `i` of `p`
  in SP1's context (`sp1Ctx`), with the calling convention added on both sides:

  * before: called from `ra` with the stack at `sp` (`Entry`), `need` bytes of stack free above `env.stackLimit`,
    `env.Static` true, `NEXT` within the heap, and `Pre`;
  * after: `sp` back and `s0`..`s11` kept (`AbiRegs`), every memory word kept but those the call may write
    (`env.Frame`: its stack, what it allocates, `NEXT`, and `Out`), `NEXT` grown within the heap, `env.Static`
    true, and `Post`.

  `Pre` and `Post` see the registers and memory at entry (and `Post` those at return); the return address and the
  stack top are `ra` and `sp` at entry. `Out` (by default nothing) names the words outside the call's own stack and
  allocations that it writes: an `sret` slot in the caller's frame, a buffer it fills.

  A call to a function with a contract is `Holds.call`, or `lsym … using [h.contract]` (with `Holds.pre`, `Entry`
  in its `with` lemmas, so that it can close the precondition, and `Holds.post`, `AbiRegs` so that the callee's
  registers are known after the call). `Core/Example.lean` proves a leaf and a caller of it.

  ## Main definitions

  * `AbiRegs`, `Holds`

  ## Main results

  * `Holds.call`: a call through a contract
  * `Env.Frame.getMem_above`, `Env.Frame.getMem_below_next`: what a caller keeps across a call
  * `Env.Frame.refl`, `Env.Frame.setMem_stack`, `Env.static_setMem_stack`: the frame of a function's own stack
-/

import Rv64mc.Core.Abi
import Rv64mc.Core.Env
import LprogRiscV.Sp1Ctx

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The registers the calling convention restores: `sp` back at `top`, `s0`..`s11` as at entry. -/
def AbiRegs (top : Word) (regs r' : Reg → Word) : Prop :=
  r' .x2 = top ∧ r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧
    r' .x20 = regs .x20 ∧ r' .x21 = regs .x21 ∧ r' .x22 = regs .x22 ∧ r' .x23 = regs .x23 ∧
    r' .x24 = regs .x24 ∧ r' .x25 = regs .x25 ∧ r' .x26 = regs .x26 ∧ r' .x27 = regs .x27

namespace Holds

/-- The precondition of `Holds`: the entry, the stack bound, the environment's invariants, `Pre`. -/
def pre (env : Env) (need : Nat) (Pre : (Reg → Word) → MachineState → Prop) (ret top : Word)
    (regs : Reg → Word) (m : MachineState) : Prop :=
  Entry ret top regs ∧ env.stackLimit.toNat + need ≤ top.toNat ∧ env.Static m ∧
    (env.next m).toNat ≤ env.heapEnd.toNat ∧ Pre regs m

/-- The postcondition of `Holds`: the ABI's registers, the memory frame, the static data, `Post`. -/
def post (env : Env) (Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop)
    (Out : (Reg → Word) → MachineState → Word → Prop) (_ret top : Word) (regs : Reg → Word) (m : MachineState)
    (r' : Reg → Word) (m' : MachineState) : Prop :=
  AbiRegs top regs r' ∧ env.Frame top (Out regs m) m m' ∧ env.Static m' ∧ Post regs m r' m'

end Holds

/-- **The contract of function `i` of `p`**: from its entry with `Pre`, the calling convention's precondition and
    `need` bytes of stack, every return satisfies `Post`, the calling convention, the memory frame (writing at most
    `Out` besides its stack and allocations) and `env.Static`. Partial: a run that traps or never returns is
    safe. -/
def Holds (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (need : Nat)
    (Pre : (Reg → Word) → MachineState → Prop)
    (Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop)
    (Out : (Reg → Word) → MachineState → Word → Prop := fun _ _ _ => False) : Prop :=
  rvIsa.Contract p sp1Ctx i (Holds.pre env need Pre) (Holds.post env Post Out)

namespace Holds

variable {env : Env} {p : Lprog (Op Reg) Reg} {f : Nat} {need : Nat}
  {Pre : (Reg → Word) → MachineState → Prop}
  {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
  {Out : (Reg → Word) → MachineState → Word → Prop}

/-- The contract as machine-checked's, for `lsym … using [h.contract]`. -/
theorem contract (h : Holds env p f need Pre Post Out) :
    rvIsa.Contract p sp1Ctx f (Holds.pre env need Pre) (Holds.post env Post Out) := h

/-- **A call through a contract**: the target reaches the callee, the stack has `need` bytes, the invariants and
    `Pre` hold with `ra` the return address, and every state the callee returns in is safe after the call. -/
theorem call (h : Holds env p f need Pre Post Out) {fn pc : Nat} {fd : Lfundef (Op Reg) Reg} {ret rv top : Word}
    {tgt : Target Reg} {rest : List Frame} {regs : Reg → Word} {m : MachineState} {G : State rvIsa → Prop} {n : Nat}
    {Q : State rvIsa → Prop} (hf : p[fn]? = some fd) (hi : fd.body[pc]? = some (.Lcall ret tgt))
    (hc : rvIsa.callee p regs tgt = some f) (hstack : env.stackLimit.toNat + need ≤ (regs .x2).toNat)
    (hst : env.Static m) (hnext : (env.next m).toNat ≤ env.heapEnd.toNat) (hpre : Pre (updReg regs .x1 ret) m)
    (hk : ∀ r' m', AbiRegs (regs .x2) (updReg regs .x1 ret) r' →
      env.Frame (regs .x2) (Out (updReg regs .x1 ret) m) m m' → env.Static m' →
      Post (updReg regs .x1 ret) m r' m' → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    rvIsa.SafeN p sp1Ctx G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.call_contract hf hi h hc ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, hstack, hst, hnext, hpre⟩
    fun r' m' ⟨ha, hfr, hs, hp⟩ => hk r' m' ha hfr hs hp

end Holds

/-! ## A function's own stack -/

namespace Env

variable {env : Env}

/-- A call that writes nothing keeps its frame. -/
theorem Frame.refl {top : Word} {out : Word → Prop} {m : MachineState} (h : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top out m m :=
  ⟨Nat.le_refl _, h, fun _ _ => rfl⟩

/-- A store into the stack below `top` is in the frame of a call from `top`. -/
theorem Frame.setMem_stack {top a v : Word} {out : Word → Prop} {m : MachineState}
    (h : (env.next m).toNat ≤ env.heapEnd.toNat) (hlo : env.stackLimit.toNat ≤ a.toNat) (hhi : a.toNat < top.toNat) :
    env.Frame top out m (m.setMem a v) := by
  have hne : env.nextAddr ≠ a := fun he => by have := env.layout; rw [he] at this; omega
  have hn : env.next (m.setMem a v) = env.next m := by
    simp [next, MachineState.getMem, MachineState.setMem, hne]
  refine ⟨by rw [hn]; omega, by rw [hn]; exact h, fun b hb => ?_⟩
  have hba : b ≠ a := fun he => hb (Or.inl ⟨by rw [he]; exact hlo, by rw [he]; exact hhi⟩)
  simp [MachineState.getMem, MachineState.setMem, hba]

/-- A store into the stack keeps `NEXT`. -/
theorem next_setMem_stack {a v : Word} {m : MachineState} (hlo : env.stackLimit.toNat ≤ a.toNat) :
    env.next (m.setMem a v) = env.next m := by
  have hne : env.nextAddr ≠ a := fun he => by have := env.layout; rw [he] at this; omega
  simp [next, MachineState.getMem, MachineState.setMem, hne]

/-- **The memory at or above a call's stack top is kept**, but for its `out`. -/
theorem Frame.getMem_above {top a : Word} {out : Word → Prop} {m m' : MachineState} (h : env.Frame top out m m')
    (hlim : env.stackLimit.toNat ≤ top.toNat) (ha : top.toNat ≤ a.toNat) (hout : ¬ out a) :
    m'.getMem a = m.getMem a := by
  have := env.layout
  refine h.2.2 a fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · omega
  · have := h.2.1; omega
  · rw [hw] at ha; omega
  · exact hout hw

/-- **The memory below `NEXT` is kept** (the heap allocated before the call, and the input below it), but for the
    call's `out`. -/
theorem Frame.getMem_below_next {top a : Word} {out : Word → Prop} {m m' : MachineState}
    (h : env.Frame top out m m') (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (ha : a.toNat < (env.next m).toNat)
    (hout : ¬ out a) : m'.getMem a = m.getMem a := by
  have := env.layout
  refine h.2.2 a fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · rw [hw] at ha; omega
  · exact hout hw

/-- A store into the stack keeps the static data. -/
theorem static_setMem_stack {a v : Word} {m : MachineState} (hs : env.Static m)
    (hlo : env.stackLimit.toNat ≤ a.toNat) : env.Static (m.setMem a v) := by
  refine env.static_frame m _ (fun b _ hb => ?_) hs
  have hba : b ≠ a := fun he => by have := env.layout; rw [he] at hb; omega
  simp [MachineState.getMem, MachineState.setMem, hba]

end Env

end Rv64mc
