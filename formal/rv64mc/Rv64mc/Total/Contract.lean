/-
  Rv64mc.Total.Contract

  A function's total contract, for any instruction set: the counterpart of `Isa.Contract`
  (`Lprog/Contract.lean`) for `Isa.Total`. Written against machine-checked's `lprog` package
  only, in its namespaces, so that it can move there unchanged.

  From its entry, with a precondition on the return address, the stack pointer, the registers
  and the memory, the function either returns in a state satisfying the postcondition, or ends
  the whole run at an accepting state with a nonempty stack whose registers and memory are in
  its stopping set `Stop`: the way a function that never returns (`halt`, a panic handler, an
  allocator's failure path) ends a program. The contract asks only that this stack be nonempty,
  not that it extend the caller's; since it holds for every caller's stack, the empty one
  included, a function that returns must return with `Post`. Every state it passes satisfies the
  obligation `G`, which is the contract's parameter and not quantified, since it is the callee
  that discharges it. In continuation form, for every `Q`: if `Q` holds at every accepting state
  with a nonempty stack in `Stop`, and the run is total for `Q` from every state the function
  returns in with `Post`, it is total from the function's entry.

  Contracts compose at calls and tail calls (`Total.call_contract`, `Total.tail_contract`), a
  caller's `Stop` taking in its callees'. Recursive functions compose by strong induction on a
  measure in their precondition (`TContract.measure`), or, over a table of functions,
  `Ascent.budget_induction` at any index type.

  ## Main definitions

  * `Isa.TContract`

  ## Main results

  * `TContract.run`, `TContract.mono`, `TContract.measure`
  * `TContract.total`: what a contract says of a run from its entry
  * `Total.call_contract`, `Total.tail_contract`
-/

import Rv64mc.Total.Judgement

namespace Lprog

namespace Isa

/-- **A total contract of the function at index `f`**: from its entry, with the return address
    `ret` and the stack pointer `top` of its frame, where `Pre ret top regs m` holds, the run is
    total for `G` and any `Q`, if `Q` holds at every accepting state with a nonempty stack whose
    registers and memory satisfy `Stop`, and the run is total from every state `⟨rest, r', m'⟩`
    it may return to with `Post ret top regs m r' m'`. -/
def TContract (I : Isa) (p : Lprog I.Op I.Reg) {E : Type} (c : Context I E) (G : State I → Prop)
    (f : Nat) (Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop)
    (Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop)
    (Stop : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop) :
    Prop :=
  ∀ (Q : State I → Prop) (ret top : BitVec 64) (rest : List Frame) (regs : I.Reg → BitVec 64)
    (m : I.M), Pre ret top regs m →
    (∀ fr st r' m', Stop ret top regs m r' m' → I.accept p c ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩) →
    (∀ r' m', Post ret top regs m r' m' → I.Total p c G Q ⟨rest, r', m'⟩) →
    I.Total p c G Q ⟨⟨f, 0, ret, top⟩ :: rest, regs, m⟩

end Isa

namespace Isa.TContract

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop} {f : Nat}
  {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
  {Post Stop : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}

/-- **A contract applied**: the precondition, the stopping states, then the continuation. -/
theorem run (h : I.TContract p c G f Pre Post Stop) {Q : State I → Prop} {ret top : BitVec 64}
    {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M} (hpre : Pre ret top regs m)
    (hstop : ∀ fr st r' m', Stop ret top regs m r' m' → I.accept p c ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', Post ret top regs m r' m' → I.Total p c G Q ⟨rest, r', m'⟩) :
    I.Total p c G Q ⟨⟨f, 0, ret, top⟩ :: rest, regs, m⟩ :=
  h Q ret top rest regs m hpre hstop hk

/-- A stronger precondition, a weaker postcondition and a larger stopping set. -/
theorem mono (h : I.TContract p c G f Pre Post Stop)
    {Pre' : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    {Post' Stop' : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}
    (hpre : ∀ ret top regs m, Pre' ret top regs m → Pre ret top regs m)
    (hpost : ∀ ret top regs m r' m', Pre' ret top regs m → Post ret top regs m r' m' →
      Post' ret top regs m r' m')
    (hstop : ∀ ret top regs m r' m', Pre' ret top regs m → Stop ret top regs m r' m' →
      Stop' ret top regs m r' m') :
    I.TContract p c G f Pre' Post' Stop' :=
  fun _ _ _ _ _ _ hp hs hk => h _ _ _ _ _ _ (hpre _ _ _ _ hp)
    (fun _ _ _ _ h' ha => hs _ _ _ _ (hstop _ _ _ _ _ _ hp h') ha)
    (fun _ _ h' => hk _ _ (hpost _ _ _ _ _ _ hp h'))

/-- **A recursive function**, by strong induction on a measure `k` in its precondition: the
    contract at `k` from the contract at every `k' < k`. -/
theorem measure {Pre : Nat → BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    (h : ∀ k, (∀ k' < k, I.TContract p c G f (Pre k') Post Stop) → I.TContract p c G f (Pre k) Post Stop) :
    ∀ k, I.TContract p c G f (Pre k) Post Stop :=
  fun k => Nat.strongRecOn k h

/-- **What a contract says of a run from the entry** of an outermost call: it is total, and
    ends either returned, with `Post`, or at an accepting state with a nonempty stack, in
    `Stop`. -/
theorem total (h : I.TContract p c G f Pre Post Stop) {ret top : BitVec 64}
    {regs : I.Reg → BitVec 64} {m : I.M} (hpre : Pre ret top regs m)
    (hG : ∀ r' m', G ⟨[], r', m'⟩) :
    I.Total p c G (fun s => (s.stack = [] ∧ Post ret top regs m s.regs s.m) ∨
      (s.stack ≠ [] ∧ Stop ret top regs m s.regs s.m)) ⟨[⟨f, 0, ret, top⟩], regs, m⟩ :=
  h.run hpre (fun _ _ _ _ hs _ => .inr ⟨nofun, hs⟩)
    (fun _ _ hp => Total.returned (hG _ _) (.inl ⟨rfl, hp⟩))

end Isa.TContract

namespace Total

open Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop}
  {Q : State I → Prop} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
  {fd : Lfundef I.Op I.Reg} {fn pc : Nat} {rv top : BitVec 64} {f : Nat}
  {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
  {Post Stop : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}

/-- **A call through a total contract** of the callee: the target reaches it, its precondition
    holds, `Q` holds where it may stop, and the run is total from every state it returns to by
    its postcondition, after the call. -/
theorem call_contract {ret : BitVec 64} {tgt : Target I.Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Lcall ret tgt)) (hcon : I.TContract p c G f Pre Post Stop)
    (hc : I.callee p regs tgt = some f) (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩)
    (hpre : Pre ret (regs I.sp) (updReg regs I.link ret) m)
    (hstop : ∀ fr st r' m', Stop ret (regs I.sp) (updReg regs I.link ret) m r' m' →
      I.accept p c ⟨fr :: st, r', m'⟩ → Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', Post ret (regs I.sp) (updReg regs I.link ret) m r' m' →
      I.Total p c G Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  call hf hi hc hg (hcon.run hpre hstop hk)

/-- A tail call through a total contract of the callee: the stack pointer is back, and the
    callee returns where the caller would. -/
theorem tail_contract {tgt : Target I.Reg} (hf : p[fn]? = some fd)
    (hi : fd.body[pc]? = some (.Ltail tgt)) (hcon : I.TContract p c G f Pre Post Stop)
    (hc : I.callee p regs tgt = some f) (hsp : regs I.sp = top)
    (hg : G ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩) (hpre : Pre rv top regs m)
    (hstop : ∀ fr st r' m', Stop rv top regs m r' m' → I.accept p c ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hk : ∀ r' m', Post rv top regs m r' m' → I.Total p c G Q ⟨rest, r', m'⟩) :
    I.Total p c G Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  tail hf hi hsp hc hg (hcon.run hpre hstop hk)

end Total

end Lprog
