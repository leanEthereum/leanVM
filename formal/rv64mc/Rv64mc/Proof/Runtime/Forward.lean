/-
  Rv64mc.Proof.Runtime.Forward

  A function whose body is a call of a function that never returns (`auipc ra; jalr ra`, with no frame of its own)
  never returns, with the callee's stack: the shape of `rust_begin_unwind` and of every panic entry but two
  (`Panics.lean`). A tail call (`auipc t1; jr t1`) has its callee's contract: `memcpy`, `memmove`, `memset`
  (`MemWrappers.lean`). Stated over the body, so that each instance is its template's equation by `rfl`.
-/

import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Link.Basic

namespace Rv64mc.Proof.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime

/-- The body `auipc ra, s.hi; jalr ra, s.lo(ra)` calling `c`, returning to `ret`. -/
def forwardBody (s : Site) (c : Callee) (ret : Word) : List (LinstrR (Op Reg) Reg) :=
  [.Llabel .internal 0, .Lopn (.set .x1 (.imm s.hi)), .Llabel .internal 1,
   .Lcall ret (.indirect (.bin .and (.bin .add (.reg .x1) (.imm s.lo)) (.imm 0xfffffffffffffffe#64)) [c.idx])]

/-- **A call of a function that never returns never returns**, with the callee's stack. -/
theorem forward_ok {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} {fd : Lfundef (Op Reg) Reg}
    (hp : p[i]? = some fd) {s : Site} {c : Callee} {ret : Word} (hb : fd.body = forwardBody s c ret)
    (hc : c.WF p) (hs : s.WF c) (h : NoReturn env p c.idx need) : NoReturn env p i need := by
  intro G n Q ret' top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _, hal⟩ _
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hc
  simp only [Site.WF] at hs
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hc, hs, Holds.post, forwardBody] using [h.contract]
  · exact ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, by simpa [updReg_apply, hsp] using hstk, hst, hnx,
      trivial, by simpa [updReg_apply, hsp] using hal⟩

/-- The body `auipc t1, s.hi; jr s.lo(t1)`: a tail call of `c`. -/
def tailBody (s : Site) (c : Callee) : List (LinstrR (Op Reg) Reg) :=
  [.Llabel .internal 0, .Lopn (.set .x6 (.imm s.hi)), .Llabel .internal 1,
   .Ltail (.indirect (.bin .and (.bin .add (.reg .x6) (.imm s.lo)) (.imm 0xfffffffffffffffe#64)) [c.idx])]

/-- **A tail call has its callee's contract**, for a contract that does not read `t1`, which the call writes. -/
theorem tail_ok {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} {fd : Lfundef (Op Reg) Reg}
    (hp : p[i]? = some fd) {s : Site} {c : Callee} (hb : fd.body = tailBody s c) (hc : c.WF p) (hs : s.WF c)
    {Pre : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    {Out : (Reg → Word) → MachineState → Word → Prop} (h : Holds env p c.idx need Pre Post Out)
    (hpre : ∀ regs m, Pre regs m → Pre (updReg regs .x6 s.hi) m)
    (hpost : ∀ regs m r' m', Post (updReg regs .x6 s.hi) m r' m' → Post regs m r' m')
    (hout : ∀ regs m a, Out (updReg regs .x6 s.hi) m a → Out regs m a) : Holds env p i need Pre Post Out := by
  intro G n Q ret top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, hP, hal⟩ hk
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hc
  simp only [Site.WF] at hs
  lsym hp with [Lprog.Isa.addrAt, hc, hs, tailBody] using [h.contract]
  · simp [updReg_apply, hsp]
  · exact ⟨⟨by simp [updReg_apply, hra], by simp [updReg_apply, hsp]⟩, hstk, hst, hnx, hpre _ _ hP, hal⟩
  · obtain ⟨hr, hf, hs', hq⟩ := hret
    refine hk _ _ ⟨?_, ⟨hf.1, hf.2.1, fun a ha => hf.2.2 a fun hw => ha ?_⟩, hs', hpost _ _ _ _ hq⟩
    · simpa [AbiRegs, updReg_apply] using hr
    · rcases hw with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr (hout _ _ _ hw)))

end Rv64mc.Proof.Runtime
