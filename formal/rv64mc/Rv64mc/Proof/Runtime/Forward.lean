/-
  Rv64mc.Proof.Runtime.Forward

  A function whose body is a call of a function that never returns (`auipc ra; jalr ra`, with no frame of its own)
  never returns, with the callee's stack: the shape of `rust_begin_unwind` and of every panic entry but two
  (`Panics.lean`). Stated over the body, so that each instance is its template's equation by `rfl`.
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
  intro G n Q ret' top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _⟩ _
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hc
  simp only [Site.WF] at hs
  lsym hp with [hra, hsp, Lprog.Isa.addrAt, hc, hs, Holds.post, forwardBody] using [h.contract]
  · exact ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, by simpa [updReg_apply, hsp] using hstk, hst, hnx,
      trivial⟩

end Rv64mc.Proof.Runtime
