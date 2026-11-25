/-
  Rv64mc.Proof.Runtime.HaltT

  The total contract of the functions that end the run with the guest's abort: `Aborts env p i
  need`, function `i` never returns and ends the run at the halting `ECALL` with `a0 = 2`. Proved
  of `verifier_rv64::halt` over its template (`halt_aborts`: it sets `a0 = 2` and `t0 = 0` and executes
  `ecall`, an end of the run under `stmtCtx`), the pattern for a function that does not return;
  and of a function whose body only calls one that aborts (`forward_aborts`), the shape of the panic
  handler and of most panic entries (`PanicsT.lean`).

  ## Main definitions

  * `Aborts`

  ## Main results

  * `halt_aborts`, `forward_aborts`
-/

import Rv64mc.Core.HoldsT
import Rv64mc.Gen.Tmpl.VerifierRv64.Halt
import Rv64mc.Proof.Runtime.Forward

namespace Rv64mc.Proof.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **Function `i` of `p` ends the run with the guest's abort**, from any arguments: it never returns (its
    postcondition is `False`), and ends the run at the halting `ECALL` with `a0 = 2`. -/
def Aborts (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) (fun _ _ _ _ => False) (Stop := fun _ _ r' _ => r' .x10 = 2)

/-- **`halt` ends the run with `a0 = 2`**, and needs no stack. -/
theorem halt_aborts (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.VerifierRv64.Halt.Link)
    (hp : p[i]? = some (Gen.VerifierRv64.Halt.tmpl L)) : Aborts env p i 0 := by
  intro Q ret top rest regs m _ hstop _
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  have h5 : stmtCtx.accept 0 (updReg (updReg regs .x10 (0 + 2)) .x5 (0 + 0)) m := by
    simp [stmtCtx, updReg_apply]
  refine Total.ext_done hp rfl h5 (WinOk.of_ne hp rfl nofun) (hstop _ _ _ _ ?_ (.inr ⟨0, SafeN.fetch_eq hp rfl, h5⟩))
  simp [updReg_apply, Expr.eval, BinOp.eval]

/-- **A call of a function that aborts aborts**, with the callee's stack. -/
theorem forward_aborts {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} {fd : Lfundef (Op Reg) Reg}
    (hp : p[i]? = some fd) {s : Site} {c : Callee} {ret : Word} (hb : fd.body = forwardBody s c ret)
    (hc : c.WF p) (hs : s.WF c) (h : Aborts env p c.idx need) : Aborts env p i need := by
  intro Q ret' top rest regs m ⟨⟨hra, hsp⟩, hstk, hst, hnx, _, hal⟩ hstop _
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine Total.set hp rfl (WinOk.of_set hp rfl) ?_
  refine Total.label hp rfl (WinOk.of_ne hp rfl nofun) ?_
  refine HoldsT.call h hp rfl (callee_site hc hs (by simp [updReg_apply, Expr.eval]))
    (by simpa [updReg_apply, hsp] using hstk) hst hnx trivial (by simpa [updReg_apply, hsp] using hal)
    hstop (fun _ _ _ _ _ h => h.elim)

end Rv64mc.Proof.Runtime
