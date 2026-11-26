/-
  Rv64mc.Proof.Runtime.Halt

  `verifier_rv64::halt` never returns: it sets `a0 = 2` and `t0 = 0` and executes `ecall`, which SP1 takes as
  `HALT` (no state after it), and which does not accept since `a0 ≠ 0`.
-/

import Rv64mc.Gen.Tmpl.VerifierRv64.Halt
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Core.Sp1

namespace Rv64mc.Proof.Runtime.Halt

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine Rv64mc.Spec.Runtime
open Rv64mc.Gen.VerifierRv64.Halt (Link tmpl)

/-- **`halt` never returns**, and needs no stack. -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) :
    NoReturn env p i 0 := by
  intro G n Q ret top rest regs m _ _
  lsym hp
  refine SafeN.ext hp rfl (fun ha => ?_) sp1Ctx_ext_ne_wrong fun r'' m'' es he => ?_
  · simp [sp1Ctx, getReg_ofParts, updReg_apply] at ha
  · obtain ⟨u, hag, hc, hu⟩ := he
    have h5 : u.getReg .x5 = 0 := by
      rw [← hag.regs .x5]; simp [getReg_ofParts, updReg_apply]
    rw [sp1Ecall_halt hc h5] at hu
    cases hu

end Rv64mc.Proof.Runtime.Halt
