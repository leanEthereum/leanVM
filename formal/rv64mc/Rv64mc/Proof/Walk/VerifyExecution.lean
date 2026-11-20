/-
  Rv64mc.Proof.Walk.VerifyExecution

  `verify_execution` is a tail call of `walk` (with `checked` folded to `true` in `walk`), so it has `walk`'s
  contract: none of it reads `t1`.
-/

import Rv64mc.Proof.Runtime.Forward
import Rv64mc.Spec.Walk.Execution
import Rv64mc.Gen.Tmpl.Verifier.VerifyExecution

namespace Rv64mc.Proof.Walk.VerifyExecution

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Walk.Execution
open Rv64mc.Gen

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Verifier.VerifyExecution.Link)
    (hp : p[i]? = some (Verifier.VerifyExecution.tmpl L)) (hL : L.WF p) {need : Nat}
    (hwalk : spec env p L.walk.idx need) : spec env p i need := fun bc pi pf ↦
  Proof.Runtime.tail_ok hp rfl hL.walk hL.s0 (hwalk bc pi pf)
    (fun _ _ h ↦ by simpa [Pre, updReg_apply] using h)
    (fun _ _ _ _ h ↦ by simpa [Post, updReg_apply] using h)
    (fun _ _ _ h ↦ by simpa [Out, updReg_apply] using h)

end Rv64mc.Proof.Walk.VerifyExecution
