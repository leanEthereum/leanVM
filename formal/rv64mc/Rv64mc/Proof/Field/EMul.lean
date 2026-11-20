/-
  Rv64mc.Proof.Field.EMul

  `<E as Mul>::mul` keeps its contract (`Spec.Field.EMul.spec`), over any program holding its template, from its
  callees' contracts: Karatsuba over `clmul`, the three products folded by `reduce`.
-/

import Rv64mc.Spec.Field.EMul
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.E.AsMul.Mul
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.EMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.E.AsMul.Mul (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hcl : Clmul.spec env p L.clmul.idx) (hrd : Reduce.spec env p L.reduce.idx) : EMul.spec env p i := by
  rv_auto hp with [hL] using [hcl, hrd]
  all_goals simp only [Model.eMul, ← hi128_xor, ← lo128_xor, ← hi128_shl1, ← lo128_shl1]
  all_goals simp only [BitVec.xor_assoc, BitVec.xor_comm, xor_left_comm, append_hi_lo]

end Rv64mc.Proof.Field.EMul
