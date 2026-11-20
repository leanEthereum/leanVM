/-
  Rv64mc.Proof.Field.Reduce

  `reduce` keeps its contract (`Spec.Field.Reduce.spec`), over any program holding its template.
-/

import Rv64mc.Spec.Field.Reduce
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.Reduce
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.Reduce

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Field.Reduce.Link)
    (hp : p[i]? = some (Gen.Verifier.Field.Reduce.tmpl L)) : Reduce.spec env p i := by
  rv_auto hp
  simp only [Model.reduce, setWidth_append, setWidth_shift_append, BitVec.xor_assoc, BitVec.xor_comm,
    xor_left_comm]

end Rv64mc.Proof.Field.Reduce
