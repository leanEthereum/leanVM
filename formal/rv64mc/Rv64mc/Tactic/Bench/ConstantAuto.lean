import Rv64mc.Spec.Layout.Constant
import Rv64mc.Gen.Tmpl.Verifier.Layout.Constant
import Rv64mc.Tactic.Sym

namespace Rv64mc.Tactic.Bench.ConstantAuto

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Gen.Verifier.Layout.Constant (Link tmpl)

set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hterm : Spec.Layout.Term.spec env p L.term.idx) : spec env p i := by
  intro value
  rv_auto hp with [hL] using [hterm [] value (env.next m) 8#64 0]

end Rv64mc.Tactic.Bench.ConstantAuto
