/-
  Rv64mc.Proof.Field.Clmul

  `clmul` keeps its contract (`Spec.Field.Clmul.spec`), over any program holding its template, from `clmul_low`'s:
  the low half is `clmul_low(a, b)`, the high half `clmul_low` of the bit-reversed operands, reversed and shifted.
-/

import Rv64mc.Spec.Field.Clmul
import Rv64mc.Spec.Field.ClmulLow
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.Clmul
import Rv64mc.Proof.Field.Reverse
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.Clmul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.Clmul (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needL : Nat} (hn : 80 + needL ≤ need) (hlow : ClmulLow.spec env p L.clmulLow.idx needL) :
    Clmul.spec env p i need := by
  rv_auto hp with [hL] using [hlow]
  · rw [Model.clmul, lo128_join]
  · generalize hc : Model.clmulLow _ _ = c
    have hc' : c = Model.clmulLow (regs .x10).reverse (regs .x11).reverse := by
      rw [← hc]
      congr 1 <;> rw [← reverse_net] <;> simp only [swapBits, bswap]
    rw [Model.clmul, hi128_join, ← hc', ← reverse_net]
    simp only [swapBits, bswap]

end Rv64mc.Proof.Field.Clmul
