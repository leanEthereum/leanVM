/-
  Rv64mc.Proof.Field.ClmulLow

  `clmul_low` keeps its contract (`Spec.Field.ClmulLow.spec`), over any program holding its template, from the
  content of the one constant it reads (`DataRef.Words`, the class mask `0x8888…`).
-/

import Rv64mc.Spec.Field.ClmulLow
import Rv64mc.Proof.Field.U128
import Rv64mc.Gen.Tmpl.Verifier.Field.ClmulLow
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Field.ClmulLow

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field
open Rv64mc.Gen.Verifier.Field.ClmulLow (Link tmpl d_c8_d07a1b83_words)

theorem classMask_0 : Model.classMask 0 = 0x1111111111111111#64 := by decide +kernel
theorem classMask_1 : Model.classMask 1 = 0x2222222222222222#64 := by decide +kernel
theorem classMask_2 : Model.classMask 2 = 0x4444444444444444#64 := by decide +kernel
theorem classMask_3 : Model.classMask 3 = 0x8888888888888888#64 := by decide +kernel

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hd : DataRef.Words env L.d_c8_d07a1b83 d_c8_d07a1b83_words) {need : Nat} (hn : 48 ≤ need) :
    ClmulLow.spec env p i need := by
  rv_auto hp
  simp only [Model.clmulLow, classMask_0, classMask_1, classMask_2, classMask_3]
  ac_rfl

end Rv64mc.Proof.Field.ClmulLow
