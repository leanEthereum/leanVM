/-
  Rv64mc.Proof.Layout.KeccakShape

  `keccak_shape` keeps its contract (`Spec.Layout.KeccakShape.spec`): a bounds check against six, then
  `table_log_heights[OP_KECCAK]`.
-/

import Rv64mc.Spec.Layout.KeccakShape
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Verifier.Layout.KeccakShape
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.KeccakShape

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Layout.KeccakShape
open Rv64mc.Gen.Verifier.Layout.KeccakShape (Link tmpl)

theorem load_heights {m : MachineState} {a : Word} {hs : List Nat}
    (hw : WordsAt m a (hs.map (BitVec.ofNat 64))) (hc : 6#64 ≤ BitVec.ofNat 64 (hs.map (BitVec.ofNat 64)).length) :
    m.getMem (a + 40#64) = BitVec.ofNat 64 (Model.keccakShapeOf hs).logSteps := by
  have h1 := hw.1
  simp only [List.length_map] at h1 hc
  rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hc
  have h5 : 5 < hs.length := by omega
  have := hw.2 5 (by simp; omega)
  simp only [List.getElem_map] at this
  rw [show (40#64 : Word) = BitVec.ofNat 64 (8 * 5) from rfl, this]
  simp [Model.keccakShapeOf, Model.opKeccakRust, List.getElem?_eq_getElem h5]

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (hpanic : Spec.Runtime.NoReturn env p L.panicBoundsCheck.idx 0) : spec env p i := by
  intro hs
  rv_auto hp with [hL] using [hpanic]
  exact load_heights hpre_7 hc

end Rv64mc.Proof.Layout.KeccakShape
