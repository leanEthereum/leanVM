/-
  Rv64mc.Proof.Runtime.Drop

  The drop glue meets `DropSpec`: `dealloc` is a no-op, so `drop_in_place::<Vec<Form>>` and
  `drop_in_place::<Vec<(StackWeight, E)>>` are a bare `ret`, and `drop_in_place::<Layout>` calls the drops of its
  vectors and writes only its own frame.
-/

import Rv64mc.Spec.Runtime.Drop
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecForm
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecTStackWeightEE
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueLayout
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Runtime.Drop

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen

theorem vecForm_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Core.Ptr.DropGlueVecForm.Link)
    (hp : p[i]? = some (Core.Ptr.DropGlueVecForm.tmpl L)) {need : Nat} : DropSpec env p i need := by
  rv_auto hp

theorem vecStackClaim_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Core.Ptr.DropGlueVecTStackWeightEE.Link)
    (hp : p[i]? = some (Core.Ptr.DropGlueVecTStackWeightEE.tmpl L)) {need : Nat} : DropSpec env p i need := by
  rv_auto hp

theorem layout_ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Core.Ptr.DropGlueLayout.Link)
    (hp : p[i]? = some (Core.Ptr.DropGlueLayout.tmpl L)) (hL : L.WF p) {need needC : Nat} (hn : 16 + needC ≤ need)
    (ht : DropSpec env p L.dropGlueVecTable.idx needC) (hb : DropSpec env p L.dropGlueVecBusBlock.idx needC) :
    DropSpec env p i need := by
  rv_auto hp with [hL] using [ht, hb]

end Rv64mc.Proof.Runtime.Drop
