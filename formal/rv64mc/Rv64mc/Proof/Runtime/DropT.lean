/-
  Rv64mc.Proof.Runtime.DropT

  The drops that return at once are total (`DropSpecT`: `DropSpec`'s, as a `HoldsT`): the drop glue of
  `Vec<Form>` and of `Vec<(StackWeight, E)>`, and `<[MaybeUninit<Form>] as PartialDrop>::partial_drop`. Each
  template is one `ret`: the allocator never frees, and `Form` owns nothing a drop must walk.

  ## Main definitions

  * `DropSpecT`

  ## Main results

  * `vecForm_total`, `vecStackClaim_total`, `partialDropForm_total`
-/

import Rv64mc.Spec.Runtime.Drop
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecForm
import Rv64mc.Gen.Tmpl.Core.Ptr.DropGlueVecTStackWeightEE
import Rv64mc.Gen.Tmpl.Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.DropT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen

/-- **The total contract of a drop that writes nothing a caller sees**: `DropSpec`'s, as a `HoldsT`. -/
def DropSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) (fun _ _ _ _ => True)

theorem vecForm_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Core.Ptr.DropGlueVecForm.Link)
    (hp : p[i]? = some (Core.Ptr.DropGlueVecForm.tmpl L)) (need : Nat) : DropSpecT env p i need := by
  rv_autoT hp

theorem vecStackClaim_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Core.Ptr.DropGlueVecTStackWeightEE.Link) (hp : p[i]? = some (Core.Ptr.DropGlueVecTStackWeightEE.tmpl L))
    (need : Nat) : DropSpecT env p i need := by
  rv_autoT hp

theorem partialDropForm_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop.Link)
    (hp : p[i]? = some (Core.Array.Iter.IterInner.SliceMaybeUninitForm.AsPartialDrop.PartialDrop.tmpl L))
    (need : Nat) : DropSpecT env p i need := by
  rv_autoT hp

end Rv64mc.Proof.Runtime.DropT
