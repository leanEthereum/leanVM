/-
  Rv64mc.Table.FieldT6d

  The field's total contracts of wave 6d at the image (`liftProg Gen.fns`): `Scaled::new`'s and `K::inv`'s total
  theorems at their indices, with the generated links, the stacks `Gen.Needs` gives (bounds over the callees' by
  `decide`), and the callees' total theorems (`VecT2.fromElemE`; `FieldT.spread`, `reduce`, `baseMul`), `K::inv`'s
  partial one (`Table.Field.kInv`) with them. Left as hypotheses: the division constant `d_c8_a4f5b9af` in the static
  data (`DataRef.InData`), `clmul_low`'s table (`FieldT.ClmulTable`) and the allocator's two facts (`NEXT`'s data
  reference and the heap's end), all environment facts.

  ## Main results

  * `scaledNew`, `kInv`
-/

import Rv64mc.Table.VecT2
import Rv64mc.Proof.Field.ScaledNewT
import Rv64mc.Proof.Field.KInvT
import Rv64mc.Table.FieldT
import Rv64mc.Table.Field
import Rv64mc.Gen.Link.Verifier.Field

namespace Rv64mc.Table.FieldT6d

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Field

variable (env : Env)

/-- `Scaled::new`. -/
theorem scaledNew
    (hdiv : DataRef.InData env [(Verifier.Field.Scaled.New.link.d_c8_a4f5b9af,
      Verifier.Field.Scaled.New.d_c8_a4f5b9af_words)])
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    ScaledNewT.specT env (liftProg fns) Idx.Verifier.Field.Scaled.New Needs.Verifier.Field.Scaled.New :=
  ScaledNewT.total env _ _ _ Verifier.Field.Scaled.New.tmpl_eq Verifier.Field.Scaled.New.wf hdiv
    (needF := Needs.Alloc.Vec.SpecFromElem.E.AsSpecFromElem.FromElemGlobal) (by decide)
    (VecT2.fromElemE env hnext hend)

/-- `K::inv`. -/
theorem kInv (hd : FieldT.ClmulTable env) :
    KInvT.specT env (liftProg fns) Idx.Verifier.Field.K.Inv Needs.Verifier.Field.K.Inv :=
  KInvT.total env _ _ _ Verifier.Field.K.Inv.tmpl_eq Verifier.Field.K.Inv.wf (by decide) (by decide) (by decide)
    (FieldT.spread env) (FieldT.reduce env) (FieldT.baseMul env hd)
    (Table.Field.kInv env (hd.words (List.mem_singleton_self _)))

end Rv64mc.Table.FieldT6d

/-- info: 'Rv64mc.Table.FieldT6d.scaledNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT6d.scaledNew

/-- info: 'Rv64mc.Table.FieldT6d.kInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT6d.kInv
