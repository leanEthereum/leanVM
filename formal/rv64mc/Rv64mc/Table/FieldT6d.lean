/-
  Rv64mc.Table.FieldT6d

  The field's total contracts of wave 6d at the image (`liftProg Gen.fns`): `Scaled::new`'s total theorem at its
  index, with the generated link, the stack `Gen.Needs` gives (its bound over its callee's by `decide`), and its
  callee's total theorem (`VecT2.fromElemE`). Left as hypotheses: the division constant `d_c8_a4f5b9af` in the static
  data (`DataRef.InData`) and the allocator's two facts (`NEXT`'s data reference and the heap's end), all
  environment facts.

  ## Main results

  * `scaledNew`
-/

import Rv64mc.Table.VecT2
import Rv64mc.Proof.Field.ScaledNewT
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

end Rv64mc.Table.FieldT6d

/-- info: 'Rv64mc.Table.FieldT6d.scaledNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT6d.scaledNew
