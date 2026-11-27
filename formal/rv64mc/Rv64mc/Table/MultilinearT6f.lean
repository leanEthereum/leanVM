/-
  Rv64mc.Table.MultilinearT6f

  `Scaler::new`'s total contracts at the image (`liftProg Gen.fns`), with the generated link, the stack `Gen.Needs`
  gives (a bound over `Scaled::new`'s by `decide`) and `Scaled::new`'s total theorem (`FieldT6d.scaledNew`).
  `scalerNewSafe` (the safety contract) leaves environment facts only: `NEXT`'s data reference and the heap's end
  (`env`), and `Scaled::new`'s divisor in the static data. `scalerNew` (with the partial contract's postcondition) also
  takes `Scaled::new`'s partial contract (`Spec.Field.Scaled.newSpec`), which the partial instance
  (`Table.Multilinear.scalerNew`) rests on and no proof discharges yet: it is not an environment fact.

  ## Main results

  * `scalerNewSafe`, `scalerNew`
-/

import Rv64mc.Table.FieldT6d
import Rv64mc.Table.Multilinear
import Rv64mc.Proof.Multilinear.ScalerNewT
import Rv64mc.Gen.Link.Verifier.Multilinear

namespace Rv64mc.Table.MultilinearT6f

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Multilinear

variable (env : Env)

/-- `Scaler::new`'s safety contract. -/
theorem scalerNewSafe
    (hdiv : DataRef.InData env [(Verifier.Field.Scaled.New.link.d_c8_a4f5b9af,
      Verifier.Field.Scaled.New.d_c8_a4f5b9af_words)])
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    ScalerNewT.safeT env (liftProg fns) Idx.Verifier.Multilinear.Scaler.New Needs.Verifier.Multilinear.Scaler.New :=
  ScalerNewT.safe env _ _ _ Verifier.Multilinear.Scaler.New.tmpl_eq Verifier.Multilinear.Scaler.New.wf (by decide)
    (FieldT6d.scaledNew env hdiv hnext hend)

/-- `Scaler::new`'s total contract with the partial contract's postcondition, over `Scaled::new`'s partial
    contract. -/
theorem scalerNew
    (hdiv : DataRef.InData env [(Verifier.Field.Scaled.New.link.d_c8_a4f5b9af,
      Verifier.Field.Scaled.New.d_c8_a4f5b9af_words)])
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64)
    (hsn : Spec.Field.Scaled.newSpec env (liftProg fns) Idx.Verifier.Field.Scaled.New
      Needs.Verifier.Field.Scaled.New) :
    ScalerNewT.specT env (liftProg fns) Idx.Verifier.Multilinear.Scaler.New Needs.Verifier.Multilinear.Scaler.New :=
  ScalerNewT.total env _ _ _ Verifier.Multilinear.Scaler.New.tmpl_eq Verifier.Multilinear.Scaler.New.wf (by decide)
    (FieldT6d.scaledNew env hdiv hnext hend) (Table.Multilinear.scalerNew env hsn)

end Rv64mc.Table.MultilinearT6f

/-- info: 'Rv64mc.Table.MultilinearT6f.scalerNewSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6f.scalerNewSafe

/-- info: 'Rv64mc.Table.MultilinearT6f.scalerNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6f.scalerNew
