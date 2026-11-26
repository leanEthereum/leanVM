/-
  Rv64mc.Table.FormT6a

  The total contracts of the functions over `Form`s (`layout.rs`) new in wave 6a at the image (`liftProg Gen.fns`),
  each at its index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as
  hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`), `clmul_low`'s constant in the static data
  (`FieldT.ClmulTable`, for `E::mul`) and, for `from_elem::<Form>`, its bound's word in the static data
  (`DataRef.InData`).

  ## Main results

  * `addScaled`, `fromElemForm`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.VecT
import Rv64mc.Table.AllocT
import Rv64mc.Table.FieldT
import Rv64mc.Table.MemT6a
import Rv64mc.Proof.Layout.AddScaledT
import Rv64mc.Proof.Layout.FromElemFormT
import Rv64mc.Gen.Link.Alloc.Vec
import Rv64mc.Gen.Link.Verifier.Layout.Form

namespace Rv64mc.Table.FormT6a

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Form::add_scaled` at the image** (function 163), given `clmul_low`'s constant in the static data. -/
theorem addScaled (hd : FieldT.ClmulTable env) :
    AddScaledT.SpecT env (liftProg fns) Idx.Verifier.Layout.Form.AddScaled Needs.Verifier.Layout.Form.AddScaled :=
  AddScaledT.total env _ _ Verifier.Layout.Form.AddScaled.link Verifier.Layout.Form.AddScaled.tmpl_eq
    Verifier.Layout.Form.AddScaled.wf (by decide) (by decide) (by decide) (by decide) (by decide)
    (RuntimeT.memcmp env) (FieldT.eMul env hd) (VecT.cloneUsize env hnext hend)
    (AllocT.growOneVecUsizeE env hnext hend) (MemT6a.memmoveWrapT env)

/-- **`<Form as SpecFromElem>::from_elem` at the image** (function 159, `vec![form; 3]` for an empty `form`), given
    its bound's word in the static data. -/
theorem fromElemForm (hd : DataRef.InData env
      [(Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal.link.d_c8_51ab739d,
        Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal.d_c8_51ab739d_words)]) :
    FromElemFormT.SpecT env (liftProg fns) Idx.Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal
      Needs.Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal :=
  FromElemFormT.total env _ _ Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal.link
    Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal.tmpl_eq
    Alloc.Vec.SpecFromElem.Form.AsSpecFromElem.FromElemGlobal.wf hd (by decide) (by decide) (by decide)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveForm env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.FormT6a

/-- info: 'Rv64mc.Table.FormT6a.addScaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6a.addScaled

/-- info: 'Rv64mc.Table.FormT6a.fromElemForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6a.fromElemForm
