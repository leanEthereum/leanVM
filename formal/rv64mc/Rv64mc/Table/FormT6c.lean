/-
  Rv64mc.Table.FormT6c

  The total contracts of the functions over `Form`s (`layout.rs`) new in wave 6c at the image (`liftProg Gen.fns`),
  each at its index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems. Left as
  hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and, for `Vec<Form>::spec_extend`, its bound's word
  (`isize::MAX / 40`) in the static data (`DataRef.InData`).

  ## Main results

  * `specExtendForm`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.VecT
import Rv64mc.Table.AllocT
import Rv64mc.Proof.Layout.SpecExtendFormT
import Rv64mc.Gen.Link.Alloc.Vec

namespace Rv64mc.Table.FormT6c

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`<Vec<Form> as SpecExtend<&Form, slice::Iter<Form>>>::spec_extend` at the image** (function 202), given its
    bound's word in the static data. -/
theorem specExtendForm (hd : DataRef.InData env
      [(Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.link.d_c8_51ab739d,
        Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.d_c8_51ab739d_words)]) :
    SpecExtendFormT.SpecT env (liftProg fns) Idx.Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend
      Needs.Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend :=
  SpecExtendFormT.total env _ _ Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.link
    Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.tmpl_eq
    Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.wf hd (by decide) (by decide) (by decide)
    (by decide) (AllocT.reserveForm env hnext hend) (RuntimeT.alloc env hnext hend) (VecT.cloneUsize env hnext hend)
    (RuntimeT.handleError env)

end Rv64mc.Table.FormT6c

/-- info: 'Rv64mc.Table.FormT6c.specExtendForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6c.specExtendForm
