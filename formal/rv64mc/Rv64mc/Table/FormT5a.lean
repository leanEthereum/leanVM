/-
  Rv64mc.Table.FormT5a

  The total contracts of the functions over `Form`s (`layout.rs`) new in wave 5a at the image (`liftProg Gen.fns`),
  each at its index with the generated link, the stack `Gen.Needs` gives, and its callees' total theorems
  (`RuntimeT`, `VecT`). Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and, for
  `Vec<Form>::clone`, its two bounds' words in the static data (`DataRef.InData`).

  ## Main results

  * `cloneForms`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Table.VecT
import Rv64mc.Proof.Layout.CloneFormsT
import Rv64mc.Gen.Link.Alloc.Vec

namespace Rv64mc.Table.FormT5a

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`<Vec<Form> as Clone>::clone` at the image** (function 168), given its two bounds' words in the static
    data. -/
theorem cloneForms (hd : DataRef.InData env
      [(Alloc.Vec.VecForm.AsClone.Clone.link.d_c8_d6dfd6bc, Alloc.Vec.VecForm.AsClone.Clone.d_c8_d6dfd6bc_words),
        (Alloc.Vec.VecForm.AsClone.Clone.link.d_c8_51ab739d, Alloc.Vec.VecForm.AsClone.Clone.d_c8_51ab739d_words)]) :
    CloneFormsT.SpecT env (liftProg fns) Idx.Alloc.Vec.VecForm.AsClone.Clone Needs.Alloc.Vec.VecForm.AsClone.Clone :=
  CloneFormsT.total env _ _ Alloc.Vec.VecForm.AsClone.Clone.link Alloc.Vec.VecForm.AsClone.Clone.tmpl_eq
    Alloc.Vec.VecForm.AsClone.Clone.wf hd (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend)
    (VecT.cloneUsize env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.FormT5a

/-- info: 'Rv64mc.Table.FormT5a.cloneForms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT5a.cloneForms
