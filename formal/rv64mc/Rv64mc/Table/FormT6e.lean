/-
  Rv64mc.Table.FormT6e

  `Form::term`'s, `constant`'s and `col`'s second total contracts at the image (`liftProg Gen.fns`), next to
  `LayoutT.lean`'s first ones: their postconditions with the result's buffers 8-byte aligned (`TermAlT.FormAl`). Left
  as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and, for `col`, `clmul_low`'s constant
  (`FieldT.ClmulTable`, through `gpow`).

  ## Main results

  * `termAl`, `constantAl`, `colAl`
-/

import Rv64mc.Table.LayoutT
import Rv64mc.Proof.Layout.ConstantAlT
import Rv64mc.Proof.Layout.ColAlT

namespace Rv64mc.Table.FormT6e

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Form::term` at the image**, its result's buffers aligned. -/
theorem termAl : TermAlT.specT env (liftProg fns) Idx.Verifier.Layout.Form.Term :=
  TermAlT.total env _ _ _ Verifier.Layout.Form.Term.tmpl_eq Verifier.Layout.Form.Term.wf
    (RuntimeT.alloc env hnext hend) (RuntimeT.panicNounwindFmt env)

/-- **`constant` at the image** (function 162), its result's buffers aligned. -/
theorem constantAl : ConstantAlT.specT env (liftProg fns) Idx.Verifier.Layout.Constant :=
  ConstantAlT.total env _ _ _ Verifier.Layout.Constant.tmpl_eq Verifier.Layout.Constant.wf (termAl env hnext hend)

/-- **`col` at the image** (function 179), its result's buffers aligned. -/
theorem colAl (hd : FieldT.ClmulTable env) :
    ColAlT.colSpecT env (liftProg fns) Idx.Verifier.Layout.Col Needs.Verifier.Layout.Col :=
  ColAlT.total env _ _ _ _ _ Verifier.Layout.Col.tmpl_eq Verifier.Layout.Col.wf (RuntimeT.alloc env hnext hend)
    (LayoutT.gpow env hd) (termAl env hnext hend) (RuntimeT.panicNounwindFmt env) (by decide) (by decide)

end Rv64mc.Table.FormT6e

/-- info: 'Rv64mc.Table.FormT6e.termAl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6e.termAl

/-- info: 'Rv64mc.Table.FormT6e.constantAl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6e.constantAl

/-- info: 'Rv64mc.Table.FormT6e.colAl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FormT6e.colAl
