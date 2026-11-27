/-
  Rv64mc.Table.FlushesT6e

  `Flushes::pair` over a `Flushes` of `Form`s (`PairFormT`) at the image (`liftProg Gen.fns`), from its total
  contract there (`FlushesT.pair`), and `Flushes::state_derived` (`StateDerivedT`) over it and the aligned `Form`
  builders (`FormT6e`), `Flushes::state_step` (`StateStepT`) over both, and `Flushes::counted` (`CountedT`) over
  `concat` (`FormT6e.concatForm`), `col` and `pair`. Left as hypotheses, environment facts: `alloc`'s two
  (`RuntimeT.alloc`, through `grow_one`) and, for `state_derived`, `state_step` and `counted`, `clmul_low`'s constant
  (`FieldT.ClmulTable`, through `col`); for `counted`, `concat`'s and `spec_extend`'s bounds' words in the static
  data (`DataRef.InData`).

  ## Main results

  * `pairForm`, `stateDerived`, `stateStep`, `counted`
-/

import Rv64mc.Table.FlushesT
import Rv64mc.Table.FormT6e
import Rv64mc.Proof.Layout.PairFormT
import Rv64mc.Proof.Layout.StateStepT
import Rv64mc.Proof.Layout.CountedT

namespace Rv64mc.Table.FlushesT6e

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`Flushes::pair` at the image** (function 200), keeping a `Flushes` of `Form`s. -/
theorem pairForm :
    PairFormT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.Pair Needs.Verifier.Layout.Flushes.Pair :=
  PairFormT.SpecT.of_pairT (FlushesT.pair env hnext hend)

/-- **`Flushes::state_derived` at the image** (function 194). -/
theorem stateDerived (hd : FieldT.ClmulTable env) :
    StateDerivedT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.StateDerived
      Needs.Verifier.Layout.Flushes.StateDerived :=
  StateDerivedT.total env _ _ _ Verifier.Layout.Flushes.StateDerived.tmpl_eq Verifier.Layout.Flushes.StateDerived.wf
    (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend) (FormT6e.constantAl env hnext hend)
    (FormT6e.colAl env hnext hend hd) (pairForm env hnext hend) (RuntimeT.panicNounwindFmt env)

/-- **`Flushes::state_step` at the image** (function 205). -/
theorem stateStep (hd : FieldT.ClmulTable env) :
    StateStepT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.StateStep Needs.Verifier.Layout.Flushes.StateStep :=
  StateStepT.total env _ _ _ Verifier.Layout.Flushes.StateStep.tmpl_eq Verifier.Layout.Flushes.StateStep.wf
    (by decide) (by decide) (FormT6e.colAl env hnext hend hd) (stateDerived env hnext hend hd)

/-- **`Flushes::counted` at the image** (function 198), given `concat`'s and `spec_extend`'s bounds' words in the
    static data. -/
theorem counted (hd : FieldT.ClmulTable env)
    (hdc : DataRef.InData env [(Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat.link.d_c8_d6dfd6bc,
      Alloc.Slice.SliceRefSliceForm.AsConcatForm.Concat.d_c8_d6dfd6bc_words)])
    (hds : DataRef.InData env
      [(Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.link.d_c8_51ab739d,
        Alloc.Vec.SpecExtend.VecForm.AsSpecExtendRefFormIterForm.SpecExtend.d_c8_51ab739d_words)]) :
    CountedT.SpecT env (liftProg fns) Idx.Verifier.Layout.Flushes.Counted Needs.Verifier.Layout.Flushes.Counted :=
  CountedT.total env _ _ _ Verifier.Layout.Flushes.Counted.tmpl_eq Verifier.Layout.Flushes.Counted.wf
    (by decide) (by decide) (by decide) (FormT6e.concatForm env hnext hend hdc hds) (FormT6e.colAl env hnext hend hd)
    (pairForm env hnext hend)

end Rv64mc.Table.FlushesT6e

/-- info: 'Rv64mc.Table.FlushesT6e.pairForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6e.pairForm

/-- info: 'Rv64mc.Table.FlushesT6e.stateDerived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6e.stateDerived

/-- info: 'Rv64mc.Table.FlushesT6e.stateStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6e.stateStep

/-- info: 'Rv64mc.Table.FlushesT6e.counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FlushesT6e.counted
