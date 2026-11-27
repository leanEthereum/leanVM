/-
  Rv64mc.Table.FlushesT6e

  `Flushes::pair` over a `Flushes` of `Form`s (`PairFormT`) at the image (`liftProg Gen.fns`), from its total
  contract there (`FlushesT.pair`), and `Flushes::state_derived` (`StateDerivedT`) over it and the aligned `Form`
  builders (`FormT6e`), and `Flushes::state_step` (`StateStepT`) over both. Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`, through `grow_one`)
  and, for `state_derived` and `state_step`, `clmul_low`'s constant (`FieldT.ClmulTable`, through `col`).

  ## Main results

  * `pairForm`, `stateDerived`, `stateStep`
-/

import Rv64mc.Table.FlushesT
import Rv64mc.Table.FormT6e
import Rv64mc.Proof.Layout.PairFormT
import Rv64mc.Proof.Layout.StateStepT

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
