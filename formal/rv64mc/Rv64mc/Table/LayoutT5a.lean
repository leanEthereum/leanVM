/-
  Rv64mc.Table.LayoutT5a

  `layout.rs`'s total contracts at the image (`liftProg Gen.fns`) new in wave 5a, each at its index with the generated
  link, the stack `Gen.Needs` gives, and its callees' total theorems (`LayoutT`, `AllocT`, `RuntimeT`, `CopyUseT`).
  Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`) and, for `column_kappas`, the
  `TABLE_WIDTHS` table in the static data (`DataRef.InData`, as `LayoutT.countColumns` takes `COUNT_COLUMNS`).

  ## Main results

  * `columnKappas`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Table.LayoutT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Layout.ColumnKappasT
import Rv64mc.Gen.Link.Verifier.Layout

namespace Rv64mc.Table.LayoutT5a

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`column_kappas` at the image** (function 181), given `TABLE_WIDTHS` in the static data. -/
theorem columnKappas (hd : DataRef.InData env [(Verifier.Layout.ColumnKappas.link.d_c48_a47cc263,
      Verifier.Layout.ColumnKappas.d_c48_a47cc263_words)]) :
    ColumnKappasT.SpecT env (liftProg fns) Idx.Verifier.Layout.ColumnKappas Needs.Verifier.Layout.ColumnKappas :=
  ColumnKappasT.total env _ _ Verifier.Layout.ColumnKappas.link Verifier.Layout.ColumnKappas.tmpl_eq
    Verifier.Layout.ColumnKappas.wf hd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Table.LayoutT.keccakShape env) (Table.RuntimeT.alloc env hnext hend)
    (Table.AllocT.tryAllocateIn env hnext hend) (Table.AllocT.reserveUsize env hnext hend) (Table.CopyUseT.memcpy env)
    (Table.RuntimeT.handleError env) (Table.RuntimeT.panicNounwindFmt env) (Table.RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.LayoutT5a

/-- info: 'Rv64mc.Table.LayoutT5a.columnKappas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT5a.columnKappas
