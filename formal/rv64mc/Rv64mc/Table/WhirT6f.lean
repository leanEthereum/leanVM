/-
  Rv64mc.Table.WhirT6f

  Wave 6f's WHIR functions' total contracts at the image (`liftProg Gen.fns`): each function's total theorem at its
  index, with the generated link, the stack `Gen.Needs` gives (bounds over the callees' by `decide`), and the callees'
  total theorems (`WhirT6b.novelBasis`, `SumT6f.eSumNovel`). Open: `clmul_low`'s table (`FieldT.ClmulTable`), `NEXT`'s
  data reference and the heap's end (`env`): environment facts.

  ## Main results

  * `novelEval`
-/

import Rv64mc.Table.WhirT6b
import Rv64mc.Table.SumT6f
import Rv64mc.Proof.Whir.NovelEvalT
import Rv64mc.Gen.Link.Verifier.Whir

namespace Rv64mc.Table.WhirT6f

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

/-- `novel_eval` (80). -/
theorem novelEval (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    NovelEvalT.specT env (liftProg fns) Idx.Verifier.Whir.NovelEval Needs.Verifier.Whir.NovelEval :=
  NovelEvalT.total env _ _ _ Verifier.Whir.NovelEval.tmpl_eq Verifier.Whir.NovelEval.wf (by decide) (by decide)
    (WhirT6b.novelBasis env hd hnext hend) (SumT6f.eSumNovel env hd)

end Rv64mc.Table.WhirT6f

/-- info: 'Rv64mc.Table.WhirT6f.novelEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6f.novelEval
