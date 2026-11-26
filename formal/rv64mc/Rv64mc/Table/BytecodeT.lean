/-
  Rv64mc.Table.BytecodeT

  `bytecode.rs`'s total contracts at the image (`liftProg Gen.fns`), new in wave 5a, each at its index with the
  generated link, the stack `Gen.Needs` gives, and its callees' total theorems (`AllocT`, `RuntimeT`, `CopyUseT`).
  Left as hypotheses, environment facts: `alloc`'s two (`RuntimeT.alloc`).

  ## Main results

  * `countingSortUsize`, `countingSortPairs`
-/

import Rv64mc.Table.AllocT
import Rv64mc.Proof.Bytecode.CountingSortUsizeT
import Rv64mc.Proof.Bytecode.CountingSortPairsT
import Rv64mc.Gen.Link.Verifier.Bytecode

namespace Rv64mc.Table.BytecodeT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Bytecode

variable (env : Env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
  (hend : env.heapEnd = 0x78000000#64)
include hnext hend

/-- **`counting_sort::<usize, block_members::{closure#0}>` at the image** (function 219). -/
theorem countingSortUsize :
    CountingSortUsizeT.SpecT env (liftProg fns) Idx.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0
      Needs.Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0 :=
  CountingSortUsizeT.total env _ _ Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0.link
    Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0.tmpl_eq
    Verifier.Bytecode.CountingSortUsizeBlockMembersClosure0.wf (by decide) (by decide) (by decide) (by decide)
    (by decide) (Table.AllocT.tryAllocateIn env hnext hend) (Table.RuntimeT.alloc env hnext hend)
    (Table.CopyUseT.memcpy env) (Table.RuntimeT.panicBoundsCheck env) (Table.RuntimeT.handleError env)

/-- **`counting_sort::<(u64, u16), group_by_word::{closure#2}>` at the image** (function 220). -/
theorem countingSortPairs :
    CountingSortPairsT.SpecT env (liftProg fns) Idx.Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2
      Needs.Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2 :=
  CountingSortPairsT.total env _ _ Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2.link
    Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2.tmpl_eq
    Verifier.Bytecode.CountingSortTU64U16EGroupByWordClosure2.wf (by decide) (by decide) (by decide) (by decide)
    (by decide) (Table.RuntimeT.alloc env hnext hend) (Table.RuntimeT.memset env) (Table.CopyUseT.memcpy env)
    (Table.RuntimeT.panicBoundsCheck env) (Table.RuntimeT.handleError env)

end Rv64mc.Table.BytecodeT

/-- info: 'Rv64mc.Table.BytecodeT.countingSortUsize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BytecodeT.countingSortUsize

/-- info: 'Rv64mc.Table.BytecodeT.countingSortPairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BytecodeT.countingSortPairs
