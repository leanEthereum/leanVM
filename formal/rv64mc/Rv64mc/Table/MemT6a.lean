/-
  Rv64mc.Table.MemT6a

  `compiler_builtins`' `memmove` at the image, total with the bytes copied (`MemmoveSpecT`, proved by
  `Proof/Runtime/MemmoveProofT.lean`), and its C wrapper `memmove` (`Table/RuntimeT.lean`'s `memmove`, which took
  the first as a hypothesis) instantiated over it. Both are leaves of the call graph but for the wrapper's tail call,
  so no hypothesis is left.

  ## Main results

  * `memmoveT`, `memmoveWrapT`
-/

import Rv64mc.Proof.Runtime.MemmoveProofT
import Rv64mc.Table.RuntimeT

namespace Rv64mc.Table.MemT6a

open MachineChecked.RiscV.Lift Rv64mc.Gen
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)

variable (env : Env)

/-- **`compiler_builtins`' `memmove` at the image** (function 225). -/
theorem memmoveT : MemmoveSpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memmove
    Needs.CompilerBuiltins.Mem.Memmove :=
  HoldsT.mono_need (Proof.Runtime.MemmoveProofT.total CompilerBuiltins.Mem.Memmove.tmpl_eq) (by decide)

/-- **The C `memmove` at the image** (function 228), over `memmoveT`. -/
theorem memmoveWrapT : MemmoveSpecT env (liftProg fns) Idx.Memmove Needs.Memmove :=
  RuntimeT.memmove env (memmoveT env)

end Rv64mc.Table.MemT6a

/-- info: 'Rv64mc.Table.MemT6a.memmoveT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MemT6a.memmoveT

/-- info: 'Rv64mc.Table.MemT6a.memmoveWrapT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MemT6a.memmoveWrapT
