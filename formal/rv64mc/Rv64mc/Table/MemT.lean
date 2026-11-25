/-
  Rv64mc.Table.MemT

  The total contracts of `compiler_builtins`' memory functions at the image: `memcpy` (`MemcpySpecT`, with the bytes
  copied) and `memset` (`MemsetSafeT`), each at its index and its generator's stack need. Both are leaves, so no
  hypothesis is left.

  ## Main results

  * `memcpyT`, `memsetT`
-/

import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Misc

namespace Rv64mc.Table.MemT

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

/-- **`compiler_builtins`' `memcpy` at the image** (function 223). -/
theorem memcpyT : Proof.Runtime.MemcpyT.MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy
    Needs.CompilerBuiltins.Mem.Memcpy :=
  HoldsT.mono_need (Proof.Runtime.MemcpyT.total CompilerBuiltins.Mem.Memcpy.tmpl_eq) (by decide)

/-- **`compiler_builtins`' `memset` at the image** (function 224). -/
theorem memsetT : Proof.Runtime.MemsetT.MemsetSafeT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memset
    Needs.CompilerBuiltins.Mem.Memset :=
  HoldsT.mono_need (Proof.Runtime.MemsetT.total _ _ _ CompilerBuiltins.Mem.Memset.tmpl_eq) (Nat.zero_le _)

end Rv64mc.Table.MemT

/-- info: 'Rv64mc.Table.MemT.memcpyT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MemT.memcpyT

/-- info: 'Rv64mc.Table.MemT.memsetT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MemT.memsetT
