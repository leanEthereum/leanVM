import Rv64Verifier.Proofs.Runtime.Alloc
import Rv64Verifier.Proofs.Runtime.TryAlloc
import Rv64Verifier.Proofs.Runtime.TryAllocZeroed
import Rv64Verifier.Proofs.Runtime.FinishGrow
import Rv64Verifier.Proofs.Runtime.Grow
import Rv64Verifier.Proofs.Runtime.GrowOne
import Rv64Verifier.Proofs.Runtime.Reserve
import Rv64Verifier.Proofs.Runtime.Drop
import Rv64Verifier.Proofs.Runtime.Memset
import Rv64Verifier.Proofs.Runtime.Memcmp
import Rv64Verifier.Proofs.Runtime.Memcpy
import Rv64Verifier.Proofs.Runtime.Wrap

/-!
# The runtime, composed

Each function's proof takes its callees' contracts; here they are put together, down to what is
not proved: `memcpy` for a source and destination that differ modulo 8 (its shifting path), and
`memmove`.
-/

namespace Rv64Verifier.Runtime
open Rv64Verifier.Runtime

theorem tryAlloc : TryAllocSpec := TryAlloc.try_alloc_spec alloc_spec

theorem tryAllocZeroed : TryAllocZeroedSpec :=
  TryAllocZeroed.try_alloc_zeroed_spec alloc_spec (Wrap.memset_wrap Memset.memset_spec)

theorem memset : MemsetSpec 0x800126f4 := Wrap.memset_wrap Memset.memset_spec

/-- `grow_amortized`, given `memcpy`'s contract. -/
theorem grow (hC : MemcpySpec 0x80011ff8) : GrowSpec :=
  Grow.grow_spec (FinishGrow.finish_grow_spec alloc_spec (Wrap.memcpy_wrap hC))

theorem dropLayout : DropLayoutSpec := Drop.drop_layout_spec Drop.drop_nop_spec

end Rv64Verifier.Runtime

/-- info: 'Rv64Verifier.Runtime.alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.alloc_spec

/-- info: 'Rv64Verifier.Runtime.tryAlloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.tryAlloc

/-- info: 'Rv64Verifier.Runtime.tryAllocZeroed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.tryAllocZeroed

/-- info: 'Rv64Verifier.Runtime.grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.grow

/-- info: 'Rv64Verifier.Runtime.GrowOne.grow_one_80011f88' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.GrowOne.grow_one_80011f88

/-- info: 'Rv64Verifier.Runtime.Reserve.reserve_8000c898' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.Reserve.reserve_8000c898

/-- info: 'Rv64Verifier.Runtime.dropLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.dropLayout

/-- info: 'Rv64Verifier.Runtime.memset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.memset

/-- info: 'Rv64Verifier.Runtime.Memcmp.memcmp_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.Memcmp.memcmp_spec

/-- info: 'Rv64Verifier.Runtime.Memcpy.memcpy_coaligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.Memcpy.memcpy_coaligned

/-- info: 'Rv64Verifier.Runtime.Wrap.memmove_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.Wrap.memmove_wrap
