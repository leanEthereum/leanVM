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
import Rv64Verifier.Proofs.Runtime.Copy

/-!
# The runtime, composed

Each function's proof takes its callees' contracts; here they are put together: every contract
of `Contracts.lean` is proved, with no hypothesis.
-/

namespace Rv64Verifier.Runtime
open Rv64Verifier.Runtime

theorem tryAlloc : TryAllocSpec := TryAlloc.try_alloc_spec alloc_tight

theorem tryAllocNext : TryAllocNextSpec := TryAlloc.try_alloc_next alloc_tight

theorem tryAllocZeroed : TryAllocZeroedSpec :=
  TryAllocZeroed.try_alloc_zeroed_spec alloc_spec (Wrap.memset_wrap Memset.memset_spec)

theorem memset : MemsetSpec 0x800126f4 := Wrap.memset_wrap Memset.memset_spec

/-- `grow_amortized`, given `memcpy`'s contract. -/
theorem grow (hC : MemcpySpec 0x80011ff8) : GrowSpec :=
  Grow.grow_spec (FinishGrow.finish_grow_spec alloc_spec (Wrap.memcpy_wrap hC))

theorem memcpy : MemcpySpec 0x800126e4 := Wrap.memcpy_wrap memcpy_spec

theorem memmove : MemmoveSpec 0x800126ec := Wrap.memmove_wrap memmove_spec

theorem growAmortized : GrowSpec := grow memcpy_spec

theorem growOneFresh_8000c0a4 : GrowOneFreshSpec 0x8000c0a4 56 8 :=
  GrowOne.grow_one_8000c0a4 growAmortized
theorem growOne_8000c0a4 : GrowOneSpec 0x8000c0a4 56 8 :=
  growOneFresh_8000c0a4.weaken fun _ _ h ↦ h.1
theorem growOneFresh_8000c7d0 : GrowOneFreshSpec 0x8000c7d0 80 8 :=
  GrowOne.grow_one_8000c7d0 growAmortized
theorem growOne_8000c7d0 : GrowOneSpec 0x8000c7d0 80 8 :=
  growOneFresh_8000c7d0.weaken fun _ _ h ↦ h.1
theorem growOneFresh_8000d7bc : GrowOneFreshSpec 0x8000d7bc 8 8 :=
  GrowOne.grow_one_8000d7bc growAmortized
theorem growOne_8000d7bc : GrowOneSpec 0x8000d7bc 8 8 :=
  growOneFresh_8000d7bc.weaken fun _ _ h ↦ h.1
theorem growOneFresh_8000db78 : GrowOneFreshSpec 0x8000db78 88 8 :=
  GrowOne.grow_one_8000db78 growAmortized
theorem growOne_8000db78 : GrowOneSpec 0x8000db78 88 8 :=
  growOneFresh_8000db78.weaken fun _ _ h ↦ h.1
theorem growOneFresh_80010a94 : GrowOneFreshSpec 0x80010a94 48 8 :=
  GrowOne.grow_one_80010a94 growAmortized
theorem growOne_80010a94 : GrowOneSpec 0x80010a94 48 8 :=
  growOneFresh_80010a94.weaken fun _ _ h ↦ h.1
theorem growOneFresh_80011c78 : GrowOneFreshSpec 0x80011c78 24 8 :=
  GrowOne.grow_one_80011c78 growAmortized
theorem growOne_80011c78 : GrowOneSpec 0x80011c78 24 8 :=
  growOneFresh_80011c78.weaken fun _ _ h ↦ h.1
theorem growOneFresh_80011f88 : GrowOneFreshSpec 0x80011f88 2 2 :=
  GrowOne.grow_one_80011f88 growAmortized
theorem growOne_80011f88 : GrowOneSpec 0x80011f88 2 2 :=
  growOneFresh_80011f88.weaken fun _ _ h ↦ h.1
theorem growOneFresh_80011fc0 : GrowOneFreshSpec 0x80011fc0 16 8 :=
  GrowOne.grow_one_80011fc0 growAmortized
theorem growOne_80011fc0 : GrowOneSpec 0x80011fc0 16 8 :=
  growOneFresh_80011fc0.weaken fun _ _ h ↦ h.1

theorem reserveFresh_80004aec : ReserveFreshSpec 0x80004aec 24 8 :=
  Reserve.reserve_80004aec growAmortized
theorem reserve_80004aec : ReserveSpec 0x80004aec 24 8 :=
  reserveFresh_80004aec.weaken fun _ _ h ↦ h.1
theorem reserveFast_80004aec : ReserveFastSpec 0x80004aec := Reserve.reserve_fast_80004aec
theorem reserveFresh_800060bc : ReserveFreshSpec 0x800060bc 48 8 :=
  Reserve.reserve_800060bc growAmortized
theorem reserve_800060bc : ReserveSpec 0x800060bc 48 8 :=
  reserveFresh_800060bc.weaken fun _ _ h ↦ h.1
theorem reserveFast_800060bc : ReserveFastSpec 0x800060bc := Reserve.reserve_fast_800060bc
theorem reserveFresh_80008a10 : ReserveFreshSpec 0x80008a10 24 8 :=
  Reserve.reserve_80008a10 growAmortized
theorem reserve_80008a10 : ReserveSpec 0x80008a10 24 8 :=
  reserveFresh_80008a10.weaken fun _ _ h ↦ h.1
theorem reserveFast_80008a10 : ReserveFastSpec 0x80008a10 := Reserve.reserve_fast_80008a10
theorem reserveFresh_8000c898 : ReserveFreshSpec 0x8000c898 1 1 :=
  Reserve.reserve_8000c898 growAmortized
theorem reserve_8000c898 : ReserveSpec 0x8000c898 1 1 :=
  reserveFresh_8000c898.weaken fun _ _ h ↦ h.1
theorem reserveFast_8000c898 : ReserveFastSpec 0x8000c898 := Reserve.reserve_fast_8000c898
theorem reserveFresh_8000d628 : ReserveFreshSpec 0x8000d628 8 8 :=
  Reserve.reserve_8000d628 growAmortized
theorem reserve_8000d628 : ReserveSpec 0x8000d628 8 8 :=
  reserveFresh_8000d628.weaken fun _ _ h ↦ h.1
theorem reserveFast_8000d628 : ReserveFastSpec 0x8000d628 := Reserve.reserve_fast_8000d628
theorem reserveFresh_8001086c : ReserveFreshSpec 0x8001086c 32 8 :=
  Reserve.reserve_8001086c growAmortized
theorem reserve_8001086c : ReserveSpec 0x8001086c 32 8 :=
  reserveFresh_8001086c.weaken fun _ _ h ↦ h.1
theorem reserveFast_8001086c : ReserveFastSpec 0x8001086c := Reserve.reserve_fast_8001086c

theorem dropLayout : DropLayoutSpec := Drop.drop_layout_spec Drop.drop_nop_spec

end Rv64Verifier.Runtime

/-- info: 'Rv64Verifier.Runtime.alloc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.alloc_spec

/-- info: 'Rv64Verifier.Runtime.tryAlloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.tryAlloc

/-- info: 'Rv64Verifier.Runtime.tryAllocNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.tryAllocNext

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

/-- info: 'Rv64Verifier.Runtime.memcpy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.memcpy

/-- info: 'Rv64Verifier.Runtime.memmove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.memmove

/-- info: 'Rv64Verifier.Runtime.growAmortized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growAmortized

/-- info: 'Rv64Verifier.Runtime.growOne_8000c0a4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_8000c0a4

/-- info: 'Rv64Verifier.Runtime.growOne_8000c7d0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_8000c7d0

/-- info: 'Rv64Verifier.Runtime.growOne_8000d7bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_8000d7bc

/-- info: 'Rv64Verifier.Runtime.growOne_8000db78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_8000db78

/-- info: 'Rv64Verifier.Runtime.growOne_80010a94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_80010a94

/-- info: 'Rv64Verifier.Runtime.growOne_80011c78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_80011c78

/-- info: 'Rv64Verifier.Runtime.growOne_80011f88' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_80011f88

/-- info: 'Rv64Verifier.Runtime.growOne_80011fc0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOne_80011fc0

/-- info: 'Rv64Verifier.Runtime.reserve_80004aec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_80004aec

/-- info: 'Rv64Verifier.Runtime.reserve_800060bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_800060bc

/-- info: 'Rv64Verifier.Runtime.reserve_80008a10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_80008a10

/-- info: 'Rv64Verifier.Runtime.reserve_8000c898' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_8000c898

/-- info: 'Rv64Verifier.Runtime.reserve_8000d628' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_8000d628

/-- info: 'Rv64Verifier.Runtime.reserve_8001086c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserve_8001086c

/-- info: 'Rv64Verifier.Runtime.growOneFresh_8000c0a4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_8000c0a4

/-- info: 'Rv64Verifier.Runtime.growOneFresh_8000c7d0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_8000c7d0

/-- info: 'Rv64Verifier.Runtime.growOneFresh_8000d7bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_8000d7bc

/-- info: 'Rv64Verifier.Runtime.growOneFresh_8000db78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_8000db78

/-- info: 'Rv64Verifier.Runtime.growOneFresh_80010a94' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_80010a94

/-- info: 'Rv64Verifier.Runtime.growOneFresh_80011c78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_80011c78

/-- info: 'Rv64Verifier.Runtime.growOneFresh_80011f88' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_80011f88

/-- info: 'Rv64Verifier.Runtime.growOneFresh_80011fc0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.growOneFresh_80011fc0

/-- info: 'Rv64Verifier.Runtime.reserveFresh_80004aec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_80004aec

/-- info: 'Rv64Verifier.Runtime.reserveFresh_800060bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_800060bc

/-- info: 'Rv64Verifier.Runtime.reserveFresh_80008a10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_80008a10

/-- info: 'Rv64Verifier.Runtime.reserveFresh_8000c898' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_8000c898

/-- info: 'Rv64Verifier.Runtime.reserveFresh_8000d628' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_8000d628

/-- info: 'Rv64Verifier.Runtime.reserveFresh_8001086c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFresh_8001086c

/-- info: 'Rv64Verifier.Runtime.reserveFast_80004aec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_80004aec

/-- info: 'Rv64Verifier.Runtime.reserveFast_800060bc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_800060bc

/-- info: 'Rv64Verifier.Runtime.reserveFast_80008a10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_80008a10

/-- info: 'Rv64Verifier.Runtime.reserveFast_8000c898' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_8000c898

/-- info: 'Rv64Verifier.Runtime.reserveFast_8000d628' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_8000d628

/-- info: 'Rv64Verifier.Runtime.reserveFast_8001086c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Runtime.reserveFast_8001086c
