module

public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Xmss.LayerRead.Names

public import NativeRustcArm.LayerRead.Head
public import NativeRustcArm.LayerRead.Loop
public import NativeRustcArm.LayerRead.Path
public import NativeRustcArm.LayerRead.Tail

/-!
# `LayerSignature::read` meets its contract

The proof composes the prologue, chain loop, intermediate copy, unrolled
path and final copies. Slice-length bounds rule out every panic branch.
-/

namespace NativeRustcArm.Xmss.LayerRead

open NativeRustcArm

/-- The reader meets the slice-cursor ABI contract. -/
public theorem layerRead_spec [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcArm.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost := by
  intro m₀ hpre
  have P := pre_of hpre
  rw [hp.label NativeRustcArm.Xmss.LayerRead.entry_at, NativeRustcArm.Xmss.LayerRead.entryOffset, Nat.add_zero]
  exact head hp hpre fun st hpc h =>
    Eventually.bind (loop hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      mid hp hmemcpy P hpc' h' fun st'' hpc'' h'' =>
        path hp P hpc'' h'' fun s hs hret hc => tail hp hmemcpy P hs hret hc

end NativeRustcArm.Xmss.LayerRead
