module

public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Xmss.LayerRead.Names

public import NativeRustcX64.LayerRead.Head
public import NativeRustcX64.LayerRead.Loop
public import NativeRustcX64.LayerRead.Path
public import NativeRustcX64.LayerRead.Tail

/-!
# `LayerSignature::read` meets its slice-cursor contract

The prologue saves the output pointer and checks the input length. The chain loop consumes
58 digests, the path reads consume 16 more, and the final copies lay out the layer and restore
all six callee-saved registers. Both words of the mutable slice descriptor are advanced.
-/

namespace NativeRustcX64.Xmss.LayerRead

public theorem layerRead_spec [Host] {k : Nat} (hp : Placed code k)
    (hmemcpy : Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcX64.Xmss.LayerRead.entryLabel) LayerReadPre LayerReadPost := by
  intro m₀ hpre
  have P := pre_of hpre
  have G : ParserGot m₀ := hpre.2.2.2.2.2.2.2.2.2
  rw [hp.label entry_at, entryOffset, Nat.add_zero]
  exact head hp hpre fun st hpc h =>
    NativeRustcX64.Eventually.bind (loop hp P hpc h) fun st' ⟨hpc', h'⟩ =>
      mid hp hmemcpy P G hpc' h' fun st'' hpc'' h'' =>
        path hp P G hpc'' h'' fun s hs hret hc => tail hp hmemcpy P hs hret hc

/--
info: 'NativeRustcX64.Xmss.LayerRead.layerRead_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layerRead_spec

end NativeRustcX64.Xmss.LayerRead
