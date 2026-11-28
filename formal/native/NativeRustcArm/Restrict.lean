module

public import NativeRustcArm.Basic
public import NativeRustc.ReadRegions

/-!
# Memory restriction helpers for AArch64 confinement proofs
-/

namespace NativeRustcArm

public section

theorem BytesAt.restrict {d : DataMem} {a : BitVec 64} {bs : List UInt8}
    (h : BytesAt d a bs) {areas : List (BitVec 64 × Nat)}
    (ha : (a, bs.length) ∈ areas) : BytesAt (NativeRustc.restrictMemory d areas) a bs := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

theorem Mapped.restrict {d : DataMem} {a : BitVec 64} {n : Nat}
    (h : Mapped d a n) {areas : List (BitVec 64 × Nat)}
    (ha : (a, n) ∈ areas) : Mapped (NativeRustc.restrictMemory d areas) a n := by
  intro i hi
  rw [NativeRustc.restrictMemory_inside d ha hi]
  exact h i hi

end

end NativeRustcArm
