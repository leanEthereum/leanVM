module

public import Kraken.Mem

namespace NativeRustc

public section

/-- The bytes in the listed regions, with modular machine addresses. -/
def ReadRegions (areas : List (BitVec 64 × Nat)) (p : BitVec 64) : Prop :=
  ∃ a ∈ areas, ∃ i < a.2, p = a.1 + BitVec.ofNat 64 i

/-- Remove all data memory outside the listed regions. -/
noncomputable def restrictMemory (d : Mem 64) (areas : List (BitVec 64 × Nat)) : Mem 64 := by
  classical
  exact d.filter fun p _ => decide (ReadRegions areas p)

theorem restrictMemory_inside (d : Mem 64) {areas : List (BitVec 64 × Nat)}
    {a : BitVec 64} {n i : Nat} (ha : (a, n) ∈ areas) (hi : i < n) :
    (restrictMemory d areas).get? (a + BitVec.ofNat 64 i) =
      d.get? (a + BitVec.ofNat 64 i) := by
  classical
  have h : ReadRegions areas (a + BitVec.ofNat 64 i) := ⟨(a, n), ha, i, hi, rfl⟩
  simp only [restrictMemory, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.getElem?_filter', h, decide_true]
  cases d[a + BitVec.ofNat 64 i]? <;> rfl

theorem restrictMemory_outside (d : Mem 64) {areas : List (BitVec 64 × Nat)}
    {p : BitVec 64} (hp : ¬ ReadRegions areas p) :
    (restrictMemory d areas).get? p = none := by
  classical
  simp [restrictMemory, Std.ExtHashMap.getElem?_filter', hp]

end

end NativeRustc
