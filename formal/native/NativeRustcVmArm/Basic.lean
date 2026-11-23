module

public import NativeRustcArm.Spec.Keccak
public import NativeRustcVm.MemLemmas

/-!
# AArch64's memory predicates are the arch-independent ones

`NativeRustcArm`'s `Mapped`, `BytesAt`, `InRange`, `SameOutside`, `NoWrap`, `Apart` are
`NativeRustcVm`'s, word for word (`DataMem` is `Mem 64`): equal by `rfl`, so a fact of either is one
of the other (`bytesAt_iff`, …). Besides: `bytesOf` of known bytes, mapped bytes kept by `Saved`,
and the stack below SP as a range (`stackBelow_toNat`, `noWrap_stackBelow`).
-/

namespace NativeRustcVmArm

open NativeRustcArm

public section

theorem mapped_eq : NativeRustcArm.Mapped = NativeRustcVm.Mapped := rfl
theorem bytesAt_eq : NativeRustcArm.BytesAt = NativeRustcVm.BytesAt := rfl
theorem inRange_eq : NativeRustcArm.InRange = NativeRustcVm.InRange := rfl
theorem sameOutside_eq : NativeRustcArm.SameOutside = NativeRustcVm.SameOutside := rfl
theorem noWrap_eq : NativeRustcArm.NoWrap = NativeRustcVm.NoWrap := rfl
theorem apart_eq : NativeRustcArm.Apart = NativeRustcVm.Apart := rfl

variable {d d' : DataMem} {a : BitVec 64} {n : Nat} {bs : List UInt8}

theorem mapped_iff : NativeRustcArm.Mapped d a n ↔ NativeRustcVm.Mapped d a n := Iff.rfl
theorem bytesAt_iff : NativeRustcArm.BytesAt d a bs ↔ NativeRustcVm.BytesAt d a bs := Iff.rfl
theorem inRange_iff {p : BitVec 64} :
    NativeRustcArm.InRange a n p ↔ NativeRustcVm.InRange a n p := Iff.rfl
theorem sameOutside_iff {R : BitVec 64 → Prop} :
    NativeRustcArm.SameOutside d d' R ↔ NativeRustcVm.SameOutside d d' R := Iff.rfl
theorem noWrap_iff : NativeRustcArm.NoWrap a n ↔ NativeRustcVm.NoWrap a n := Iff.rfl
theorem apart_iff {a' : BitVec 64} {n' : Nat} :
    NativeRustcArm.Apart a n a' n' ↔ NativeRustcVm.Apart a n a' n' := Iff.rfl

/-- Mapped bytes are what `bytesOf` reads. -/
theorem bytesAt_bytesOf (h : NativeRustcVm.Mapped d a n) :
    NativeRustcVm.BytesAt d a (bytesOf d a n) := by
  intro i hi
  simp only [bytesOf, List.length_map, List.length_range] at hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  rw [hv]
  rfl

theorem length_bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : (bytesOf d a n).length = n := by
  simp [bytesOf]

/-- `bytesOf` reads the bytes there. -/
theorem bytesOf_eq (h : NativeRustcVm.BytesAt d a bs) : bytesOf d a bs.length = bs :=
  (bytesAt_bytesOf h.mapped).unique h (length_bytesOf _ _ _)

/-- Mapped bytes stay mapped across a call (`Saved`). -/
theorem Mapped.of_saved {m m' : MachineData} (h : NativeRustcVm.Mapped m.dmem a n)
    (hs : Saved m m') : NativeRustcVm.Mapped m'.dmem a n := fun i hi ↦ hs.2.2 _ (h i hi)

/-- The `n` bytes below SP as a number. -/
theorem stackBelow_toNat {m : MachineData} (h : n ≤ m.regs.SP.toNat) :
    (stackBelow m n).toNat = m.regs.SP.toNat - n :=
  NativeRustcVm.toNat_sub_ofNat h

/-- The `n` bytes below SP do not wrap around. -/
theorem noWrap_stackBelow {m : MachineData} (h : StackOk m n) :
    NativeRustcVm.NoWrap (stackBelow m n) n := by
  unfold NativeRustcVm.NoWrap
  rw [stackBelow_toNat h.2.1]
  have := m.regs.SP.toNat_lt
  have := h.2.1
  omega

theorem mapped_stackBelow {m : MachineData} (h : StackOk m n) :
    NativeRustcVm.Mapped m.dmem (stackBelow m n) n := h.2.2

end

end NativeRustcVmArm
