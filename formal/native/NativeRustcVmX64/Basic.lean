module

public import NativeRustcX64.Spec.Keccak
public import NativeRustcVm.MemLemmas
public import NativeRustcVm.Arrays.Read

/-!
# x86-64's memory predicates are the arch-independent ones

`NativeRustcX64`'s `Mapped`, `BytesAt`, `InRange`, `SameOutside`, `NoWrap`, `Apart` are
`NativeRustcVm`'s, word for word (`DataMem` is `Mem 64`): equal by `rfl`, so a fact of either is one
of the other (`bytesAt_iff`, …). Besides: `bytesOf` of known bytes, mapped bytes kept by `Saved`,
and the stack below RSP with the return address at RSP as a range (`stackBelow_toNat`,
`noWrap_stackBelow`, `mapped_stackBelow`: the `n + 8` bytes from `stackBelow m n`). A `bool`
result is AL (`boolRet`); argument words past the sixth are on the stack above the return address
(`stackArg`, mapped by `ArgsOk`).
-/

namespace NativeRustcVmX64

open NativeRustcX64

public section

theorem mapped_eq : NativeRustcX64.Mapped = NativeRustcVm.Mapped := rfl
theorem bytesAt_eq : NativeRustcX64.BytesAt = NativeRustcVm.BytesAt := rfl
theorem inRange_eq : NativeRustcX64.InRange = NativeRustcVm.InRange := rfl
theorem sameOutside_eq : NativeRustcX64.SameOutside = NativeRustcVm.SameOutside := rfl
theorem noWrap_eq : NativeRustcX64.NoWrap = NativeRustcVm.NoWrap := rfl
theorem apart_eq : NativeRustcX64.Apart = NativeRustcVm.Apart := rfl

variable {d d' : DataMem} {a : BitVec 64} {n : Nat} {bs : List UInt8}

theorem mapped_iff : NativeRustcX64.Mapped d a n ↔ NativeRustcVm.Mapped d a n := Iff.rfl
theorem bytesAt_iff : NativeRustcX64.BytesAt d a bs ↔ NativeRustcVm.BytesAt d a bs := Iff.rfl
theorem inRange_iff {p : BitVec 64} :
    NativeRustcX64.InRange a n p ↔ NativeRustcVm.InRange a n p := Iff.rfl
theorem sameOutside_iff {R : BitVec 64 → Prop} :
    NativeRustcX64.SameOutside d d' R ↔ NativeRustcVm.SameOutside d d' R := Iff.rfl
theorem noWrap_iff : NativeRustcX64.NoWrap a n ↔ NativeRustcVm.NoWrap a n := Iff.rfl
theorem apart_iff {a' : BitVec 64} {n' : Nat} :
    NativeRustcX64.Apart a n a' n' ↔ NativeRustcVm.Apart a n a' n' := Iff.rfl

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
    (hs : Saved m m') : NativeRustcVm.Mapped m'.dmem a n := fun i hi ↦ hs.2 _ (h i hi)

/-- The `n` bytes below RSP as a number. -/
theorem stackBelow_toNat {m : MachineData} (h : n ≤ (rspOf m).toNat) :
    (stackBelow m n).toNat = (rspOf m).toNat - n :=
  NativeRustcVm.toNat_sub_ofNat h

/-- The `n` bytes below RSP and the return address at RSP do not wrap around. -/
theorem noWrap_stackBelow {m : MachineData} (h : StackOk m n) :
    NativeRustcVm.NoWrap (stackBelow m n) (n + 8) := by
  unfold NativeRustcVm.NoWrap
  rw [stackBelow_toNat h.1]
  have := h.1
  have := h.2.1
  omega

/-- The `n` bytes below RSP and the return address at RSP are data memory. -/
theorem mapped_stackBelow {m : MachineData} (h : StackOk m n) :
    NativeRustcVm.Mapped m.dmem (stackBelow m n) (n + 8) := h.2.2

/-- The `bool` a function returns: AL. -/
@[expose] def boolRet (m : MachineData) : Nat := (reg m .rax).toNat % 256

/-- Argument word `i` on the stack, above the return address (the seventh argument word and on). -/
@[expose] def stackArg (m : MachineData) (i : Nat) : BitVec 64 :=
  (NativeRustcVm.wordOf m.dmem (rspOf m + BitVec.ofNat 64 (8 + 8 * i))).toBitVec

/-- The `k` argument words on the stack are data memory, and the return address and they end below
`2^64` (so the frame, the return address and the arguments are one range that does not wrap). -/
@[expose] def ArgsOk (m : MachineData) (k : Nat) : Prop :=
  Mapped m.dmem (rspOf m + 8#64) (8 * k) ∧ (rspOf m).toNat + 8 + 8 * k ≤ 2 ^ 64

end

end NativeRustcVmX64
