module

public import NativeRustcVmArm.Rodata
public import NativeRustcVmArm.Spec.Keccak

/-!
# The round constants from the read-only data

`RodataAt m n` gives `keccak_f`'s `RcAt m n`: the round constants are the item `keccakRC`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeRustcVm.Data

public section

variable [Labels]

theorem rcAddr_eq : rcAddr = rodataAddr .keccakRC := rfl

omit [Labels] in
theorem keccakRC_eq : NativeRustcVm.Data.keccakRC = LeanVM.Parameters.keccakRC := rfl

/-- **The round constants at their label**, from the read-only data. -/
theorem RodataAt.rcAt {m : MachineData} {n : Nat} (h : RodataAt m n) : RcAt m n := by
  have hl : (Item.bytes .keccakRC).length = 192 := by
    rw [Item.bytes, NativeRustcVm.length_wordsBytes, keccakRC_eq]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have := h.bytesAt .keccakRC
    rw [Item.bytes, keccakRC_eq] at this
    exact this
  · have := h.noWrap .keccakRC
    rwa [hl] at this
  · have := h.apart .keccakRC
    rwa [hl] at this

end

end NativeRustcVmArm
