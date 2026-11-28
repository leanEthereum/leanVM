module

public import NativeRustcVmX64.Keccak.KeccakF.Prologue
public import NativeRustcVmX64.Keccak.KeccakF.Round
public import NativeRustcVmX64.Keccak.KeccakF.Epilogue
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names

/-!
# `keccak_f` meets its contract (x86-64)

`keccakF_spec`: the leanVM crate's x86-64 `keccak_f`, placed anywhere in the program, given
`memcpy`'s contract, from its entry in a state satisfying `KeccakFPre` inevitably returns to its
caller, with RSP 8 above, with the 25 words at RDI replaced by `keccakF1600` of them, no byte
changed outside them and its 480-byte stack, the callee-saved registers restored and every mapped
byte still mapped (`KeccakFPost`). The prologue (`prologue_step`) copies the round constants to the
frame and reaches the loop invariant before the first round, each turn of the loop (`round_step`)
one round further, by induction on the rounds left (`Sym.loop`), and after the 24th the epilogue
(`epilogue_step`) returns.
-/

namespace NativeRustcVmX64

open NativeRustcX64

public section

variable [Host]

/-- **`keccak_f` meets its contract.** -/
theorem keccakF_spec {k : Nat} (hp : Placed Vm.KeccakF.code k)
    (hmemcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) :
    Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost := by
  intro m0 hpre
  rw [show label NativeRustcVmX64.Vm.KeccakF.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b0Offset) from hp.label NativeRustcVmX64.Vm.KeccakF.entry_at]
  refine Eventually.bind (KeccakF.prologue_step hp hmemcpy hpre) fun st₁ ⟨hA₁, hpc₁⟩ => ?_
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun st => KeccakF.At m0 24 st.data ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b3Offset))
    (fun n st => ∃ i, n = 24 - i ∧ i < 24 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.KeccakF.b2Offset) ∧ KeccakF.At m0 i st.data)
    (fun n st ⟨i, hn, hi, hpc, hA⟩ => by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      refine Eventually.mono (KeccakF.round_step hp hpre.1 hi hA) fun st' ⟨hA', hpc'⟩ => ?_
      by_cases h : i + 1 = 24
      · simp only [h, ↓reduceIte] at hpc'
        exact .inl ⟨h ▸ hA', hpc'⟩
      · simp only [h, ↓reduceIte] at hpc'
        exact .inr ⟨24 - (i + 1), by omega, i + 1, rfl, by omega, hpc', hA'⟩)
    (n := 24) ⟨0, rfl, by decide, hpc₁, hA₁⟩
  refine Eventually.bind hloop fun st₂ ⟨hA₂, hpc₂⟩ => ?_
  obtain ⟨m, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  exact KeccakF.epilogue_step hp hpre hA₂

end

end NativeRustcVmX64
