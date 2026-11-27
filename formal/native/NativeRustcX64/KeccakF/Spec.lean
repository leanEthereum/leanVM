module

public import NativeRustcX64.Code.Common.KeccakF.Names

public import NativeRustcX64.KeccakF.Prologue
public import NativeRustcX64.KeccakF.Round
public import NativeRustcX64.KeccakF.Epilogue

/-!
# `keccak_f` meets its contract (x86-64)

`keccakF_spec`: rustc's x86-64 `keccak_f`, placed anywhere in the program, from its entry in a
state satisfying `KeccakFPre` inevitably returns to the address at its RSP, with RSP 8 above, the
200 bytes at RDI replaced by `Keccak.keccakF` of them (Keccak-f[1600] of their lanes), no byte
changed outside them and the 288 bytes below RSP, the callee-saved registers restored and every
mapped byte still mapped (`KeccakFPost`). The prologue (`prologue_step`) reaches the loop
invariant before the first round, each turn of the loop (`round_step`) two rounds further, by
induction on the pairs of rounds left (`Sym.loop`), and after the 24th the epilogue (`epilogue_step`)
returns.
-/

namespace NativeRustcX64

open KeccakF

public section

/-- **`keccak_f` meets its contract** under `ElfHost`. -/
theorem keccakF_spec_elf [ElfHost] {sec k : Nat} (hp : PlacedIn Common.KeccakF.code sec k) :
    ElfSpec (label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost := by
  intro m0 hpre
  rw [hp.label NativeRustcX64.Common.KeccakF.entry_at, NativeRustcX64.Common.KeccakF.entryOffset, Nat.add_zero]
  refine Eventually.bind_elf (prologue_step hp hpre) fun st₁ ⟨hA₁, hpc₁⟩ => ?_
  have hloop := Sym.loop (tr := elfStep1 ElfHost.exe)
    (Q := fun st => At m0 24 st.data ∧ st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.KeccakF.b2Offset))
    (fun n st => ∃ i, n = 12 - i ∧ i < 12 ∧ st.pc = ElfHost.addrOf sec (k + NativeRustcX64.Common.KeccakF.b1Offset) ∧ At m0 (2 * i) st.data)
    (fun n st ⟨i, hn, hi, hpc, hA⟩ => by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      refine Eventually.mono_elf (round_step hp hpre (by omega) hA) fun st' ⟨hA', hpc'⟩ => ?_
      by_cases h : 2 * i + 2 = 24
      · simp only [h, ↓reduceIte] at hpc'
        exact .inl ⟨h ▸ hA', hpc'⟩
      · simp only [h, ↓reduceIte] at hpc'
        refine .inr ⟨12 - (i + 1), by omega, i + 1, rfl, by omega, hpc', ?_⟩
        simpa only [Nat.mul_add, Nat.mul_one] using hA')
    (n := 12) ⟨0, rfl, by decide, hpc₁, hA₁⟩
  refine Eventually.bind_elf hloop fun st₂ ⟨hA₂, hpc₂⟩ => ?_
  obtain ⟨m, pc⟩ := st₂
  simp only at hpc₂
  subst hpc₂
  exact epilogue_step hp hpre hA₂

/-- **`keccak_f` meets its contract.** -/
theorem keccakF_spec [Host] {k : Nat} (hp : Placed Common.KeccakF.code k) :
    Spec (label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost :=
  ElfSpec.toSpec (entry := fun [Labels] => label NativeRustcX64.Common.KeccakF.entryLabel)
    (P := fun [Labels] => KeccakFPre) (Q := fun [Labels] => KeccakFPost)
    (@keccakF_spec_elf (Host.toElfHost _) 0 k hp.toPlacedIn)

end

end NativeRustcX64
