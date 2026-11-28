module

public import NativeRustcArm.Code.Common.KeccakF.Names

public import NativeRustcArm.KeccakF.Prologue
public import NativeRustcArm.KeccakF.Round
public import NativeRustcArm.KeccakF.Epilogue

/-!
# `keccak_f` meets its contract

`keccakF_spec`: rustc's AArch64 `keccak_f`, placed anywhere in the program, from its entry in a
state satisfying `KeccakFPre` inevitably returns to its caller with the 200 bytes at X0 replaced by
`Keccak.keccakF` of them (Keccak-f[1600] of their lanes), no byte changed outside them and its
192-byte frame, the callee-saved registers and SP restored and every mapped byte still mapped
(`KeccakFPost`). The prologue (`prologue_step`) reaches the loop invariant before the first round,
each turn of the loop (`round_step`) one round further, by induction on the rounds left
(`Sym.loop`), and after the 24th the epilogue (`epilogue_step`) returns.
-/

namespace NativeRustcArm

open KeccakF NativeRustcArm

public section

variable [Host]

/-- **`keccak_f` meets its contract.** -/
theorem keccakF_spec {k : Nat} (hp : Placed Common.KeccakF.code k) :
    Spec (label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost := by
  intro m0 hpre
  rw [hp.label NativeRustcArm.Common.KeccakF.entry_at, NativeRustcArm.Common.KeccakF.entryOffset, Nat.add_zero]
  refine Eventually.bind (prologue_step hp hpre) fun st₁ ⟨hA₁, hpc₁⟩ => ?_
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun st => At m0 24 st.data ∧ st.pc = Host.addrOf (k + NativeRustcArm.Common.KeccakF.b2Offset))
    (fun n st => ∃ i, n = 24 - i ∧ i < 24 ∧ st.pc = Host.addrOf (k + NativeRustcArm.Common.KeccakF.b1Offset) ∧ At m0 i st.data)
    (fun n st ⟨i, hn, hi, hpc, hA⟩ => by
      obtain ⟨m, pc⟩ := st
      simp only at hpc
      subst hpc
      refine Eventually.mono (round_step hp hpre hi hA) fun st' ⟨hA', hpc'⟩ => ?_
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
  exact epilogue_step hp hpre hA₂

end

end NativeRustcArm
