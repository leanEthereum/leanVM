module

public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names

public import NativeRustcArm.Hasher.UpdateB1
public import NativeRustcArm.Hasher.UpdateB7

/-!
# `Hasher::update`'s loop

A turn from the loop head (`turn_spec`): copy into the buffer, count, absorb a full buffer, then
back to the loop head with more input absorbed or out of the loop with all of it. The loop
(`loop_spec`): from the loop head, out of the loop with the whole input absorbed.
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustc NativeRustc.Keccak NativeRustcArm.Sym NativeRustcArm.Common.Update NativeRustcArm

public section

variable [ElfHost] {sec k : Nat}

/-- **A turn of the loop.** -/
theorem turn_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : ElfSpec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m1 m : MachineData} (hpre : UpdatePre m0)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {c : Nat}
    (hinv : Inv m0 m1 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b8Offset) ∧ Inv m0 m1 (nOf m0) st.data) ∨
        ∃ n' < nOf m0 - c, st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset) ∧
          ∃ c', nOf m0 - c' = n' ∧ Inv m0 m1 c' st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset)⟩ := by
  -- After a turn, at `.LUpdate_1`.
  have fin : ∀ (t : Nat) (st : MachineState), st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b1Offset) →
      Mid m0 m1 c t st.data →
      Eventually (elfStep1 ElfHost.exe)
        (fun st => (st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b8Offset) ∧ Inv m0 m1 (nOf m0) st.data) ∨
          ∃ n' < nOf m0 - c, st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset) ∧
            ∃ c', nOf m0 - c' = n' ∧ Inv m0 m1 c' st.data) st := by
    intro t st hpc hmid
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    refine NativeRustcArm.Eventually.mono_elf (b1_spec hp hmid) fun st h => ?_
    rcases h with ⟨hpc, hinv', ht⟩ | h
    · exact Or.inr ⟨nOf m0 - (c + t), by have := hinv'.le; omega, hpc, c + t, rfl, hinv'⟩
    · exact Or.inl h
  refine NativeRustcArm.Eventually.bind_elf (copy_spec hp hmemcpy hpre h01 hinv) fun st ⟨hpc, hcp⟩ => ?_
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  refine NativeRustcArm.Eventually.bind_elf (b5_spec hp hpre hcp) fun st h => ?_
  rcases h with ⟨hpc, hmid⟩ | ⟨hpc, hfu⟩
  · exact fin _ st hpc hmid
  · obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    refine NativeRustcArm.Eventually.bind_elf (b6_spec hp hkf hpre h01 hfu) fun st ⟨hpc, hab⟩ => ?_
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    subst hpc
    exact NativeRustcArm.Eventually.bind_elf (b7_spec hp hpre hab) fun st ⟨hpc, hmid⟩ => fin _ st hpc hmid

/-- **The loop**: out of it with the whole input absorbed. -/
theorem loop_spec (hp : PlacedIn code sec k)
    (hmemcpy : ElfSpec (Labels.label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hkf : ElfSpec (Labels.label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost)
    {m0 m1 m : MachineData} (hpre : UpdatePre m0)
    (h01 : SameOutside m0.dmem m1.dmem (InRange (spAt m0 - 64#64) 64)) {c : Nat}
    (hinv : Inv m0 m1 c m) :
    Eventually (elfStep1 ElfHost.exe)
      (fun st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b8Offset) ∧ Inv m0 m1 (nOf m0) st.data)
      ⟨m, ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset)⟩ := by
  refine Sym.loop (fun n st => st.pc = ElfHost.addrOf sec (k + NativeRustcArm.Common.Update.b2Offset) ∧
      ∃ c', nOf m0 - c' = n ∧ Inv m0 m1 c' st.data) (fun n st ⟨hpc, c', hn, hi⟩ => ?_)
    ⟨rfl, c, rfl, hinv⟩
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc hn
  exact turn_spec hp hmemcpy hkf hpre h01 hi

end

end NativeRustcArm.Hasher.Update
