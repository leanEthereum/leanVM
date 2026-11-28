module

public import NativeRustcVmArm.Keccak.WordsHash.Lane

/-!
# `keccak256_words::<hash_words's closure>`: the last block's words

`tail_run`: from the last block's head after `tailHead` (`TailAt m0 k 0`), the machine inevitably
reaches the padding block (`PadAt`): the lanes the whole blocks' state with the words `base` to
`base + 15` XORed into the first 16 (`pre … 16`), X8 word `base + 16` (zero past the slice). Lane
`j`'s step (`tail{j}`) is `tailL_step` where word `base + j` is in the slice, else `tailZ_step`.
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym
open NativeRustcArm.KeccakF (wordAt_keep)

public section

variable [Host]

omit [Host] in
/-- A label of a block. -/
theorem label_at [Host] {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k)
    {b : List Directive} {j : Nat} (hb : b.IsInfixAt Vm.Keccak256WordsOfHashWords.code j)
    {l : Label} {b' : List Directive} (h : b = .label l :: b') :
    Labels.label l = Host.addrOf (k + j) := by
  subst h
  exact hp.label (List.IsInfixAt.cons hb).1

/-- **At the padding block**: the first 16 lanes XORed, X8 word `base + 16`. -/
@[expose] def PadAt (m0 : MachineData) (k : Nat) (st : MachineState) : Prop :=
  Ctx m0 st.data ∧ Lanes m0 st.data (pre (stA m0) (word m0) (base m0) 16) ∧
    (st.data.regs.getXReg .X8).toBitVec = (word m0 (base m0 + 16)).toBitVec ∧
    st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.b76Offset)

theorem tail0 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 0 28 405 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 1 412 35) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 0 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 0) g (by decide) hin hc hl (.inr ⟨rfl, rfl⟩) (Vm.Keccak256WordsOfHashWords.b3_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL0 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b60_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 0) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b59_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ0 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b4_in_code rfl) rfl

theorem tail1 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 1 412 35 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 2 420 42) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 1 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 1) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b60_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL1 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b5_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 1) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b4_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ1 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b61_in_code rfl) rfl

theorem tail2 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 2 420 42 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 3 428 49) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 2 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 2) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b61_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL2 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b6_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 2) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b5_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ2 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b62_in_code rfl) rfl

theorem tail3 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 3 428 49 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 4 436 56) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 3 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 3) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b62_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL3 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b7_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 3) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ3 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b63_in_code rfl) rfl

theorem tail4 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 4 436 56 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 5 444 63) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 4 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 4) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b63_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL4 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b8_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 4) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b7_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ4 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b64_in_code rfl) rfl

theorem tail5 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 5 444 63 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 6 452 70) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 5 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 5) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b64_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL5 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b9_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 5) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b8_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ5 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b65_in_code rfl) rfl

theorem tail6 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 6 452 70 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 7 460 77) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 6 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 6) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b65_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL6 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b10_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 6) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b9_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ6 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b66_in_code rfl) rfl

theorem tail7 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 7 460 77 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 8 468 84) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 7 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 7) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b66_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL7 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b11_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 7) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b10_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ7 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b67_in_code rfl) rfl

theorem tail8 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 8 468 84 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 9 476 91) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 8 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 8) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b67_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL8 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b12_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 8) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b11_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ8 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b68_in_code rfl) rfl

theorem tail9 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 9 476 91 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 10 484 98) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 9 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 9) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b68_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL9 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b13_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 9) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b12_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ9 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b69_in_code rfl) rfl

theorem tail10 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 10 484 98 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 11 492 105) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 10 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 10) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b69_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL10 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b14_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 10) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b13_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ10 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b70_in_code rfl) rfl

theorem tail11 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 11 492 105 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 12 500 112) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 11 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 11) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b70_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL11 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b15_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 11) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b14_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ11 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b71_in_code rfl) rfl

theorem tail12 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 12 500 112 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 13 508 119) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 12 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 12) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b71_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL12 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b16_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 12) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b15_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ12 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b72_in_code rfl) rfl

theorem tail13 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 13 508 119 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 14 516 126) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 13 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 13) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b72_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL13 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b17_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 13) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b16_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ13 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b73_in_code rfl) rfl

theorem tail14 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 14 516 126 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 15 524 133) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 14 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 14) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b73_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL14 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b18_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 14) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b17_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ14 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b74_in_code rfl) rfl

theorem tail15 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 15 524 133 st) :
    Eventually (step1 Host.exe) (TailAt m0 k 16 532 140) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨d, pc⟩ := st
  simp only at hc hl hx9 hpc
  by_cases hin : base m0 + 15 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailL_step (j := 15) g (by decide) hin hc hl (.inl ⟨rfl, hx9 (by decide)⟩) (Vm.Keccak256WordsOfHashWords.b74_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL15 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := false) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b19_in_code rfl) rfl
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    exact tailZ_step (j := 15) g (by decide) (by omega) hc hl (Vm.Keccak256WordsOfHashWords.b18_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ15 rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ rfl (pos := true) rfl (label_at hp Vm.Keccak256WordsOfHashWords.b75_in_code rfl) rfl

theorem tail16 {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 16 532 140 st) :
    Eventually (step1 Host.exe) (PadAt m0 k) st := by
  obtain ⟨hc, hl, hx9, hpc⟩ := h
  obtain ⟨m, pc⟩ := st
  simp only at hc hl hx9 hpc
  have hstk := g.stk
  by_cases hin : base m0 + 16 < m0.regs.X4.toNat
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    obtain ⟨hat, hreg1, hap1⟩ := slice_region g hc (i0 := base m0 + 16) (c := 1) (by omega)
      (by omega)
    let env := Env.ofMachine m [(frame m0, 288),
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (base m0 + 16)), 8)]
    have hwf : env.WF :=
      Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, hreg1, trivial⟩
        (List.pairwise_pair.mpr hap1)
    have hm : Match env startTailL m := by
      refine match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, rfl,
        fun h => absurd h (by decide), trivial⟩ (by rw [hc.sp]; simp [Sym.eval]) trivial trivial
        trivial ⟨?_, trivial⟩
      show addrX9.eval env = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * (base m0 + 16)) +
        BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      exact addr_word hc (hx9 (by decide))
    refine exec_then (Vm.Keccak256WordsOfHashWords.b75_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailL16 hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
    · exact ctx_step hstk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ fun w hw => by cases hw
    · intro i hi
      exact wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
    · rw [hm'.regs .X8 _ rfl]
      have hw : env.load 1 (8 * 0) 8 = (word m0 (base m0 + 16 + 0)).toBitVec :=
        load_word (r := 1) rfl (by omega) fun t ht => slice_same g hc (by omega)
      exact hw
    · exact hpc
  · simp only [hin, ↓reduceIte] at hpc
    subst hpc
    let env := Env.ofMachine m [(frame m0, 288)]
    have hwf : env.WF :=
      Env.wf_of ⟨⟨frame_mapped hstk hc.kept, frame_noWrap hstk⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm : Match env startMain m :=
      match_ofMachine ⟨rfl, fun _ => frame_aligned hstk, trivial⟩
        (by rw [hc.sp]; simp [Sym.eval]) trivial trivial trivial trivial
    refine exec_then (Vm.Keccak256WordsOfHashWords.b19_in_code.trans hp.1 (List.cons_ne_nil _ _)) tailZ16 hwf hm fun st hm' hpc => .done _ ⟨?_, ?_, ?_, ?_⟩
    · exact ctx_step hstk hc hm' hwf rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩ fun w hw => by cases hw
    · intro i hi
      exact wordAt_keep (r := 0) (sz := 288) hm' rfl (by omega) rfl (hl i hi)
    · rw [hm'.regs .X8 _ rfl, word_ge (by omega)]
      rfl
    · exact hpc.trans (label_at hp Vm.Keccak256WordsOfHashWords.b76_in_code rfl)

/-- **The last block's words.** -/
theorem tail_run {k : Nat} (hp : Placed Vm.Keccak256WordsOfHashWords.code k) {m0 : MachineData} (g : Geo m0)
    {st : MachineState} (h : TailAt m0 k 0 28 405 st) :
    Eventually (step1 Host.exe) (PadAt m0 k) st := by
  refine Eventually.bind (tail0 hp g h) fun st1 h1 => ?_
  refine Eventually.bind (tail1 hp g h1) fun st2 h2 => ?_
  refine Eventually.bind (tail2 hp g h2) fun st3 h3 => ?_
  refine Eventually.bind (tail3 hp g h3) fun st4 h4 => ?_
  refine Eventually.bind (tail4 hp g h4) fun st5 h5 => ?_
  refine Eventually.bind (tail5 hp g h5) fun st6 h6 => ?_
  refine Eventually.bind (tail6 hp g h6) fun st7 h7 => ?_
  refine Eventually.bind (tail7 hp g h7) fun st8 h8 => ?_
  refine Eventually.bind (tail8 hp g h8) fun st9 h9 => ?_
  refine Eventually.bind (tail9 hp g h9) fun st10 h10 => ?_
  refine Eventually.bind (tail10 hp g h10) fun st11 h11 => ?_
  refine Eventually.bind (tail11 hp g h11) fun st12 h12 => ?_
  refine Eventually.bind (tail12 hp g h12) fun st13 h13 => ?_
  refine Eventually.bind (tail13 hp g h13) fun st14 h14 => ?_
  refine Eventually.bind (tail14 hp g h14) fun st15 h15 => ?_
  refine Eventually.bind (tail15 hp g h15) fun st16 h16 => ?_
  exact tail16 hp g h16

end

end NativeRustcVmArm.WordsHash
