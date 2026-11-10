import Rv64Verifier.Proofs.Runtime.Inv

/-!
# Byte loads and stores at any address

The symbolic executor reads and writes a byte at `b + k` only for an 8-aligned base `b`, so that it
knows the byte's offset in its doubleword; `memset`, `memcpy` and `memcmp` walk bytes from any
address. `step_sb` and `step_lbu` are the machine's step for `SB` and `LBU` at a known pc, in
terms of `byteAt`: the byte at the address, and nothing else, changes (`SB`), or lands in the
register (`LBU`).
-/

namespace Rv64Verifier.Runtime
open RiscvZkvm.Rv64

/-- The base instruction at `pc`, if any: decidable, so a fetch is one `decide +kernel`
(`fetch_of`). -/
def fetchBase (code : Code) (pc : Word) : Option Instr :=
  match code.fetch pc with
  | some (.base i) => some i
  | _ => none

theorem fetch_of {code : Code} {pc : Word} {i : Instr} (h : fetchBase code pc = some i) :
    code.fetch pc = some (.base i) := by
  unfold fetchBase at h
  split at h
  · rename_i heq; cases h; exact heq
  · cases h

/-- A byte of a mapped range is a valid byte access. -/
theorem Mapped.valid {a : Word} {n i : Nat} (h : Mapped a n) (hi : i < n) :
    isValidMemAddr (a + BitVec.ofNat 64 i) = true := by
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp only [Mapped] at h; omega
  simp only [isValidMemAddr_eq, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, this, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [Mapped] at h
  omega

theorem Mapped.valid8 {a x : Word} {n : Nat} (h : Mapped a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : Sym.validAccess 8 x = true := by
  rw [Sym.validAccess_eight]
  simp only [Mapped] at h
  omega

theorem ne_of_mem_of_not_mem {l : List Reg} {r x : Reg} (hr : r ∈ l) (hx : x ∉ l) : r ≠ x :=
  fun e ↦ hx (e ▸ hr)

/-- One step of a classified instruction, observed through registers, memory and pc. -/
theorem step_micro {code : Code} {s t : MachineState} {i : Instruction} {m : Sym.Micro}
    (hf : code.fetch s.pc = some i) (hc : Sym.classify i = some m) (he : m.exec s = some t) :
    ∃ u, Steps code 1 s u ∧ u.pc = t.pc ∧ (∀ r, u.getReg r = t.getReg r) ∧
      ∀ a, u.getMem a = t.getMem a := by
  refine ⟨{ t with code := Sym.codeAfter code s i }, Steps.one ?_, rfl,
    fun r ↦ Sym.getReg_withCode t _ r, fun _ ↦ rfl⟩
  rw [Sym.classify_sound hf hc, he]
  rfl

theorem eq_iff_alignDown {a b : Word} :
    a = b ↔ a &&& ~~~7#64 = b &&& ~~~7#64 ∧ a.toNat % 8 = b.toNat % 8 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have := congrArg BitVec.toNat h1
    rw [toNat_alignDown, toNat_alignDown] at this
    apply BitVec.eq_of_toNat_eq
    omega

/-- The byte at `a` after storing `v` at `p`. -/
theorem byteAt_setByte (s : MachineState) (p a : Word) (v : BitVec 8) :
    byteAt (s.setByte p v) a = if a = p then v else byteAt s a := by
  have hp := Nat.mod_lt p.toNat (by decide : 0 < 8)
  have ha := Nat.mod_lt a.toNat (by decide : 0 < 8)
  simp only [byteAt_eq, MachineState.setByte, alignToDword, byteOffset, toNat_and7]
  by_cases hd : a &&& ~~~7#64 = p &&& ~~~7#64
  · rw [hd, MachineState.getMem_setMem_eq, extractByte_replaceByte _ _ hp ha]
    by_cases ho : p.toNat % 8 = a.toNat % 8
    · have h' : a = p := eq_iff_alignDown.mpr ⟨hd, ho.symm⟩
      simp only [ho, h', ↓reduceIte]
    · have h' : a ≠ p := fun h ↦ ho (eq_iff_alignDown.mp h).2.symm
      simp only [ho, h', ↓reduceIte]
  · have h' : a ≠ p := fun h ↦ hd (eq_iff_alignDown.mp h).1
    rw [MachineState.getMem_setMem_ne hd]
    simp only [h', ↓reduceIte]

/-- `SB rs2, off(rs1)`: the byte at the address becomes `rs2`'s low byte. -/
theorem step_sb {code : Code} {s : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hf : code.fetch s.pc = some (.base (.SB rs1 rs2 off)))
    (hv : isValidMemAddr (s.getReg rs1 + signExtend12 off) = true) :
    ∃ t, Steps code 1 s t ∧ t.pc = s.pc + 4 ∧ (∀ r, t.getReg r = s.getReg r) ∧
      (∀ a, byteAt t a = if a = s.getReg rs1 + signExtend12 off then (s.getReg rs2).truncate 8
        else byteAt s a) ∧
      ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = s.getMem a := by
  obtain ⟨u, hu, hpc, hr, hm⟩ := step_micro (m := .store .b rs1 rs2 (signExtend12 off)) hf rfl
    (by simp only [Sym.Micro.exec, Sym.StoreKind.width, Sym.validAccess, isValidByteAccess, hv,
      ↓reduceIte]; rfl)
  refine ⟨u, hu, hpc, fun r ↦ hr r, fun a ↦ ?_, fun a ha ↦ ?_⟩
  · have h' : byteAt u a = byteAt (s.setByte (s.getReg rs1 + signExtend12 off)
        ((s.getReg rs2).truncate 8)) a := by simp only [byteAt_eq, hm]; rfl
    rw [h', byteAt_setByte]
  · rw [hm]
    show (s.setByte _ _).getMem a = s.getMem a
    simp only [MachineState.setByte]
    refine MachineState.getMem_setMem_ne fun h ↦ ha ?_
    rw [h, alignToDword, toNat_alignDown]
    omega

/-- `LBU rd, off(rs1)`: `rd` gets the byte at the address. -/
theorem step_lbu {code : Code} {s : MachineState} {rd rs1 : Reg} {off : BitVec 12}
    (hf : code.fetch s.pc = some (.base (.LBU rd rs1 off)))
    (hv : isValidMemAddr (s.getReg rs1 + signExtend12 off) = true) :
    ∃ t, Steps code 1 s t ∧ t.pc = s.pc + 4 ∧
      (∀ r, t.getReg r = if r = rd ∧ rd ≠ .x0 then
        (byteAt s (s.getReg rs1 + signExtend12 off)).zeroExtend 64 else s.getReg r) ∧
      ∀ a, t.getMem a = s.getMem a := by
  obtain ⟨u, hu, hpc, hr, hm⟩ := step_micro (m := .load .bu rd rs1 (signExtend12 off)) hf rfl
    (by simp only [Sym.Micro.exec, Sym.LoadKind.width, Sym.validAccess, isValidByteAccess, hv,
      ↓reduceIte]; rfl)
  refine ⟨u, hu, hpc, fun r ↦ ?_, fun a ↦ by rw [hm]; simp⟩
  rw [hr]
  show (s.setReg rd _).getReg r = _
  by_cases h : r = rd ∧ rd ≠ .x0
  · obtain ⟨rfl, h0⟩ := h
    rw [MachineState.getReg_setReg_eq h0]
    simp only [true_and, ne_eq, h0, not_false_eq_true, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    by_cases h0 : rd = .x0
    · subst h0; rfl
    · exact MachineState.getReg_setReg_ne _ _ _ _ fun h' ↦ h ⟨h'.symm, h0⟩

end Rv64Verifier.Runtime
