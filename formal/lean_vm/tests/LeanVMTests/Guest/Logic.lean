import LeanVM.Guest.Logic

/-!
# The program logic on a hand-built program

`tiny` lays out three functions the way the compiler does, in `2^5` slots:

```text
main   0  SET fp[3] = 1                     seven  7  SET fp[2] = 7
       1  SET fp[4] = g^7                          8  SET fp[3] = 1
       2  DEREF *(fp[2]·g^1) = fp   [Fp]           9  JUMP fp[3]: fp[0], fp[1]
       3  DEREF *(fp[2]·g^0) = g²pc [Pc]   loop  10  JUMP fp[2]: fp[0], fp[1]
       4  JUMP fp[3]: fp[4], fp[2]                11  DEREF *(fp[3]·g^0) = fp[0]
       5  SET fp[5] = g^31                        12  DEREF *(fp[3]·g^1) = fp[1]
       6  JUMP fp[3]: fp[5], fp[3]                13  SET fp[4] = g^10
                                                  14  SET fp[5] = 1
                                                  15  JUMP fp[5]: fp[4], fp[3]
```

`main` calls `seven` at the frame `fp[2]`, which sets its `fp[2]` to `7` and returns; `loop`
returns when `fp[2] ≠ 0` and otherwise tail calls itself at the frame `fp[3]`. Soundness:
`seven`'s contract, `main` through the call, and `loop`'s contract by strong induction. Completeness:
on a memory holding the cells an honest run writes, `main` reaches the final registers.
-/

namespace LeanVMTests.Guest.Logic

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest

def mainFn : CompiledFunction :=
  ⟨"main", 0, 7, [[.set 3 1 0, .set 4 0x80 0, .deref 2 1 0 .fp, .deref 2 0 0 .pc,
    .jump 3 4 2, .set 5 0x80000000 0, .jump 3 5 3]]⟩

def sevenFn : CompiledFunction := ⟨"seven", 7, 3, [[.set 2 7 0, .set 3 1 0, .jump 3 0 1]]⟩

def loopFn : CompiledFunction :=
  ⟨"loop", 10, 6, [[.jump 2 0 1, .deref 3 0 0 .cell, .deref 3 1 1 .cell, .set 4 0x400 0,
    .set 5 1 0, .jump 5 4 3]]⟩

def fns : List CompiledFunction := [mainFn, sevenFn, loopFn]

def tiny : LeanIsaProgram := assemble fns 5 (by decide)

theorem fns_consecutive : consecutive 0 fns 16 = true := by decide

theorem tiny_fetch {f : CompiledFunction} (hf : f ∈ fns) (pc : ℕ) (ins : OffsetInstruction) (hlo :
    f.entryPc ≤ pc)
    (hhi : pc - f.entryPc < f.instructionCount) (hins : f.instructionAt (pc - f.entryPc) = ins) :
    tiny.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction :=
  assemble_fetch_of fns_consecutive (by decide) hf hhi (by omega) hins

theorem main_mem : mainFn ∈ fns := by simp [fns]
theorem seven_mem : sevenFn ∈ fns := by simp [fns]
theorem loop_mem : loopFn ∈ fns := by simp [fns]

/-- `fetch% f pc ins`: instruction `pc` of `tiny`, in function `f`, is `ins`. -/
macro "fetch% " mem:term:max pc:term:max ins:term:max : term =>
  `(tiny_fetch $mem $pc $ins (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem tiny_pc {pc : ℕ} (h : pc < 31) : pc < 2 ^ tiny.logSize - 1 := h

/-! ## Constants -/

theorem limb_imm_one : (OffsetInstruction.immediateWord 1 0).limb 0 = addressOfIndex 0 :=
    by decide +kernel
theorem imm_one_ne_zero : OffsetInstruction.immediateWord 1 0 ≠ 0 := by decide +kernel
theorem limb_imm_seven : (OffsetInstruction.immediateWord 0x80 0).limb 0 = addressOfIndex 7 :=
    by decide +kernel
theorem limb_imm_ten : (OffsetInstruction.immediateWord 0x400 0).limb 0 = addressOfIndex 10 :=
    by decide +kernel
theorem limb_imm_final : (OffsetInstruction.immediateWord 0x80000000 0).limb 0 = tiny.pcFinal :=
    by decide +kernel
theorem isInK_imm (k : ℕ) : IsInK (OffsetInstruction.immediateWord k 0) := by
  have : K.ofBits 0 = 0 := by decide
  simp [IsInK, OffsetInstruction.immediateWord, this]

section

variable {κ : ℕ} {L : MemoryImage κ}

/-! ## Soundness -/

/-- `seven` returns with `fp[2] = 7`. -/
theorem seven_spec :
    FunSpec tiny L 7 (fun _ ↦ True) (fun fp ↦ L.read (fp * addressOfIndex 2) = some
        (OffsetInstruction.immediateWord 7 0)) := by
  intro fp k _ h
  obtain ⟨k, rfl, h7, h⟩ := h.fallThrough (fetch% seven_mem 7 (.set 2 7 0))
      (tiny_pc (by decide)) rfl
  obtain ⟨k, rfl, h3, h⟩ := h.fallThrough (fetch% seven_mem 8 (.set 3 1 0))
      (tiny_pc (by decide)) rfl
  obtain ⟨k, rfl, r, hr, h⟩ := h.ret (fetch% seven_mem 9 (.jump 3 0 1))
      (tiny_pc (by decide)) h3 imm_one_ne_zero
  exact ⟨k, by omega, r, hr, h7, h⟩

/-- `main` calls `seven` at the frame `fp[2]`, whose `fp[2]` is then `7`. -/
theorem main_sound {k : ℕ} (h : Safe tiny L k ⟨addressOfIndex 0, 1⟩) :
    ∃ p, L.read (1 * addressOfIndex 2) = some p ∧ L.read (p.limb 0 * addressOfIndex 2) = some
        (OffsetInstruction.immediateWord 7 0) := by
  obtain ⟨k, rfl, h3, h⟩ := h.fallThrough (fetch% main_mem 0 (.set 3 1 0))
      (tiny_pc (by decide)) rfl
  obtain ⟨k, rfl, h4, h⟩ := h.fallThrough (fetch% main_mem 1 (.set 4 0x80 0))
      (tiny_pc (by decide)) rfl
  obtain ⟨k, rfl, ⟨p, _, hp, -, -, hfp⟩, h⟩ :=
    h.fallThrough (fetch% main_mem 2 (.deref 2 1 0 .fp)) (tiny_pc (by decide)) rfl
  obtain ⟨k, rfl, ⟨p', _, hp', -, -, hpc⟩, h⟩ :=
    h.fallThrough (fetch% main_mem 3 (.deref 2 0 0 .pc)) (tiny_pc (by decide)) rfl
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
  obtain ⟨k, r, rfl, ⟨c, d, f, hc, hd, hf, -, -, -, rfl⟩, h⟩ :=
    h.jump (fetch% main_mem 4 (.jump 3 4 2)) (tiny_pc (by decide))
  obtain rfl : c = _ := Option.some.inj (hc.symm.trans h3)
  obtain rfl : d = _ := Option.some.inj (hd.symm.trans h4)
  obtain rfl : p = f := Option.some.inj (hp.symm.trans hf)
  rw [ite_eq_right imm_one_ne_zero, limb_imm_seven] at h
  rw [derefSource_pc] at hpc
  have hret := retRegs_of_ofK hpc hfp
  obtain ⟨_, _, h7, -⟩ := seven_spec.call trivial hret h
  exact ⟨p, hp, h7⟩

/-- A dispatch-shaped jump whose target comes from a precondition, not from the code before. -/
example {fp p : K} {k : ℕ} (h3 : L.read (fp * addressOfIndex 3) = some
    (OffsetInstruction.immediateWord 1 0))
    (h4 : L.read (fp * addressOfIndex 4) = some (ofK (addressOfIndex 7))) (h2 : L.read (fp *
        addressOfIndex 2) = some (ofK p))
    (h : Safe tiny L k ⟨addressOfIndex 4, fp⟩) : ∃ k', k = k' + 1 ∧ Safe tiny L k' ⟨addressOfIndex
        7, p⟩ :=
  h.jumpTo (fetch% main_mem 4 (.jump 3 4 2)) (tiny_pc (by decide)) h3 imm_one_ne_zero h4 h2

/-- `loop` returns from every frame, by strong induction through its tail call. -/
theorem loop_spec : FunSpec tiny L 10 (fun _ ↦ True) (fun _ ↦ True) := by
  refine funSpec_induction (ι := Unit) (entry := fun _ ↦ 10) (P := fun _ _ ↦ True)
    (Q := fun _ _ ↦ True) (fun n ih _ fp k hk _ h ↦ ?_) ()
  obtain ⟨k, r, rfl, ⟨c, d, f, hc, hd, hf, -, -, -, rfl⟩, h⟩ :=
    h.jump (fetch% loop_mem 10 (.jump 2 0 1)) (tiny_pc (by decide))
  by_cases hc0 : c = 0
  · rw [ite_eq_left hc0] at h
    obtain ⟨k, rfl, ⟨q, v0, hq, -, h0, hq0⟩, h⟩ :=
      h.fallThrough (fetch% loop_mem 11 (.deref 3 0 0 .cell)) (tiny_pc (by decide)) rfl
    obtain ⟨k, rfl, ⟨q', v1, hq', -, h1, hq1⟩, h⟩ :=
      h.fallThrough (fetch% loop_mem 12 (.deref 3 1 1 .cell)) (tiny_pc (by decide)) rfl
    obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
    obtain ⟨k, rfl, h4, h⟩ := h.fallThrough (fetch% loop_mem 13 (.set 4 0x400 0))
        (tiny_pc (by decide)) rfl
    obtain ⟨k, rfl, h5, h⟩ := h.fallThrough (fetch% loop_mem 14 (.set 5 1 0))
        (tiny_pc (by decide)) rfl
    obtain ⟨k, r, rfl, ⟨c, d, f, hc, hd, hf, -, -, -, rfl⟩, h⟩ :=
      h.jump (fetch% loop_mem 15 (.jump 5 4 3)) (tiny_pc (by decide))
    obtain rfl : c = _ := Option.some.inj (hc.symm.trans h5)
    obtain rfl : d = _ := Option.some.inj (hd.symm.trans h4)
    obtain rfl : q = f := Option.some.inj (hq.symm.trans hf)
    rw [ite_eq_right imm_one_ne_zero, limb_imm_ten] at h
    have hret : retRegs L (q.limb 0) = retRegs L fp := by
      simp only [retRegs, hq0, hq1, h0, h1, derefSource]
    obtain ⟨k', hk', r, hr, -, hs⟩ := (ih ()).tail (by omega) trivial hret h
    exact ⟨k', by omega, r, hr, trivial, hs⟩
  · rw [ite_eq_right hc0] at h
    exact ⟨k, by omega, _, retRegs_eq_some_iff.mpr ⟨d, f, hd, hf, rfl⟩, trivial, h⟩

/-! ## Completeness -/

/-- On a memory holding what an honest run writes (`main`'s frame `1`, `seven`'s frame `p`),
`main` reaches the final registers. -/
theorem main_complete {p : K} {w : E} (h0 : L.read (1 * addressOfIndex 0) = some w)
    (h2 : L.read (1 * addressOfIndex 2) = some (ofK p)) (h3 : L.read (1 * addressOfIndex 3) = some
        (OffsetInstruction.immediateWord 1 0))
    (h4 : L.read (1 * addressOfIndex 4) = some (OffsetInstruction.immediateWord 0x80 0))
    (h5 : L.read (1 * addressOfIndex 5) = some (OffsetInstruction.immediateWord 0x80000000 0))
    (hp0 : L.read (p * addressOfIndex 0) = some (ofK (addressOfIndex 5))) (hp1 : L.read (p *
        addressOfIndex 1) = some (ofK 1))
    (hp2 : L.read (p * addressOfIndex 2) = some (OffsetInstruction.immediateWord 7 0))
    (hp3 : L.read (p * addressOfIndex 3) = some (OffsetInstruction.immediateWord 1 0)) :
    Reach tiny L ⟨addressOfIndex 0, 1⟩ (Registers.final tiny) := by
  have hK : ∀ a : K, IsInK (ofK a) := fun a ↦ (isInK_iff _).mpr ⟨a, rfl⟩
  have hseven : Returns tiny L 7 p := by
    refine ⟨⟨addressOfIndex 5, 1⟩, retRegs_of_ofK hp0 hp1, ?_⟩
    refine (reach_fallThrough (fetch% seven_mem 7 (.set 2 7 0))
        (tiny_pc (by decide)) rfl hp2).trans ?_
    refine (reach_fallThrough (fetch% seven_mem 8 (.set 3 1 0))
        (tiny_pc (by decide)) rfl hp3).trans ?_
    exact reach_ret (fetch% seven_mem 9 (.jump 3 0 1))
        (tiny_pc (by decide)) hp3 (isInK_imm 1) imm_one_ne_zero hp0
      (hK _) hp1 (hK _) (retRegs_of_ofK hp0 hp1)
  refine (reach_fallThrough (fetch% main_mem 0 (.set 3 1 0))
      (tiny_pc (by decide)) rfl h3).trans ?_
  refine (reach_fallThrough (fetch% main_mem 1 (.set 4 0x80 0))
      (tiny_pc (by decide)) rfl h4).trans ?_
  refine (reach_fallThrough (fetch% main_mem 2 (.deref 2 1 0 .fp)) (tiny_pc (by decide)) rfl
    ⟨ofK p, w, h2, hK p, h0, by simpa [derefSource] using hp1⟩).trans ?_
  refine (reach_fallThrough (fetch% main_mem 3 (.deref 2 0 0 .pc)) (tiny_pc (by decide)) rfl
    ⟨ofK p, w, h2, hK p, h0, by simpa [derefSource_pc] using hp0⟩).trans ?_
  refine (reach_jump (fetch% main_mem 4 (.jump 3 4 2)) (tiny_pc (by decide))
    ⟨_, _, _, h3, h4, h2, isInK_imm 1, isInK_imm _, hK p, rfl⟩).trans ?_
  have hpl : (ofK p).limb 0 = p := by simp
  rw [ite_eq_right imm_one_ne_zero, limb_imm_seven, hpl]
  refine (hseven.reach (retRegs_of_ofK hp0 hp1)).trans ?_
  refine (reach_fallThrough (fetch% main_mem 5 (.set 5 0x80000000 0))
      (tiny_pc (by decide)) rfl h5).trans ?_
  refine (reach_jump (fetch% main_mem 6 (.jump 3 5 3)) (tiny_pc (by decide))
    ⟨_, _, _, h3, h5, h3, isInK_imm 1, isInK_imm _, isInK_imm 1, rfl⟩).trans ?_
  rw [ite_eq_right imm_one_ne_zero, limb_imm_final, limb_imm_one, addressOfIndex, pow_zero]
  exact Reach.refl _

end

end LeanVMTests.Guest.Logic
