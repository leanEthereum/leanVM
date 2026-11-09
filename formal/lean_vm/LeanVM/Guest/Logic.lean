/-
  LeanVM.Guest.Logic

  A program logic for compiled functions over `run`: one lemma per instruction shape, function
  contracts in continuation form with strong induction on the steps left, and the run-building
  counterparts for completeness.
-/

module

public import LeanVM.Guest.Code
public import LeanVM.Semantics.KeccakCells

/-!
# The program logic

For a program `prog` and one memory `L`, fixed throughout as in a valid execution.

**Soundness.** `Safe prog L k r` says the run from `r` halts after exactly `k` steps. Every lemma
takes a `Safe` state to the next one and gives what the instruction checked: `Safe.fallThrough`
(`Holds`, the relation of a non-`JUMP`), `Safe.jump` and `Safe.ret`. A function's contract
`FunSpec prog L entry P Q` is in continuation form: from `(g^entry, fp)` with `P fp`, a run that
halts first returns, in fewer steps, to the caller's registers stored at `fp[0]` and `fp[1]`
(`retRegs`), with `Q fp`. Contracts are proved together by strong induction on the steps left
(`funSpec_induction`), through `FunSpecLt`, the contract for runs shorter than `n`: a call or a
loop's tail call to the next frame (`FunSpecLt.call`, `FunSpecLt.tail`) happens after at least one
step, so it uses the contracts at a smaller bound. A run of the program starts at `(g^0, 1)`
(`safe_of_validExecution`).

**Completeness.** `Reach prog L s t` says some run goes from `s` to `t`; it is transitive, and
the same instruction shapes extend it (`reach_fallThrough`, `reach_jump`, `reach_ret`). A
function returns from frame `fp` (`Returns`) when it reaches the registers `retRegs L fp`;
`returns_induction` proves that of a family of functions by strong induction on a measure the
caller chooses (a loop's iterations left, a call depth). `validExecution_of_reach` closes a run
from `(g^0, 1)` to the final registers.

A contract's `P` and `Q` are any predicates on the frame over the fixed memory, so a
precondition or a callee's postcondition can carry what a later step needs, such as a selector
cell `L[fp·g^o] = g^j` with `j < n` that bounds a table dispatch; no rule assumes such a fact
comes from a gadget in the same function. `Safe.jumpTo` and `reach_jumpTo` take a jump's target
cells as such facts.

Each step lemma needs the instruction fetched, which `LeanVM.Guest.assemble_fetch` gives for an
assembled program, and `pc < 2^logSize - 1`, which keeps the state away from the halting slot.
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-! ## Definitions -/

section

variable {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ)

/-- The run from `r` halts after exactly `k` steps. -/
def Safe (k : ℕ) (r : Registers K) : Prop := run prog L k r = some (Registers.final prog)

/-- What a non-`JUMP` instruction at `(g^pc, fp)` checks of the memory. -/
def Holds (pc : ℕ) (fp : K) : OffsetInstruction → Prop
  | .xor a b c => ∃ vA vB, L.read (fp * addressOfIndex a) = some vA ∧ L.read (fp * addressOfIndex b) = some vB ∧
      L.read (fp * addressOfIndex c) = some (vA + vB)
  | .mul a b c => ∃ vA vB, L.read (fp * addressOfIndex a) = some vA ∧ L.read (fp * addressOfIndex b) = some vB ∧
      L.read (fp * addressOfIndex c) = some (vA * vB)
  | .set o k0 k1 k2 => L.read (fp * addressOfIndex o) = some (OffsetInstruction.immediateWord k0 k1 k2)
  | .deref o1 o2 o3 mode => ∃ p v3, L.read (fp * addressOfIndex o1) = some p ∧ IsInK p ∧
      L.read (fp * addressOfIndex o3) = some v3 ∧
      L.read (p.limb 0 * addressOfIndex o2) = some (derefSource mode ⟨addressOfIndex pc, fp⟩ v3)
  | .jump .. => False
  | .keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells => ∃ input output : Fin 13 → E,
      (∀ c : Fin 13, L.read (fp * addressOfIndex (keccakInOff m0 m1 m2 m3 tail b8 cap c.val)) =
        some (input c)) ∧
      (∀ c : Fin 13, c.val < outCells.cellCount →
        L.read (fp * addressOfIndex (out + c.val)) = some (output c)) ∧
      KeccakCellsRelation input inOdd output outOdd outCells

/-- What a `JUMP fp[oc], fp[od], fp[of]` at `(g^pc, fp)` checks, and where it goes. -/
def JumpsTo (pc : ℕ) (fp : K) (oc od of : ℕ) (r : Registers K) : Prop :=
  ∃ c d f, L.read (fp * addressOfIndex oc) = some c ∧ L.read (fp * addressOfIndex od) = some d ∧
    L.read (fp * addressOfIndex of) = some f ∧ IsInK c ∧ IsInK d ∧ IsInK f ∧
    r = if c = 0 then ⟨addressOfIndex (pc + 1), fp⟩ else ⟨d.limb 0, f.limb 0⟩

/-- The caller's registers a function at frame `fp` returns to: `(fp[0], fp[1])`. -/
noncomputable def retRegs (fp : K) : Option (Registers K) :=
  (L.read (fp * addressOfIndex 0)).bind fun d ↦ (L.read (fp * addressOfIndex 1)).map fun f ↦ ⟨d.limb
      0, f.limb 0⟩

/-- **A function's contract, for runs shorter than `n`**: from `(g^entry, fp)` with `P fp`, a
run halting after `k < n` steps returns first, after fewer steps, to `retRegs L fp`, and
`Q fp` holds. -/
def FunSpecLt (n entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, k < n → P fp → Safe prog L k ⟨addressOfIndex entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ Safe prog L k' r

/-- **A function's contract**: from `(g^entry, fp)` with `P fp`, a run that halts returns first,
after fewer steps, to `retRegs L fp`, and `Q fp` holds. -/
def FunSpec (entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, P fp → Safe prog L k ⟨addressOfIndex entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ Safe prog L k' r

/-- Some run goes from `s` to `t`. -/
def Reach (s t : Registers K) : Prop := ∃ n, run prog L n s = some t

/-- From `(g^entry, fp)`, a run returns to `retRegs L fp`. -/
def Returns (entry : ℕ) (fp : K) : Prop :=
  ∃ r, retRegs L fp = some r ∧ Reach prog L ⟨addressOfIndex entry, fp⟩ r

end

/-! ## Instructions -/

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

private theorem guard_eq_some_iff {p : Prop} [Decidable p] {u : Unit} :
    (guard p : Option Unit) = some u ↔ p := by
  unfold guard
  split_ifs with h <;> simp [h]

/-- A non-`JUMP` instruction executes exactly when it `Holds`, and falls through. -/
theorem execute_iff_holds {pc : ℕ} {fp : K} {ins : OffsetInstruction} (hj : ins.isJump = false)
    {r : Registers K} :
    execute L ⟨addressOfIndex pc, fp⟩ ins.toLeanIsaInstruction = some r ↔ Holds L pc fp ins ∧ r =
        ⟨addressOfIndex (pc + 1), fp⟩ := by
  have hnext : (⟨addressOfIndex pc, fp⟩ : Registers K).next = ⟨addressOfIndex (pc + 1), fp⟩ := by
    rw [Registers.next, gpow_succ]
  cases ins with
  | jump => simp [OffsetInstruction.isJump] at hj
  | xor a b c =>
    simp only [execute, executeWith, OffsetInstruction.toLeanIsaInstruction, Holds,
        Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | mul a b c =>
    simp only [execute, executeWith, OffsetInstruction.toLeanIsaInstruction, Holds,
        Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | set o k0 k1 k2 =>
    simp only [execute, executeWith, OffsetInstruction.toLeanIsaInstruction, Holds,
        Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨v, hv, rfl, rfl⟩
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨_, hv, rfl, rfl⟩
  | deref o1 o2 o3 mode =>
    simp only [execute, executeWith, OffsetInstruction.toLeanIsaInstruction, Holds,
        Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨p, hp, hpK, v3, h3, v2, h2, rfl, rfl⟩
      exact ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
    · rintro ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
      exact ⟨p, hp, hpK, v3, h3, _, h2, rfl, rfl⟩
  | keccak m0 m1 m2 m3 tail b8 cap out inOdd outOdd outCells =>
    rw [OffsetInstruction.toLeanIsaInstruction, execute_keccak_eq_some_iff, hnext]
    simp only [Holds, keccakInOffset_gpow, keccakOutOffset_gpow]
    constructor
    · rintro ⟨input, output, hin, hout, hk, rfl⟩
      exact ⟨⟨input, output, hin, hout, hk⟩, rfl⟩
    · rintro ⟨⟨input, output, hin, hout, hk⟩, rfl⟩
      exact ⟨input, output, hin, hout, hk, rfl⟩

/-- A `JUMP` executes exactly when its reads are in `K`, to where `JumpsTo` says. -/
theorem execute_jump_iff {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Registers K} :
    execute L ⟨addressOfIndex pc, fp⟩ (OffsetInstruction.jump oc od of).toLeanIsaInstruction =
        some r ↔
      JumpsTo L pc fp oc od of r := by
  have hnext : (⟨addressOfIndex pc, fp⟩ : Registers K).next = ⟨addressOfIndex (pc + 1), fp⟩ := by
    rw [Registers.next, gpow_succ]
  simp only [execute, executeWith, OffsetInstruction.toLeanIsaInstruction, JumpsTo,
      Option.bind_eq_bind,
    Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
  constructor
  · rintro ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩
    exact ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
  · rintro ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
    exact ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩

/-- A pc before the last slot is not the halting one. -/
theorem gpow_ne_pcFinal {pc : ℕ} (hpc : pc < 2 ^ prog.logSize - 1) : addressOfIndex pc ≠
    prog.pcFinal := by
  have hlog : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) prog.logSize_le
  intro h
  have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h
  omega

/-- `DEREF … [Pc]` at pc `pc` stores the return address `g^(pc+2)`. -/
theorem derefSource_pc (pc : ℕ) (fp : K) (v : E) :
    derefSource .pc ⟨addressOfIndex pc, fp⟩ v = ofK (addressOfIndex (pc + 2)) := by
  rw [derefSource, addressOfIndex, addressOfIndex, pow_add, mul_comm]

/-- `DEREF … [Fp]` stores the frame pointer. -/
theorem derefSource_fp (r : Registers K) (v : E) : derefSource .fp r v = ofK r.fp := rfl

/-- `retRegs` reads `fp[0]` and `fp[1]`. -/
theorem retRegs_eq_some_iff {fp : K} {r : Registers K} :
    retRegs L fp = some r ↔ ∃ d f, L.read (fp * addressOfIndex 0) = some d ∧
      L.read (fp * addressOfIndex 1) = some f ∧ r = ⟨d.limb 0, f.limb 0⟩ := by
  simp only [retRegs, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨d, hd, f, hf, rfl⟩
    exact ⟨d, f, hd, hf, rfl⟩
  · rintro ⟨d, f, hd, hf, rfl⟩
    exact ⟨d, hd, f, hf, rfl⟩

/-- A frame whose `fp[0]`, `fp[1]` hold `a`, `b` returns to `(a, b)`. -/
theorem retRegs_of_ofK {fp a b : K} (h0 : L.read (fp * addressOfIndex 0) = some (ofK a))
    (h1 : L.read (fp * addressOfIndex 1) = some (ofK b)) : retRegs L fp = some ⟨a, b⟩ := by
  rw [retRegs_eq_some_iff]
  exact ⟨_, _, h0, h1, by simp⟩

end

/-! ## Soundness: stepping a halting run -/

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

theorem safe_zero_iff {r : Registers K} : Safe prog L 0 r ↔ r = Registers.final prog := by
  simp [Safe]

theorem safe_succ_iff {k : ℕ} {r : Registers K} :
    Safe prog L (k + 1) r ↔
      r ≠ Registers.final prog ∧ ∃ r', step prog L r = some r' ∧ Safe prog L k r' := by
  unfold Safe
  by_cases h : r = Registers.final prog
  · rw [run_succ_of_eq h]; simp [h]
  · rw [run_succ_of_ne_final h]; simp [h, Option.bind_eq_some_iff]

/-- A halting run from a fetched instruction away from the last slot takes a step. -/
theorem Safe.step {pc k : ℕ} {fp : K} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (h : Safe prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ execute L ⟨addressOfIndex pc, fp⟩ ins.toLeanIsaInstruction = some r ∧ Safe
        prog L k' r := by
  cases k with
  | zero =>
    have := congrArg Registers.pc (safe_zero_iff.mp h)
    exact absurd this (gpow_ne_pcFinal hpc)
  | succ k =>
    obtain ⟨-, r, hr, hs⟩ := safe_succ_iff.mp h
    rw [step_of_fetch_eq_some hf] at hr
    exact ⟨k, r, rfl, hr, hs⟩

/-- Through a non-`JUMP`: it `Holds`, and the run goes on at the next pc. -/
theorem Safe.fallThrough {pc k : ℕ} {fp : K} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (hj : ins.isJump = false) (h : Safe prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ Holds L pc fp ins ∧ Safe prog L k' ⟨addressOfIndex (pc + 1), fp⟩ := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  obtain ⟨hh, rfl⟩ := (execute_iff_holds hj).mp hr
  exact ⟨k', rfl, hh, hs⟩

/-- Through a `JUMP`: the run goes on where it `JumpsTo`. -/
theorem Safe.jump {pc k : ℕ} {fp : K} {oc od of : ℕ}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc od
        of).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : Safe prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ JumpsTo L pc fp oc od of r ∧ Safe prog L k' r := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  exact ⟨k', r, rfl, execute_jump_iff.mp hr, hs⟩

/-- Through a taken `JUMP` whose target cells hold `a` and `b`: the run goes on at `(a, b)`. The
facts about the cells may come from anywhere: the code before, a precondition, a callee's
postcondition (a dispatch's target read from a table at a selector bounded by any of them). -/
theorem Safe.jumpTo {pc k oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc od
        of).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * addressOfIndex oc) = some c) (hc0 : c ≠ 0)
    (hd : L.read (fp * addressOfIndex od) = some (ofK a)) (hf' : L.read (fp * addressOfIndex of) =
        some (ofK b))
    (h : Safe prog L k ⟨addressOfIndex pc, fp⟩) : ∃ k', k = k' + 1 ∧ Safe prog L k' ⟨a, b⟩ := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd', hf'', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : d = ofK a := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f = ofK b := Option.some.inj (hf''.symm.trans hf')
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, by simpa using hs⟩

/-- Through a return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc] ≠ 0`: the run goes on at
`retRegs L fp`. -/
theorem Safe.ret {pc k oc : ℕ} {fp : K} {c : E}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc 0
        1).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * addressOfIndex oc) = some c) (hc0 : c ≠ 0)
    (h : Safe prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ ∃ r, retRegs L fp = some r ∧ Safe prog L k' r := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd, hf', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, _, retRegs_eq_some_iff.mpr ⟨d, f, hd, hf', rfl⟩, hs⟩

/-- A halting run of a valid execution starts at `(g^0, 1)`. -/
theorem safe_of_validExecution {input : PublicInput} {t : Execution prog}
    (h : ValidExecution prog input t) : Safe prog t.memory t.stepCount ⟨addressOfIndex 0, 1⟩ := by
  have : (⟨addressOfIndex 0, 1⟩ : Registers K) = Registers.initial :=
      by rw [addressOfIndex, pow_zero]; rfl
  rw [this]
  exact h.2

end

/-! ## Soundness: contracts -/

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ} {entry : ℕ} {P Q : K → Prop}

theorem FunSpec.lt (h : FunSpec prog L entry P Q) (n : ℕ) : FunSpecLt prog L n entry P Q :=
  fun fp k _ hP hs ↦ h fp k hP hs

theorem FunSpec.of_lt (h : ∀ n, FunSpecLt prog L n entry P Q) : FunSpec prog L entry P Q :=
  fun fp k hP hs ↦ h (k + 1) fp k (Nat.lt_succ_self k) hP hs

/-- **Strong induction on the steps left**, for a family of contracts proved together: assuming
every contract for runs shorter than `n`, prove each for runs shorter than `n + 1`. -/
theorem funSpec_induction {ι : Type} {entry : ι → ℕ} {P Q : ι → K → Prop}
    (h : ∀ n, (∀ j, FunSpecLt prog L n (entry j) (P j) (Q j)) →
      ∀ i, FunSpecLt prog L (n + 1) (entry i) (P i) (Q i))
    (i : ι) : FunSpec prog L (entry i) (P i) (Q i) := by
  have hall : ∀ n j, FunSpecLt prog L n (entry j) (P j) (Q j) := by
    intro n
    induction n with
    | zero => exact fun _ _ _ hk ↦ absurd hk (Nat.not_lt_zero _)
    | succ n ih => exact h n ih
  exact FunSpec.of_lt (fun n ↦ hall n i)

/-- **A call**: a halting run entering a function at frame `fp'` after the caller stored the
return registers `r` in `fp'[0]`, `fp'[1]` comes back to `r`, in fewer steps, with `Q fp'`. -/
theorem FunSpecLt.call {n k : ℕ} {fp' : K} {r : Registers K} (hS : FunSpecLt prog L n entry P Q)
    (hk : k < n) (hP : P fp') (hret : retRegs L fp' = some r)
    (h : Safe prog L k ⟨addressOfIndex entry, fp'⟩) : ∃ k' < k, Q fp' ∧ Safe prog L k' r := by
  obtain ⟨k', hk', r', hr', hQ, hs⟩ := hS fp' k hk hP h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact ⟨k', hk', hQ, hs⟩

/-- **A tail call**: a loop iteration at frame `fp` jumping to the loop's entry at the next
frame `fp'`, which returns where `fp` does, returns where `fp` does. -/
theorem FunSpecLt.tail {n k : ℕ} {fp fp' : K} (hS : FunSpecLt prog L n entry P Q) (hk : k < n)
    (hP : P fp') (hret : retRegs L fp' = retRegs L fp) (h : Safe prog L k ⟨addressOfIndex entry,
        fp'⟩) :
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp' ∧ Safe prog L k' r := by
  obtain ⟨k', hk', r, hr, hQ, hs⟩ := hS fp' k hk hP h
  exact ⟨k', hk', r, hret ▸ hr, hQ, hs⟩

/-- `FunSpecLt.call` for a contract already proved. -/
theorem FunSpec.call {k : ℕ} {fp' : K} {r : Registers K} (hS : FunSpec prog L entry P Q)
    (hP : P fp') (hret : retRegs L fp' = some r) (h : Safe prog L k ⟨addressOfIndex entry, fp'⟩) :
    ∃ k' < k, Q fp' ∧ Safe prog L k' r :=
  (hS.lt (k + 1)).call (Nat.lt_succ_self k) hP hret h

end

/-! ## Completeness: building a run -/

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

theorem Reach.refl (s : Registers K) : Reach prog L s s := ⟨0, rfl⟩

theorem Reach.trans {s t u : Registers K} (h₁ : Reach prog L s t) (h₂ : Reach prog L t u) :
    Reach prog L s u := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [run_add, hm]; exact hn⟩

/-- One step from a fetched instruction away from the last slot. -/
theorem reach_step {pc : ℕ} {fp : K} {ins : OffsetInstruction} {r : Registers K}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (h : execute L ⟨addressOfIndex pc, fp⟩ ins.toLeanIsaInstruction = some r) : Reach prog L
        ⟨addressOfIndex pc, fp⟩ r := by
  refine ⟨1, ?_⟩
  rw [run_succ_of_ne (gpow_ne_pcFinal hpc), step_of_fetch_eq_some hf, h]
  rfl

/-- A non-`JUMP` that `Holds` falls through. -/
theorem reach_fallThrough {pc : ℕ} {fp : K} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (hj : ins.isJump = false) (h : Holds L pc fp ins) :
    Reach prog L ⟨addressOfIndex pc, fp⟩ ⟨addressOfIndex (pc + 1), fp⟩ :=
  reach_step hf hpc ((execute_iff_holds hj).mpr ⟨h, rfl⟩)

/-- A `JUMP` goes where it `JumpsTo`. -/
theorem reach_jump {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Registers K}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc od
        of).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : JumpsTo L pc fp oc od of r) :
    Reach prog L ⟨addressOfIndex pc, fp⟩ r :=
  reach_step hf hpc (execute_jump_iff.mpr h)

/-- A return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc]` a nonzero `K` word and `fp[0]`,
`fp[1]` words of `K`, goes to `retRegs L fp`. -/
theorem reach_ret {pc oc : ℕ} {fp : K} {c d f : E} {r : Registers K}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc 0
        1).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * addressOfIndex oc) = some c) (hcK :
        IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * addressOfIndex 0) = some d) (hdK : IsInK d)
    (hf' : L.read (fp * addressOfIndex 1) = some f) (hfK : IsInK f) (hr : retRegs L fp = some r) :
    Reach prog L ⟨addressOfIndex pc, fp⟩ r := by
  obtain ⟨d', f', hd', hf'', rfl⟩ := retRegs_eq_some_iff.mp hr
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f' = f := Option.some.inj (hf''.symm.trans hf')
  exact reach_jump hf hpc ⟨c, d', f', hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩

/-- **A call**, for completeness: a function that returns from frame `fp'`, whose `fp'[0]`,
`fp'[1]` hold `r`, reaches `r`. -/
theorem Returns.reach {entry : ℕ} {fp' : K} {r : Registers K} (h : Returns prog L entry fp')
    (hret : retRegs L fp' = some r) : Reach prog L ⟨addressOfIndex entry, fp'⟩ r := by
  obtain ⟨r', hr', hreach⟩ := h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact hreach

/-- A run from `(g^0, 1)` to the final registers, on a memory holding the public input, is a
valid execution. -/
theorem validExecution_of_reach {input : PublicInput}
    (hb : HoldsPublicInput input (⟨κ, L, 0⟩ : Execution prog))
    (h : Reach prog L ⟨addressOfIndex 0, 1⟩ (Registers.final prog)) :
    ∃ n, ValidExecution prog input ⟨κ, L, n⟩ := by
  obtain ⟨n, hn⟩ := h
  have : (⟨addressOfIndex 0, 1⟩ : Registers K) = Registers.initial :=
      by rw [addressOfIndex, pow_zero]; rfl
  rw [this] at hn
  exact ⟨n, hb, hn⟩

end

/-! ## Soundness on the run from the initial state

`SafeReached prog L k r`: the run from the initial state `(g^0, 1)` reaches `r`, and from `r`
halts after `k` steps. The contracts over it (`FunSpecLtReached`, `FunSpecReached`) assume of a
function's entry that the run from `(g^0, 1)` reached it, and give it of the return, so a
postcondition may say that the frame was entered on that run. The rules are `Safe`'s, each step
extending the reach (`SafeReached.fallThrough`, `SafeReached.jump`). -/

section

variable {κ : ℕ} (prog : LeanIsaProgram) (L : MemoryImage κ)

/-- **The run from `(g^0, 1)` reaches `r`, and from `r` halts after `k` steps.** -/
def SafeReached (k : ℕ) (r : Registers K) : Prop :=
  Safe prog L k r ∧ Reach prog L ⟨addressOfIndex 0, 1⟩ r

/-- **A function's contract on the run from `(g^0, 1)`, for runs shorter than `n`**: from
`(g^entry, fp)` reached from `(g^0, 1)`, with `P fp`, a run halting after `k < n` steps returns
first, after fewer steps, to `retRegs L fp`, and `Q fp` holds. -/
def FunSpecLtReached (n entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, k < n → P fp → SafeReached prog L k ⟨addressOfIndex entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ SafeReached prog L k' r

/-- **A function's contract on the run from `(g^0, 1)`**. -/
def FunSpecReached (entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, P fp → SafeReached prog L k ⟨addressOfIndex entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ SafeReached prog L k' r

end

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ} {entry : ℕ} {P Q : K → Prop}

/-- Through a non-`JUMP`: it `Holds`, and the run goes on at the next pc. -/
theorem SafeReached.fallThrough {pc k : ℕ} {fp : K} {ins : OffsetInstruction}
    (hf : prog.fetch (addressOfIndex pc) = some ins.toLeanIsaInstruction) (hpc : pc < 2 ^
        prog.logSize - 1)
    (hj : ins.isJump = false) (h : SafeReached prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ Holds L pc fp ins ∧ SafeReached prog L k' ⟨addressOfIndex (pc + 1), fp⟩ := by
  obtain ⟨k', rfl, hh, hs⟩ := h.1.fallThrough hf hpc hj
  exact ⟨k', rfl, hh, hs, h.2.trans (reach_fallThrough hf hpc hj hh)⟩

/-- Through a `JUMP`: the run goes on where it `JumpsTo`. -/
theorem SafeReached.jump {pc k : ℕ} {fp : K} {oc od of : ℕ}
    (hf : prog.fetch (addressOfIndex pc) = some (OffsetInstruction.jump oc od
        of).toLeanIsaInstruction)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : SafeReached prog L k ⟨addressOfIndex pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ JumpsTo L pc fp oc od of r ∧ SafeReached prog L k' r := by
  obtain ⟨k', r, rfl, hj, hs⟩ := h.1.jump hf hpc
  exact ⟨k', r, rfl, hj, hs, h.2.trans (reach_jump hf hpc hj)⟩

theorem FunSpecReached.lt (h : FunSpecReached prog L entry P Q) (n : ℕ) :
    FunSpecLtReached prog L n entry P Q :=
  fun fp k _ hP hs ↦ h fp k hP hs

theorem FunSpecReached.of_lt (h : ∀ n, FunSpecLtReached prog L n entry P Q) :
    FunSpecReached prog L entry P Q :=
  fun fp k hP hs ↦ h (k + 1) fp k (Nat.lt_succ_self k) hP hs

theorem FunSpecLtReached.mono {m n : ℕ} (hmn : m ≤ n) (h : FunSpecLtReached prog L n entry P Q) :
    FunSpecLtReached prog L m entry P Q :=
  fun fp k hk hP hs ↦ h fp k (Nat.lt_of_lt_of_le hk hmn) hP hs

/-- **Strong induction on the steps left**, for a family of contracts on the run from
`(g^0, 1)` proved together. -/
theorem funSpecReached_induction {ι : Type} {entry : ι → ℕ} {P Q : ι → K → Prop}
    (h : ∀ n, (∀ j, FunSpecLtReached prog L n (entry j) (P j) (Q j)) →
      ∀ i, FunSpecLtReached prog L (n + 1) (entry i) (P i) (Q i))
    (i : ι) : FunSpecReached prog L (entry i) (P i) (Q i) := by
  have hall : ∀ n j, FunSpecLtReached prog L n (entry j) (P j) (Q j) := by
    intro n
    induction n with
    | zero => exact fun _ _ _ hk ↦ absurd hk (Nat.not_lt_zero _)
    | succ n ih => exact h n ih
  exact FunSpecReached.of_lt (fun n ↦ hall n i)

/-- **A call**: a halting run entering a function at frame `fp'` after the caller stored the
return registers `r` in `fp'[0]`, `fp'[1]` comes back to `r`, in fewer steps, with `Q fp'`. -/
theorem FunSpecLtReached.call {n k : ℕ} {fp' : K} {r : Registers K}
    (hS : FunSpecLtReached prog L n entry P Q) (hk : k < n) (hP : P fp')
    (hret : retRegs L fp' = some r) (h : SafeReached prog L k ⟨addressOfIndex entry, fp'⟩) :
    ∃ k' < k, Q fp' ∧ SafeReached prog L k' r := by
  obtain ⟨k', hk', r', hr', hQ, hs⟩ := hS fp' k hk hP h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact ⟨k', hk', hQ, hs⟩

/-- **A tail call**: a loop iteration at frame `fp` jumping to the loop's entry at the next
frame `fp'`, which returns where `fp` does, returns where `fp` does. -/
theorem FunSpecLtReached.tail {n k : ℕ} {fp fp' : K} (hS : FunSpecLtReached prog L n entry P Q)
    (hk : k < n) (hP : P fp') (hret : retRegs L fp' = retRegs L fp)
    (h : SafeReached prog L k ⟨addressOfIndex entry, fp'⟩) :
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp' ∧ SafeReached prog L k' r := by
  obtain ⟨k', hk', r, hr, hQ, hs⟩ := hS fp' k hk hP h
  exact ⟨k', hk', r, hret ▸ hr, hQ, hs⟩

end

end
end LeanVM.Guest
