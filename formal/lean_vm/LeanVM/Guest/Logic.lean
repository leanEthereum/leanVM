/-
  LeanVM.Guest.Logic

  A program logic for compiled functions over `run`: one lemma per instruction shape, function
  contracts in continuation form with strong induction on the steps left, and the run-building
  counterparts for completeness.
-/

module

public import LeanVM.Guest.Code

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

variable {κ : ℕ} (prog : Program) (L : MemImage κ)

/-- The run from `r` halts after exactly `k` steps. -/
def Safe (k : ℕ) (r : Regs K) : Prop := run prog L k r = some (Regs.final prog)

/-- What a non-`JUMP` instruction at `(g^pc, fp)` checks of the memory. -/
def Holds (pc : ℕ) (fp : K) : OInstr → Prop
  | .xor a b c => ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow c) = some (vA + vB)
  | .mul a b c => ∃ vA vB, L.read (fp * gpow a) = some vA ∧ L.read (fp * gpow b) = some vB ∧
      L.read (fp * gpow c) = some (vA * vB)
  | .set o k0 k1 k2 => L.read (fp * gpow o) = some (OInstr.imm k0 k1 k2)
  | .deref o1 o2 o3 mode => ∃ p v3, L.read (fp * gpow o1) = some p ∧ IsInK p ∧
      L.read (fp * gpow o3) = some v3 ∧
      L.read (p.limb 0 * gpow o2) = some (derefSource mode ⟨gpow pc, fp⟩ v3)
  | .jump .. => False
  | .blake2s m0 m1 m2 m3 cv out md => ∃ w0 w1 w2 w3 c0 c1 d0 d1 v,
      L.read (fp * gpow m0) = some w0 ∧ L.read (fp * gpow m1) = some w1 ∧
      L.read (fp * gpow m2) = some w2 ∧ L.read (fp * gpow m3) = some w3 ∧
      L.read (fp * gpow cv) = some c0 ∧ L.read (fp * (g * gpow cv)) = some c1 ∧
      L.read (fp * gpow out) = some d0 ∧ L.read (fp * (g * gpow out)) = some d1 ∧
      L.read (fp * gpow md) = some v ∧ CompressCells ![w0, w1, w2, w3] c0 c1 d0 d1 v

/-- What a `JUMP fp[oc], fp[od], fp[of]` at `(g^pc, fp)` checks, and where it goes. -/
def JumpsTo (pc : ℕ) (fp : K) (oc od of : ℕ) (r : Regs K) : Prop :=
  ∃ c d f, L.read (fp * gpow oc) = some c ∧ L.read (fp * gpow od) = some d ∧
    L.read (fp * gpow of) = some f ∧ IsInK c ∧ IsInK d ∧ IsInK f ∧
    r = if c = 0 then ⟨gpow (pc + 1), fp⟩ else ⟨d.limb 0, f.limb 0⟩

/-- The caller's registers a function at frame `fp` returns to: `(fp[0], fp[1])`. -/
noncomputable def retRegs (fp : K) : Option (Regs K) :=
  (L.read (fp * gpow 0)).bind fun d ↦ (L.read (fp * gpow 1)).map fun f ↦ ⟨d.limb 0, f.limb 0⟩

/-- **A function's contract, for runs shorter than `n`**: from `(g^entry, fp)` with `P fp`, a
run halting after `k < n` steps returns first, after fewer steps, to `retRegs L fp`, and
`Q fp` holds. -/
def FunSpecLt (n entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, k < n → P fp → Safe prog L k ⟨gpow entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ Safe prog L k' r

/-- **A function's contract**: from `(g^entry, fp)` with `P fp`, a run that halts returns first,
after fewer steps, to `retRegs L fp`, and `Q fp` holds. -/
def FunSpec (entry : ℕ) (P Q : K → Prop) : Prop :=
  ∀ fp k, P fp → Safe prog L k ⟨gpow entry, fp⟩ →
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp ∧ Safe prog L k' r

/-- Some run goes from `s` to `t`. -/
def Reach (s t : Regs K) : Prop := ∃ n, run prog L n s = some t

/-- From `(g^entry, fp)`, a run returns to `retRegs L fp`. -/
def Returns (entry : ℕ) (fp : K) : Prop :=
  ∃ r, retRegs L fp = some r ∧ Reach prog L ⟨gpow entry, fp⟩ r

end

/-! ## Instructions -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

private theorem guard_eq_some_iff {p : Prop} [Decidable p] {u : Unit} :
    (guard p : Option Unit) = some u ↔ p := by
  unfold guard
  split_ifs with h <;> simp [h]

/-- A non-`JUMP` instruction executes exactly when it `Holds`, and falls through. -/
theorem execute_iff_holds {pc : ℕ} {fp : K} {ins : OInstr} (hj : ins.isJump = false)
    {r : Regs K} :
    execute L ⟨gpow pc, fp⟩ ins.toInstr = some r ↔ Holds L pc fp ins ∧ r = ⟨gpow (pc + 1), fp⟩ := by
  have hnext : (⟨gpow pc, fp⟩ : Regs K).next = ⟨gpow (pc + 1), fp⟩ := by
    rw [Regs.next, gpow_succ]
  cases ins with
  | jump => simp [OInstr.isJump] at hj
  | xor a b c =>
    simp only [execute, executeWith, OInstr.toInstr, Holds, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | mul a b c =>
    simp only [execute, executeWith, OInstr.toInstr, Holds, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨vA, hA, vB, hB, vC, hC, rfl, rfl⟩
      exact ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
    · rintro ⟨⟨vA, vB, hA, hB, hC⟩, rfl⟩
      exact ⟨vA, hA, vB, hB, _, hC, rfl, rfl⟩
  | set o k0 k1 k2 =>
    simp only [execute, executeWith, OInstr.toInstr, Holds, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨v, hv, rfl, rfl⟩
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨_, hv, rfl, rfl⟩
  | deref o1 o2 o3 mode =>
    simp only [execute, executeWith, OInstr.toInstr, Holds, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
    constructor
    · rintro ⟨p, hp, hpK, v3, h3, v2, h2, rfl, rfl⟩
      exact ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
    · rintro ⟨⟨p, v3, hp, hpK, h3, h2⟩, rfl⟩
      exact ⟨p, hp, hpK, v3, h3, _, h2, rfl, rfl⟩
  | blake2s m0 m1 m2 m3 cv out md =>
    simp only [execute, executeWith, OInstr.toInstr, Holds, Option.bind_eq_bind,
      Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons]
    constructor
    · rintro ⟨w0, h0, w1, h1, w2, h2, w3, h3, c0, hc0, c1, hc1, d0, hd0, d1, hd1, v, hv, hcomp,
        rfl⟩
      exact ⟨⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hcomp⟩,
        rfl⟩
    · rintro ⟨⟨w0, w1, w2, w3, c0, c1, d0, d1, v, h0, h1, h2, h3, hc0, hc1, hd0, hd1, hv, hcomp⟩,
        rfl⟩
      exact ⟨w0, h0, w1, h1, w2, h2, w3, h3, c0, hc0, c1, hc1, d0, hd0, d1, hd1, v, hv, hcomp,
        rfl⟩

/-- A `JUMP` executes exactly when its reads are in `K`, to where `JumpsTo` says. -/
theorem execute_jump_iff {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Regs K} :
    execute L ⟨gpow pc, fp⟩ (OInstr.jump oc od of).toInstr = some r ↔
      JumpsTo L pc fp oc od of r := by
  have hnext : (⟨gpow pc, fp⟩ : Regs K).next = ⟨gpow (pc + 1), fp⟩ := by
    rw [Regs.next, gpow_succ]
  simp only [execute, executeWith, OInstr.toInstr, JumpsTo, Option.bind_eq_bind,
    Option.bind_eq_some_iff, guard_eq_some_iff, exists_const, Option.pure_def, Option.some.injEq, hnext]
  constructor
  · rintro ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩
    exact ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
  · rintro ⟨c, d, f, hc, hd, hf, hcK, hdK, hfK, rfl⟩
    exact ⟨c, hc, d, hd, f, hf, ⟨hcK, hdK, hfK⟩, rfl⟩

/-- A pc before the last slot is not the halting one. -/
theorem gpow_ne_finalPc {pc : ℕ} (hpc : pc < 2 ^ prog.logSize - 1) : gpow pc ≠ prog.finalPc := by
  have hlog : 2 ^ prog.logSize ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) prog.logSize_le
  intro h
  have := gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h
  omega

/-- `DEREF … [Pc]` at pc `pc` stores the return address `g^(pc+2)`. -/
theorem derefSource_pc (pc : ℕ) (fp : K) (v : E) :
    derefSource .pc ⟨gpow pc, fp⟩ v = ofK (gpow (pc + 2)) := by
  rw [derefSource, gpow, gpow, pow_add, mul_comm]

/-- `DEREF … [Fp]` stores the frame pointer. -/
theorem derefSource_fp (r : Regs K) (v : E) : derefSource .fp r v = ofK r.fp := rfl

/-- `retRegs` reads `fp[0]` and `fp[1]`. -/
theorem retRegs_eq_some_iff {fp : K} {r : Regs K} :
    retRegs L fp = some r ↔ ∃ d f, L.read (fp * gpow 0) = some d ∧
      L.read (fp * gpow 1) = some f ∧ r = ⟨d.limb 0, f.limb 0⟩ := by
  simp only [retRegs, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨d, hd, f, hf, rfl⟩
    exact ⟨d, f, hd, hf, rfl⟩
  · rintro ⟨d, f, hd, hf, rfl⟩
    exact ⟨d, hd, f, hf, rfl⟩

/-- A frame whose `fp[0]`, `fp[1]` hold `a`, `b` returns to `(a, b)`. -/
theorem retRegs_of_ofK {fp a b : K} (h0 : L.read (fp * gpow 0) = some (ofK a))
    (h1 : L.read (fp * gpow 1) = some (ofK b)) : retRegs L fp = some ⟨a, b⟩ := by
  rw [retRegs_eq_some_iff]
  exact ⟨_, _, h0, h1, by simp⟩

end

/-! ## Soundness: stepping a halting run -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem safe_zero_iff {r : Regs K} : Safe prog L 0 r ↔ r = Regs.final prog := by
  simp [Safe]

theorem safe_succ_iff {k : ℕ} {r : Regs K} :
    Safe prog L (k + 1) r ↔
      r.pc ≠ prog.finalPc ∧ ∃ r', step prog L r = some r' ∧ Safe prog L k r' := by
  unfold Safe
  by_cases h : r.pc = prog.finalPc
  · simp [run_succ_of_eq h, h]
  · simp [run_succ_of_ne h, h, Option.bind_eq_some_iff]

/-- A halting run from a fetched instruction away from the last slot takes a step. -/
theorem Safe.step {pc k : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (h : Safe prog L k ⟨gpow pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ execute L ⟨gpow pc, fp⟩ ins.toInstr = some r ∧ Safe prog L k' r := by
  cases k with
  | zero =>
    have := congrArg Regs.pc (safe_zero_iff.mp h)
    exact absurd this (gpow_ne_finalPc hpc)
  | succ k =>
    obtain ⟨-, r, hr, hs⟩ := safe_succ_iff.mp h
    rw [step_of_fetch_eq_some hf] at hr
    exact ⟨k, r, rfl, hr, hs⟩

/-- Through a non-`JUMP`: it `Holds`, and the run goes on at the next pc. -/
theorem Safe.fallThrough {pc k : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (hj : ins.isJump = false) (h : Safe prog L k ⟨gpow pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ Holds L pc fp ins ∧ Safe prog L k' ⟨gpow (pc + 1), fp⟩ := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  obtain ⟨hh, rfl⟩ := (execute_iff_holds hj).mp hr
  exact ⟨k', rfl, hh, hs⟩

/-- Through a `JUMP`: the run goes on where it `JumpsTo`. -/
theorem Safe.jump {pc k : ℕ} {fp : K} {oc od of : ℕ}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : Safe prog L k ⟨gpow pc, fp⟩) :
    ∃ k' r, k = k' + 1 ∧ JumpsTo L pc fp oc od of r ∧ Safe prog L k' r := by
  obtain ⟨k', r, rfl, hr, hs⟩ := h.step hf hpc
  exact ⟨k', r, rfl, execute_jump_iff.mp hr, hs⟩

/-- Through a taken `JUMP` whose target cells hold `a` and `b`: the run goes on at `(a, b)`. The
facts about the cells may come from anywhere: the code before, a precondition, a callee's
postcondition (a dispatch's target read from a table at a selector bounded by any of them). -/
theorem Safe.jumpTo {pc k oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hc0 : c ≠ 0)
    (hd : L.read (fp * gpow od) = some (ofK a)) (hf' : L.read (fp * gpow of) = some (ofK b))
    (h : Safe prog L k ⟨gpow pc, fp⟩) : ∃ k', k = k' + 1 ∧ Safe prog L k' ⟨a, b⟩ := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd', hf'', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  obtain rfl : d = ofK a := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f = ofK b := Option.some.inj (hf''.symm.trans hf')
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, by simpa using hs⟩

/-- Through a `JUMP` not taken, `fp[oc] = 0`: the run goes on at the next pc. -/
theorem Safe.jumpNot {pc k oc od of : ℕ} {fp : K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some 0)
    (h : Safe prog L k ⟨gpow pc, fp⟩) : ∃ k', k = k' + 1 ∧ Safe prog L k' ⟨gpow (pc + 1), fp⟩ := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', -, -, -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = 0 := Option.some.inj (hc'.symm.trans hc)
  rw [ite_eq_left rfl] at hs
  exact ⟨k', rfl, hs⟩

/-- Through a return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc] ≠ 0`: the run goes on at
`retRegs L fp`. -/
theorem Safe.ret {pc k oc : ℕ} {fp : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc 0 1).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hc0 : c ≠ 0)
    (h : Safe prog L k ⟨gpow pc, fp⟩) :
    ∃ k', k = k' + 1 ∧ ∃ r, retRegs L fp = some r ∧ Safe prog L k' r := by
  obtain ⟨k', r, rfl, ⟨c', d, f, hc', hd, hf', -, -, -, rfl⟩, hs⟩ := h.jump hf hpc
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
  rw [ite_eq_right hc0] at hs
  exact ⟨k', rfl, _, retRegs_eq_some_iff.mpr ⟨d, f, hd, hf', rfl⟩, hs⟩

/-- A halting run of a valid execution starts at `(g^0, 1)`. -/
theorem safe_of_validExecution {input : PublicInput} {t : Trace prog}
    (h : ValidExecution prog input t) : Safe prog t.image t.steps ⟨gpow 0, 1⟩ := by
  have : (⟨gpow 0, 1⟩ : Regs K) = Regs.initial := by rw [gpow, pow_zero]; rfl
  rw [this]
  exact h.2

end

/-! ## Soundness: contracts -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ} {entry : ℕ} {P Q : K → Prop}

theorem FunSpec.lt (h : FunSpec prog L entry P Q) (n : ℕ) : FunSpecLt prog L n entry P Q :=
  fun fp k _ hP hs ↦ h fp k hP hs

theorem FunSpec.of_lt (h : ∀ n, FunSpecLt prog L n entry P Q) : FunSpec prog L entry P Q :=
  fun fp k hP hs ↦ h (k + 1) fp k (Nat.lt_succ_self k) hP hs

theorem FunSpecLt.mono {m n : ℕ} (hmn : m ≤ n) (h : FunSpecLt prog L n entry P Q) :
    FunSpecLt prog L m entry P Q :=
  fun fp k hk hP hs ↦ h fp k (Nat.lt_of_lt_of_le hk hmn) hP hs

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
theorem FunSpecLt.call {n k : ℕ} {fp' : K} {r : Regs K} (hS : FunSpecLt prog L n entry P Q)
    (hk : k < n) (hP : P fp') (hret : retRegs L fp' = some r)
    (h : Safe prog L k ⟨gpow entry, fp'⟩) : ∃ k' < k, Q fp' ∧ Safe prog L k' r := by
  obtain ⟨k', hk', r', hr', hQ, hs⟩ := hS fp' k hk hP h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact ⟨k', hk', hQ, hs⟩

/-- **A tail call**: a loop iteration at frame `fp` jumping to the loop's entry at the next
frame `fp'`, which returns where `fp` does, returns where `fp` does. -/
theorem FunSpecLt.tail {n k : ℕ} {fp fp' : K} (hS : FunSpecLt prog L n entry P Q) (hk : k < n)
    (hP : P fp') (hret : retRegs L fp' = retRegs L fp) (h : Safe prog L k ⟨gpow entry, fp'⟩) :
    ∃ k' < k, ∃ r, retRegs L fp = some r ∧ Q fp' ∧ Safe prog L k' r := by
  obtain ⟨k', hk', r, hr, hQ, hs⟩ := hS fp' k hk hP h
  exact ⟨k', hk', r, hret ▸ hr, hQ, hs⟩

/-- `FunSpecLt.call` for a contract already proved. -/
theorem FunSpec.call {k : ℕ} {fp' : K} {r : Regs K} (hS : FunSpec prog L entry P Q)
    (hP : P fp') (hret : retRegs L fp' = some r) (h : Safe prog L k ⟨gpow entry, fp'⟩) :
    ∃ k' < k, Q fp' ∧ Safe prog L k' r :=
  (hS.lt (k + 1)).call (Nat.lt_succ_self k) hP hret h

end

/-! ## Completeness: building a run -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

theorem Reach.refl (s : Regs K) : Reach prog L s s := ⟨0, rfl⟩

theorem Reach.trans {s t u : Regs K} (h₁ : Reach prog L s t) (h₂ : Reach prog L t u) :
    Reach prog L s u := by
  obtain ⟨m, hm⟩ := h₁
  obtain ⟨n, hn⟩ := h₂
  exact ⟨m + n, by rw [run_add, hm]; exact hn⟩

/-- One step from a fetched instruction away from the last slot. -/
theorem reach_step {pc : ℕ} {fp : K} {ins : OInstr} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (h : execute L ⟨gpow pc, fp⟩ ins.toInstr = some r) : Reach prog L ⟨gpow pc, fp⟩ r := by
  refine ⟨1, ?_⟩
  rw [run_succ_of_ne (gpow_ne_finalPc hpc), step_of_fetch_eq_some hf, h]
  rfl

/-- A non-`JUMP` that `Holds` falls through. -/
theorem reach_fallThrough {pc : ℕ} {fp : K} {ins : OInstr}
    (hf : prog.fetch (gpow pc) = some ins.toInstr) (hpc : pc < 2 ^ prog.logSize - 1)
    (hj : ins.isJump = false) (h : Holds L pc fp ins) :
    Reach prog L ⟨gpow pc, fp⟩ ⟨gpow (pc + 1), fp⟩ :=
  reach_step hf hpc ((execute_iff_holds hj).mpr ⟨h, rfl⟩)

/-- A `JUMP` goes where it `JumpsTo`. -/
theorem reach_jump {pc : ℕ} {fp : K} {oc od of : ℕ} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (h : JumpsTo L pc fp oc od of r) :
    Reach prog L ⟨gpow pc, fp⟩ r :=
  reach_step hf hpc (execute_jump_iff.mpr h)

/-- A taken `JUMP` whose target cells hold `a` and `b` goes to `(a, b)`. -/
theorem reach_jumpTo {pc oc od of : ℕ} {fp a b : K} {c : E}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc od of).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow od) = some (ofK a))
    (hf' : L.read (fp * gpow of) = some (ofK b)) : Reach prog L ⟨gpow pc, fp⟩ ⟨a, b⟩ := by
  have hK : ∀ x : K, IsInK (ofK x) := fun x ↦ (isInK_iff _).mpr ⟨x, rfl⟩
  have := reach_jump (L := L) hf hpc ⟨c, _, _, hc, hd, hf', hcK, hK a, hK b, rfl⟩
  rw [ite_eq_right hc0] at this
  simpa using this

/-- A return, `JUMP fp[oc], fp[0], fp[1]` with `fp[oc]` a nonzero `K` word and `fp[0]`,
`fp[1]` words of `K`, goes to `retRegs L fp`. -/
theorem reach_ret {pc oc : ℕ} {fp : K} {c d f : E} {r : Regs K}
    (hf : prog.fetch (gpow pc) = some (OInstr.jump oc 0 1).toInstr)
    (hpc : pc < 2 ^ prog.logSize - 1) (hc : L.read (fp * gpow oc) = some c) (hcK : IsInK c)
    (hc0 : c ≠ 0) (hd : L.read (fp * gpow 0) = some d) (hdK : IsInK d)
    (hf' : L.read (fp * gpow 1) = some f) (hfK : IsInK f) (hr : retRegs L fp = some r) :
    Reach prog L ⟨gpow pc, fp⟩ r := by
  obtain ⟨d', f', hd', hf'', rfl⟩ := retRegs_eq_some_iff.mp hr
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  obtain rfl : f' = f := Option.some.inj (hf''.symm.trans hf')
  exact reach_jump hf hpc ⟨c, d', f', hc, hd, hf', hcK, hdK, hfK, by rw [ite_eq_right hc0]⟩

/-- **A call**, for completeness: a function that returns from frame `fp'`, whose `fp'[0]`,
`fp'[1]` hold `r`, reaches `r`. -/
theorem Returns.reach {entry : ℕ} {fp' : K} {r : Regs K} (h : Returns prog L entry fp')
    (hret : retRegs L fp' = some r) : Reach prog L ⟨gpow entry, fp'⟩ r := by
  obtain ⟨r', hr', hreach⟩ := h
  obtain rfl : r' = r := Option.some.inj (hr'.symm.trans hret)
  exact hreach

/-- **Strong induction on a measure**, for a family of functions shown to return together:
assuming every call of a smaller measure returns, show that each call returns. -/
theorem returns_induction {ι : Type} {entry : ι → ℕ} {P : ι → K → Prop} (μ : ι → K → ℕ)
    (h : ∀ i fp, P i fp → (∀ j fp', μ j fp' < μ i fp → P j fp' → Returns prog L (entry j) fp') →
      Returns prog L (entry i) fp)
    (i : ι) (fp : K) (hP : P i fp) : Returns prog L (entry i) fp := by
  have hall : ∀ m j fp', μ j fp' < m → P j fp' → Returns prog L (entry j) fp' := by
    intro m
    induction m with
    | zero => exact fun _ _ hm ↦ absurd hm (Nat.not_lt_zero _)
    | succ m ih =>
      exact fun j fp' hm hP' ↦ h j fp' hP' fun j' fp'' hlt hP'' ↦ ih j' fp'' (by omega) hP''
  exact hall _ i fp (Nat.lt_succ_self _) hP

/-- A run from `(g^0, 1)` to the final registers, on a memory holding the public input, is a
valid execution. -/
theorem validExecution_of_reach {input : PublicInput}
    (hb : HasPublicBoundary input (⟨κ, L, 0⟩ : Trace prog))
    (h : Reach prog L ⟨gpow 0, 1⟩ (Regs.final prog)) :
    ∃ n, ValidExecution prog input ⟨κ, L, n⟩ := by
  obtain ⟨n, hn⟩ := h
  have : (⟨gpow 0, 1⟩ : Regs K) = Regs.initial := by rw [gpow, pow_zero]; rfl
  rw [this] at hn
  exact ⟨n, hb, hn⟩

end

end
end LeanVM.Guest
