/-
  LeanVM.Semantics.Lemmas

  The lemmas about the definitions of `Statement.LeanIsa`: addressing, fetching, the step, and the
  execution loop.
-/

module

public import Statement.LeanIsa
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Parameters.Isa

/-!
# Lemmas about leanISA

The load-bearing lemmas of `LeanVM.Semantics`, by section: the memory reader, the program's
fetch, the lanes of a `K` word, the step, and the execution loop (`run`), with the register
sequence of a trace (`Execution.regs`).
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Addressing -/

/-- The specification of `addressIndex?`: on an address space of at most `2 ^ 63` cells, so that
`2 ^ κ ≤ orderOf g`, `addressIndex? κ a = some i` exactly when `a = g ^ i`. -/
theorem gLog?_spec {κ : ℕ} (hκ : κ < 64) {a : K} {i : Fin (2 ^ κ)} :
    addressIndex? κ a = some i ↔ a = addressOfIndex i := by
  unfold addressIndex?
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro hi
      obtain rfl := Option.some.inj hi
      exact hc
    · intro hi
      have hbound : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hj : ((Classical.choose h : Fin (2 ^ κ)) : ℕ) < 2 ^ 64 - 1 := by
        have := (Classical.choose h).isLt; omega
      have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
      exact congrArg some (Fin.ext (gpow_injOn hj hi' (hc.symm.trans hi)))
  · exact ⟨fun hi ↦ (nomatch hi), fun hi ↦ absurd ⟨i, hi⟩ h⟩

/-- `addressIndex?` fails exactly on the addresses that are no power below `2 ^ κ`; no size bound is
needed. -/
theorem gLog?_eq_none_iff {κ : ℕ} {a : K} :
    addressIndex? κ a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ addressOfIndex i := by
  unfold addressIndex?
  split_ifs with h
  · exact ⟨fun hn ↦ (nomatch hn), fun hn ↦ absurd h (not_exists.mpr hn)⟩
  · exact ⟨fun _ ↦ not_exists.mp h, fun _ ↦ rfl⟩

/-- `0` is never an address, whatever the size. -/
theorem gLog?_zero (κ : ℕ) : addressIndex? κ 0 = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ gpow_ne_zero i h.symm

/-- A power past the end is no address: `g ^ j` with `2 ^ κ ≤ j < orderOf g` has no index. -/
theorem gLog?_gpow_eq_none {κ j : ℕ} (hj : 2 ^ κ ≤ j) (hj' : j < 2 ^ 64 - 1) :
    addressIndex? κ (addressOfIndex j) = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ by
    have hi : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have := gpow_injOn hj' hi h
    have := i.isLt
    omega

/-! ## Readers and decision procedures -/

/-- The limbs of the word at `a`, zero when there is none: `read`, as a row's three-limb column
(the arithmetization's row builders); specified by `ofLimbs_limbsAt`. -/
noncomputable def MemoryImage.limbsAt {κ : ℕ} (L : MemoryImage κ) (a : K) : Vector K 3 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1, v.limb 2]
  | none => #v[0, 0, 0]

/-- The two limbs of the word at `a`, zero when there is none: `read`, as a row's two-limb cell
column; specified by `ofCell_cellAt`. -/
noncomputable def MemoryImage.cellAt {κ : ℕ} (L : MemoryImage κ) (a : K) : Vector K 2 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-! ## Memory -/

/-! ### Load-bearing lemmas -/

/-- Reading at the address of index `i` gives word `i`. -/
theorem MemoryImage.read_gpow {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) (i : Fin (2 ^ κ)) :
    L.read (addressOfIndex i) = some (L i) := by
  rw [MemoryImage.read, (gLog?_spec hκ).mpr rfl, Option.map_some]

/-- A successful read is the word of the address's index. -/
theorem MemoryImage.read_eq_some_iff {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) {a : K} {v : E} :
    L.read a = some v ↔ ∃ i : Fin (2 ^ κ), a = addressOfIndex i ∧ L i = v := by
  simp only [MemoryImage.read, Option.map_eq_some_iff, gLog?_spec hκ]

/-- A read fails exactly at the addresses that are no power below `2 ^ κ`. -/
theorem MemoryImage.read_eq_none_iff {κ : ℕ} (L : MemoryImage κ) {a : K} :
    L.read a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ addressOfIndex i := by
  rw [MemoryImage.read, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Address `0` reads nothing. -/
theorem MemoryImage.read_zero {κ : ℕ} (L : MemoryImage κ) : L.read 0 = none := by
  rw [MemoryImage.read, gLog?_zero, Option.map_none]

/-- The limbs read back at an address that holds a word form that word. -/
theorem MemoryImage.ofLimbs_limbsAt {κ : ℕ} {L : MemoryImage κ} {a : K} {v : E}
    (h : L.read a = some v) :
    E.ofLimbs (L.limbsAt a)[0] (L.limbsAt a)[1] (L.limbsAt a)[2] = v := by
  unfold MemoryImage.limbsAt
  rw [h]
  exact ofLimbs_limb v

/-- The low limb read back at an address that holds a word is the word's. -/
theorem MemoryImage.limbsAt_getElem_zero {κ : ℕ} {L : MemoryImage κ} {a : K} {v : E}
    (h : L.read a = some v) : (L.limbsAt a)[0] = v.limb 0 := by
  unfold MemoryImage.limbsAt
  rw [h]
  rfl

/-- The two limbs read back at an address that holds a canonical word form that word. -/
theorem MemoryImage.ofCell_cellAt {κ : ℕ} {L : MemoryImage κ} {a : K} {v : E}
    (h : L.read a = some v) (hc : IsCanonical128 v) : E.ofCell (L.cellAt a) = v := by
  unfold MemoryImage.cellAt
  rw [h]
  show E.ofLimbs (v.limb 0) (v.limb 1) 0 = v
  calc E.ofLimbs (v.limb 0) (v.limb 1) 0 = E.ofLimbs (v.limb 0) (v.limb 1) (v.limb 2) := by
        rw [show v.limb 2 = 0 from hc]
    _ = v := ofLimbs_limb v

/-- The two words determine the input: no lane is dropped or shared. -/
theorem PublicInput.words_injective :
    Function.Injective fun p : PublicInput ↦ (p.word0, p.word1) := by
  rintro ⟨p⟩ ⟨q⟩ h
  simp only [Prod.mk.injEq, PublicInput.word0, PublicInput.word1] at h
  congr 1
  funext i
  fin_cases i
  · simpa using congrArg (fun z : E ↦ z.limb 0) h.1
  · simpa using congrArg (fun z : E ↦ z.limb 1) h.1
  · simpa using congrArg (fun z : E ↦ z.limb 0) h.2
  · simpa using congrArg (fun z : E ↦ z.limb 1) h.2

/-! ## Instruction -/

/-! ### Proof helpers -/

/-- The cap keeps the bytecode inside the address space `gLog?_spec` covers. -/
private theorem LeanIsaProgram.logSize_lt (prog : LeanIsaProgram) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-! ### Load-bearing lemmas -/

/-- Fetching at the address of index `i` gives instruction `i`. -/
theorem LeanIsaProgram.fetch_gpow (prog : LeanIsaProgram) (i : Fin (2 ^ prog.logSize)) :
    prog.fetch (addressOfIndex i) = some (prog.instructions i) := by
  rw [LeanIsaProgram.fetch, (gLog?_spec prog.logSize_lt).mpr rfl, Option.map_some]

/-- A successful fetch is the instruction of the counter's index. -/
theorem LeanIsaProgram.fetch_eq_some_iff (prog : LeanIsaProgram) {pc : K} {ins :
    LeanIsaInstruction} :
    prog.fetch pc = some ins ↔ ∃ i : Fin (2 ^ prog.logSize), pc = addressOfIndex i ∧
        prog.instructions i = ins := by
  simp only [LeanIsaProgram.fetch, Option.map_eq_some_iff, gLog?_spec prog.logSize_lt]

/-- A fetch fails exactly at the counters that are no power below `2 ^ logSize`. -/
theorem LeanIsaProgram.fetch_eq_none_iff (prog : LeanIsaProgram) {pc : K} :
    prog.fetch pc = none ↔ ∀ i : Fin (2 ^ prog.logSize), pc ≠ addressOfIndex i := by
  rw [LeanIsaProgram.fetch, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Program counter `0` fetches nothing. -/
theorem LeanIsaProgram.fetch_zero (prog : LeanIsaProgram) : prog.fetch 0 = none := by
  rw [LeanIsaProgram.fetch, gLog?_zero, Option.map_none]

/-! ## Lanes -/

/-- A `K` word is the word of its lane. -/
@[simp] theorem K.ofLane_lane (a : K) : K.ofLane a.lane = a := rfl

/-- A lane is the lane of its word. -/
@[simp] theorem K.lane_ofLane (w : UInt64) : (K.ofLane w).lane = w := rfl

/-- Lanes determine words. -/
theorem K.lane_injective : Function.Injective K.lane := fun a b h ↦ by
  rw [← K.ofLane_lane a, ← K.ofLane_lane b, h]

/-! ## Step -/

/-! ### Load-bearing lemmas -/

/-- A counter that fetches nothing steps nowhere. -/
theorem step_eq_none_of_fetch_eq_none {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ} {r :
    Registers K}
    (h : prog.fetch r.pc = none) : step prog L r = none := by
  rw [step, h]; rfl

/-- A step from a counter that fetches `ins` executes `ins`. -/
theorem step_of_fetch_eq_some {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ} {r : Registers K}
    {ins : LeanIsaInstruction} (h : prog.fetch r.pc = some ins) : step prog L r = execute L r
        ins := by
  rw [step, h]; rfl

/-! ## Execution -/

/-! ### The register sequence of a trace -/

/-- The register sequence `r_0 = (1, 1), r_1, …, r_steps` of a trace; a prefix that fails to
run is dropped, so a valid trace has exactly `steps + 1` entries (`Execution.regs_length`). -/
noncomputable def Execution.regs {prog : LeanIsaProgram} (t : Execution prog) : List
    (Registers K) :=
  (List.range (t.stepCount + 1)).filterMap fun n ↦ run prog t.memory n Registers.initial

/-! ### Load-bearing lemmas -/

section

variable {κ : ℕ} {prog : LeanIsaProgram} {L : MemoryImage κ}

/-- Zero steps go nowhere. -/
@[simp] theorem run_zero (r : Registers K) : run prog L 0 r = some r := rfl

/-- The loop: test for the final state, then fetch, execute, and continue. -/
theorem run_succ (n : ℕ) (r : Registers K) :
    run prog L (n + 1) r = if r = Registers.final prog then none else step prog L r >>= run prog L n :=
  rfl

/-- Away from the final state, a step is taken. -/
theorem run_succ_of_ne_final {r : Registers K} (h : r ≠ Registers.final prog) (n : ℕ) :
    run prog L (n + 1) r = step prog L r >>= run prog L n := by
  rw [run_succ, ite_eq_right h]

/-- Away from the last slot, a step is taken. -/
theorem run_succ_of_ne {r : Registers K} (h : r.pc ≠ prog.pcFinal) (n : ℕ) :
    run prog L (n + 1) r = step prog L r >>= run prog L n :=
  run_succ_of_ne_final (fun hr ↦ h (congrArg Registers.pc hr)) n

/-- In the final state, no step is taken. -/
theorem run_succ_of_eq {r : Registers K} (h : r = Registers.final prog) (n : ℕ) :
    run prog L (n + 1) r = none := by
  rw [run_succ, ite_eq_left h]

/-- Runs compose. -/
theorem run_add (m n : ℕ) (r : Registers K) :
    run prog L (m + n) r = run prog L m r >>= run prog L n := by
  induction m generalizing r with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, run_succ, run_succ]
    split_ifs
    · rfl
    · rw [bind_assoc]
      exact bind_congr fun r' ↦ ih r'

/-- A run of `m + n` steps passes through the registers after `m`. -/
theorem run_prefix {m n : ℕ} {r r'' : Registers K} (h : run prog L (m + n) r = some r'') :
    ∃ r', run prog L m r = some r' ∧ run prog L n r' = some r'' := by
  rw [run_add] at h
  exact Option.bind_eq_some_iff.mp h

/-- A state that is stepped from is not the final state. -/
theorem ne_final_of_run_succ {n : ℕ} {r r' : Registers K} (h : run prog L (n + 1) r = some r') :
    r ≠ Registers.final prog :=
  fun hr ↦ by rw [run_succ_of_eq hr] at h; exact Option.some_ne_none r' h.symm

/-- Along a run, every state before the last is not the final state: the halting test precedes
every fetch. -/
theorem run_intermediate {n : ℕ} {r r' : Registers K} (h : run prog L n r = some r') {m : ℕ}
    (hm : m < n) : ∃ r₁, run prog L m r = some r₁ ∧ r₁ ≠ Registers.final prog := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  obtain ⟨r₁, h₁, h₂⟩ := run_prefix h
  exact ⟨r₁, h₁, ne_final_of_run_succ h₂⟩

end

/-- A trace that runs has `steps + 1` register states. -/
theorem Execution.regs_length {prog : LeanIsaProgram} {t : Execution prog} {r : Registers K}
    (h : run prog t.memory t.stepCount Registers.initial = some r) : t.regs.length = t.stepCount +
        1 := by
  rw [Execution.regs]
  refine (List.filterMap_length_eq_length.mpr ?_).trans List.length_range
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hn) with hlt | rfl
  · obtain ⟨r₁, h₁, -⟩ := run_intermediate h hlt
    simp [h₁]
  · simp [h]

end
end LeanVM.Semantics
