/-
  LeanVM.Semantics.Lemmas

  The lemmas about the definitions of `LeanVM.Spec.Isa`: addressing, fetching, the step, and the
  execution loop.
-/

module

public import LeanVM.Spec.Isa
public import LeanVM.Parameters.Isa

/-!
# Lemmas about leanISA

The load-bearing lemmas of `LeanVM.Semantics`, by section: the memory reader, the program's
fetch, the BLAKE2s cell encoding, the step, and the execution loop (`run`), with the register
sequence of a trace (`Trace.regs`).
-/

namespace LeanVM.Semantics

open LeanVM.Parameters

@[expose] public section

/-! ## Addressing -/

/-- The specification of `gLog?`: on an address space of at most `2 ^ 63` cells, so that
`2 ^ κ ≤ orderOf g`, `gLog? κ a = some i` exactly when `a = g ^ i`. -/
theorem gLog?_spec {κ : ℕ} (hκ : κ < 64) {a : K} {i : Fin (2 ^ κ)} :
    gLog? κ a = some i ↔ a = gpow i := by
  unfold gLog?
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

/-- `gLog?` fails exactly on the addresses that are no power below `2 ^ κ`; no size bound is
needed. -/
theorem gLog?_eq_none_iff {κ : ℕ} {a : K} :
    gLog? κ a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ gpow i := by
  unfold gLog?
  split_ifs with h
  · exact ⟨fun hn ↦ (nomatch hn), fun hn ↦ absurd h (not_exists.mpr hn)⟩
  · exact ⟨fun _ ↦ not_exists.mp h, fun _ ↦ rfl⟩

/-- `0` is never an address, whatever the size. -/
theorem gLog?_zero (κ : ℕ) : gLog? κ 0 = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ gpow_ne_zero i h.symm

/-- A power past the end is no address: `g ^ j` with `2 ^ κ ≤ j < orderOf g` has no index. -/
theorem gLog?_gpow_eq_none {κ j : ℕ} (hj : 2 ^ κ ≤ j) (hj' : j < 2 ^ 64 - 1) :
    gLog? κ (gpow j) = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ by
    have hi : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have := gpow_injOn hj' hi h
    have := i.isLt
    omega

/-! ## Readers and decision procedures -/

/-- The limbs of the word at `a`, zero when there is none: `read`, as a row's three-limb column
(the arithmetization's row builders); specified by `ofLimbs_limbsAt`. -/
noncomputable def MemImage.limbsAt {κ : ℕ} (L : MemImage κ) (a : K) : Vector K 3 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1, v.limb 2]
  | none => #v[0, 0, 0]

/-- The two limbs of the word at `a`, zero when there is none: `read`, as a `BLAKE2S` row's cell
column; specified by `ofCell_cellAt`. -/
noncomputable def MemImage.cellAt {κ : ℕ} (L : MemImage κ) (a : K) : Vector K 2 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-- Register equality is decided field by field. Not derived: the derived instance decides the
second field under `h ▸` for the first, whose `Eq.rec` makes the kernel compare two register
values by definitional unfolding instead of evaluation, and `g * 1 = g ^ 1` then never
decides. -/
instance {F : Type} [DecidableEq F] : DecidableEq (Regs F) := fun x y ↦
  decidable_of_iff (x.pc = y.pc ∧ x.fp = y.fp) (by cases x; cases y; simp)

/-- Sentinel safety is checked from the last typed instruction, without an address search. -/
instance (prog : Program) : Decidable (SentinelSafe prog) :=
  inferInstanceAs (Decidable (_ ≠ Opcode.jump))

/-! ## Memory -/

/-! ### Load-bearing lemmas -/

/-- Reading at the address of index `i` gives word `i`. -/
theorem MemImage.read_gpow {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) (i : Fin (2 ^ κ)) :
    L.read (gpow i) = some (L i) := by
  rw [MemImage.read, (gLog?_spec hκ).mpr rfl, Option.map_some]

/-- A successful read is the word of the address's index. -/
theorem MemImage.read_eq_some_iff {κ : ℕ} (hκ : κ < 64) (L : MemImage κ) {a : K} {v : E} :
    L.read a = some v ↔ ∃ i : Fin (2 ^ κ), a = gpow i ∧ L i = v := by
  simp only [MemImage.read, Option.map_eq_some_iff, gLog?_spec hκ]

/-- A read fails exactly at the addresses that are no power below `2 ^ κ`. -/
theorem MemImage.read_eq_none_iff {κ : ℕ} (L : MemImage κ) {a : K} :
    L.read a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ gpow i := by
  rw [MemImage.read, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Address `0` reads nothing. -/
theorem MemImage.read_zero {κ : ℕ} (L : MemImage κ) : L.read 0 = none := by
  rw [MemImage.read, gLog?_zero, Option.map_none]

/-- The limbs read back at an address that holds a word form that word. -/
theorem MemImage.ofLimbs_limbsAt {κ : ℕ} {L : MemImage κ} {a : K} {v : E}
    (h : L.read a = some v) :
    E.ofLimbs (L.limbsAt a)[0] (L.limbsAt a)[1] (L.limbsAt a)[2] = v := by
  unfold MemImage.limbsAt
  rw [h]
  exact ofLimbs_limb v

/-- The low limb read back at an address that holds a word is the word's. -/
theorem MemImage.limbsAt_getElem_zero {κ : ℕ} {L : MemImage κ} {a : K} {v : E}
    (h : L.read a = some v) : (L.limbsAt a)[0] = v.limb 0 := by
  unfold MemImage.limbsAt
  rw [h]
  rfl

/-- The two limbs read back at an address that holds a canonical word form that word. -/
theorem MemImage.ofCell_cellAt {κ : ℕ} {L : MemImage κ} {a : K} {v : E}
    (h : L.read a = some v) (hc : IsCanonical128 v) : E.ofCell (L.cellAt a) = v := by
  unfold MemImage.cellAt
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
private theorem Program.logSize_lt (prog : Program) : prog.logSize < 64 :=
  lt_of_le_of_lt prog.logSize_le (by decide)

/-! ### Load-bearing lemmas -/

/-- Fetching at the address of index `i` gives instruction `i`. -/
theorem Program.fetch_gpow (prog : Program) (i : Fin (2 ^ prog.logSize)) :
    prog.fetch (gpow i) = some (prog.code i) := by
  rw [Program.fetch, (gLog?_spec prog.logSize_lt).mpr rfl, Option.map_some]

/-- A successful fetch is the instruction of the counter's index. -/
theorem Program.fetch_eq_some_iff (prog : Program) {pc : K} {ins : Instr} :
    prog.fetch pc = some ins ↔ ∃ i : Fin (2 ^ prog.logSize), pc = gpow i ∧ prog.code i = ins := by
  simp only [Program.fetch, Option.map_eq_some_iff, gLog?_spec prog.logSize_lt]

/-- A fetch fails exactly at the counters that are no power below `2 ^ logSize`. -/
theorem Program.fetch_eq_none_iff (prog : Program) {pc : K} :
    prog.fetch pc = none ↔ ∀ i : Fin (2 ^ prog.logSize), pc ≠ gpow i := by
  rw [Program.fetch, Option.map_eq_none_iff, gLog?_eq_none_iff]

/-- Program counter `0` fetches nothing. -/
theorem Program.fetch_zero (prog : Program) : prog.fetch 0 = none := by
  rw [Program.fetch, gLog?_zero, Option.map_none]

/-! ## Blake2s -/

/-! ### Proof helpers -/

/-- Splitting a `K` element into its two words and joining them again is the identity. -/
private theorem ofWords_lowWord_highWord (a : K) : ofWords (lowWord a) (highWord a) = a := by
  apply BF64.toBitVec_injective
  have := BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (x := a.toBitVec) (start₁ := 0) (len₁ := 32)
    (start₂ := 32) (len₂ := 32) rfl
  simpa [ofWords, lowWord, highWord] using this

/-! ### Load-bearing lemmas -/

/-- Packing the words of a canonical cell gives the cell back. -/
theorem wordsCell_cellWords {x : E} (h : IsCanonical128 x) : wordsCell (cellWords x) = x := by
  have h2 : x.limb 2 = 0 := h
  apply E.ext; intro i
  rw [wordsCell, limb_ofLimbs]
  fin_cases i <;> simp [cellWords, ofWords_lowWord_highWord, h2]

/-! ## Step -/

/-! ### Load-bearing lemmas -/

/-- A counter that fetches nothing steps nowhere. -/
theorem step_eq_none_of_fetch_eq_none {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K}
    (h : prog.fetch r.pc = none) : step prog L r = none := by
  rw [step, h]; rfl

/-- A step from a counter that fetches `ins` executes `ins`. -/
theorem step_of_fetch_eq_some {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K}
    {ins : Instr} (h : prog.fetch r.pc = some ins) : step prog L r = execute L r ins := by
  rw [step, h]; rfl

/-- A step that fetches `ins` and reaches `next` executes `ins` to `next`: the one join between
a program's step and an instruction's execution. The tables of the arithmetization
are stated over `execute`, program-free as leanVM's are, and `constraintSoundness` composes them
with `Program.fetch` through this lemma. -/
theorem execute_of_step {κ : ℕ} {prog : Program} {L : MemImage κ} {r : Regs K} {ins : Instr}
    {next : Regs K} (hfetch : prog.fetch r.pc = some ins) (hstep : step prog L r = some next) :
    execute L r ins = some next := by
  rwa [step_of_fetch_eq_some hfetch] at hstep

/-! ## Execution -/

/-! ### The register sequence of a trace -/

/-- The register sequence `r_0 = (1, 1), r_1, …, r_steps` of a trace; a prefix that fails to
run is dropped, so a valid trace has exactly `steps + 1` entries (`Trace.regs_length`). -/
noncomputable def Trace.regs {prog : Program} (t : Trace prog) : List (Regs K) :=
  (List.range (t.steps + 1)).filterMap fun n ↦ run prog t.image n Regs.initial

/-! ### Load-bearing lemmas -/

section

variable {κ : ℕ} {prog : Program} {L : MemImage κ}

/-- Zero steps go nowhere. -/
@[simp] theorem run_zero (r : Regs K) : run prog L 0 r = some r := rfl

/-- The loop: test for the sentinel, then fetch, execute, and continue. -/
theorem run_succ (n : ℕ) (r : Regs K) :
    run prog L (n + 1) r = if r.pc = prog.finalPc then none else step prog L r >>= run prog L n :=
  rfl

/-- Away from the sentinel, a step is taken. -/
theorem run_succ_of_ne {r : Regs K} (h : r.pc ≠ prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = step prog L r >>= run prog L n := by
  rw [run_succ, ite_eq_right h]

/-- At the sentinel, no step is taken. -/
theorem run_succ_of_eq {r : Regs K} (h : r.pc = prog.finalPc) (n : ℕ) :
    run prog L (n + 1) r = none := by
  rw [run_succ, ite_eq_left h]

/-- Runs compose. -/
theorem run_add (m n : ℕ) (r : Regs K) :
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
theorem run_prefix {m n : ℕ} {r r'' : Regs K} (h : run prog L (m + n) r = some r'') :
    ∃ r', run prog L m r = some r' ∧ run prog L n r' = some r'' := by
  rw [run_add] at h
  exact Option.bind_eq_some_iff.mp h

/-- A state that is stepped from is not at the sentinel. -/
theorem pc_ne_finalPc_of_run_succ {n : ℕ} {r r' : Regs K} (h : run prog L (n + 1) r = some r') :
    r.pc ≠ prog.finalPc :=
  fun hpc ↦ by rw [run_succ_of_eq hpc] at h; exact Option.some_ne_none r' h.symm

/-- Along a run, every state before the last is away from the sentinel: the halting test
precedes every fetch. -/
theorem run_intermediate {n : ℕ} {r r' : Regs K} (h : run prog L n r = some r') {m : ℕ}
    (hm : m < n) : ∃ r₁, run prog L m r = some r₁ ∧ r₁.pc ≠ prog.finalPc := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (k + 1) := ⟨n - m - 1, by omega⟩
  obtain ⟨r₁, h₁, h₂⟩ := run_prefix h
  exact ⟨r₁, h₁, pc_ne_finalPc_of_run_succ h₂⟩

end

/-- A trace that runs has `steps + 1` register states. -/
theorem Trace.regs_length {prog : Program} {t : Trace prog} {r : Regs K}
    (h : run prog t.image t.steps Regs.initial = some r) : t.regs.length = t.steps + 1 := by
  rw [Trace.regs]
  refine (List.filterMap_length_eq_length.mpr ?_).trans List.length_range
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp (List.mem_range.mp hn) with hlt | rfl
  · obtain ⟨r₁, h₁, -⟩ := run_intermediate h hlt
    simp [h₁]
  · simp [h]

end
end LeanVM.Semantics
