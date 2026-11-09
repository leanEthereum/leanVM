import LeanVM.Protocol.EndToEnd.Complete.Statement
import LeanVMTests.Arithmetization.Completeness.Fixture
import LeanVM.Protocol.WithHash

/-!
# Completeness within the budget, locked

Statement locks of `LeanVM/Protocol/EndToEnd/Complete/Small.lean`, with their axioms. The budget
`Execution.committedSize ≤ 2^28` holds whenever the former caps do (at most `2^19` steps, `2^23` words
of memory and `2^23` instructions: `committedSize_le_of_caps`), in particular for the one-step
trace of `Completeness.Fixture`. It also holds for a run of `2^20` steps, all `JUMP`s, which the
former caps excluded, so completeness (`Complete.completeness_le`, which `LeanVM.completeness`
restates) applies to it (`longTrace_complete`). The negative case: a `KECCAK` table of more than
`2^21` rows has no admissible sizes, whatever the rest.
-/

namespace LeanVMTests.Protocol.EndToEnd.Complete.Small

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVMTests.Arithmetization.Completeness.Fixture

/-! ## Statement locks -/

section Locks

open LeanVM.Protocol.Verifier

example {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu) :
    ∃ (w : Air.Flat.EnsembleWitness (leanIsaEnsemble prog t.logMemorySize))
      (s : Sizes), SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧
      s.Admissible prog :=
  exists_admissible_witness hv hbudget

example (H : Bytes → Digest) (F : KeccakState → KeccakState) {prog : LeanIsaProgram} {input :
    PublicInput}
    {t : Execution prog} {ρ fuel : ℕ} {proof : Proof}
    (h : honestProofOf H F prog input t ρ fuel = some proof) :
    verifyWithHash (m := Id) H F (bytecodeWords prog) (publicInputDigest input) proof = true :=
  verify_honestProofOf H F h

example {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {ρ : ℕ}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ maxMu)
    (hρ : validRate ρ) (H : Bytes → Digest) (F : KeccakState → KeccakState) (fuel : ℕ)
    (hpow : ∀ hist bits k sp,
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist =
          some (.grind bits k) → findNonce F bits sp fuel ≠ none) :
    (honestProofOf H F prog input t ρ fuel).isSome :=
  honestProofOf_isSome hv hbudget hρ H F fuel hpow

example (prog : LeanIsaProgram) (s : Sizes) : (LeanVM.Protocol.LeanIsa.blocks prog s).total =
    4 * 2 ^ s.logMem + 2 ^ prog.logSize + 2 ^ (s.τ 5 + 6) + 15 * 2 ^ s.τ 0 + 15 * 2 ^ s.τ 1 +
      8 * 2 ^ s.τ 2 + 15 * 2 ^ s.τ 3 + 14 * 2 ^ s.τ 4 + 28 * 2 ^ s.τ 5 :=
  blocks_total_eq prog s

/--
info: 'LeanVM.Protocol.EndToEnd.Complete.exists_admissible_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms exists_admissible_witness

/--
info: 'LeanVM.Protocol.EndToEnd.Complete.verify_honestProofOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms verify_honestProofOf

/--
info: 'LeanVM.Protocol.EndToEnd.Complete.complete_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms complete_of_budget

end Locks

/-! ## The former caps imply the budget -/

/-- A table's height is at most `2^n` when the run has at most `2^n` steps. -/
theorem height_le {prog : LeanIsaProgram} {t : Execution prog} {rf : Registers K} {n : ℕ}
    (h : run prog t.memory t.stepCount Registers.initial = some rf) (hn : t.stepCount ≤ 2 ^ n) (op : Opcode) :
    2 ^ Nat.clog 2 (t.opcodeCount op) ≤ 2 ^ n := by
  refine Nat.pow_le_pow_right (by norm_num) (Nat.clog_le_of_le_pow ?_)
  rw [Execution.count_eq_runRows h]
  exact (Execution.runRows_le_steps h op).trans hn

/-- The `KECCAK` table's height, at least `2^9`, is at most `2^n + 2^9` with at most `2^n`
steps. -/
theorem keccakHeight_le {prog : LeanIsaProgram} {t : Execution prog} {rf : Registers K} {n : ℕ}
    (h : run prog t.memory t.stepCount Registers.initial = some rf) (hn : t.stepCount ≤ 2 ^ n) :
    2 ^ max (Nat.clog 2 (t.opcodeCount .keccak)) 9 ≤ 2 ^ n + 512 := by
  have h5 := height_le h hn .keccak
  rcases le_total (Nat.clog 2 (t.opcodeCount .keccak)) 9 with hle | hle
  · rw [max_eq_right hle]; omega
  · rw [max_eq_left hle]; omega

/-- With at most `2^n` steps, the committed size is at most
`4·2^κ + 2^logSize + 159·2^n + 47104`. -/
theorem committedSize_le {prog : LeanIsaProgram} {t : Execution prog} {rf : Registers K} {n : ℕ}
    (h : run prog t.memory t.stepCount Registers.initial = some rf) (hn : t.stepCount ≤ 2 ^ n) :
    t.committedSize ≤ 4 * 2 ^ t.logMemorySize + 2 ^ prog.logSize + 159 * 2 ^ n + 47104 := by
  have h0 := height_le h hn .xor
  have h1 := height_le h hn .mulNative
  have h2 := height_le h hn .setConstant
  have h3 := height_le h hn .deref
  have h4 := height_le h hn .jump
  have h5 := keccakHeight_le h hn
  simp only [Execution.committedSize]
  omega

/-- **The former caps imply the budget**: at most `2^19` steps, `2^23` words of memory and `2^23`
instructions. -/
theorem committedSize_le_of_caps {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hsteps : t.stepCount ≤ 2 ^ 19) (hmem : t.logMemorySize ≤ 23)
    (hcode : prog.logSize ≤ 23) : t.committedSize ≤ 2 ^ 28 := by
  have := committedSize_le hv.2 hsteps
  have hm : 2 ^ t.logMemorySize ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hmem
  have hc : 2 ^ prog.logSize ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hcode
  omega

/-- The one-step trace of `Completeness.Fixture` is within the budget, -/
theorem badTrace_budget : badTrace.committedSize ≤ 2 ^ maxMu :=
  committedSize_le_of_caps badTrace_valid (by decide) (by decide) (by decide)

/-- and has a witness at admissible sizes. -/
theorem badTrace_admissible :
    ∃ (w : Air.Flat.EnsembleWitness (leanIsaEnsemble jumpProg badTrace.logMemorySize)) (s : Sizes),
      SatisfiedBy jumpProg badInput w ∧ AssignmentRepresents w badTrace ∧
      Sizes.ofWitness w = some s ∧ s.Admissible jumpProg :=
  exists_admissible_witness badTrace_valid badTrace_budget

/-! ## A run of `2^20` steps

`loopProg` has two slots, both `JUMP [g^2, g^2, g^3]`, the second the sentinel. On `loopImage`,
frame `j` (frame pointer `g^(2j)`) holds the condition and destination `1` at word `2j + 2` and
the next frame pointer `g^(2(j + 1))` at word `2j + 3`; the last frame holds the sentinel `g` and
the frame pointer `1`. So the run takes `J = 2^20` steps, all `JUMP`s, on a memory of `2^22`
words. -/

/-- The number of frames, and of steps. -/
def J : ℕ := 2 ^ 20

/-- Two slots, both `JUMP [g^2, g^2, g^3]`. -/
def loopProg : LeanIsaProgram := ⟨1,
    by decide, fun _ ↦ .jump (addressOfIndex 2) (addressOfIndex 2) (addressOfIndex 3)⟩

/-- The public input: zero. -/
def loopInput : PublicInput := ⟨fun _ ↦ 0⟩

/-- The image: the public words, then two words per frame. -/
def loopImage : MemoryImage 22 := fun n ↦
  if (n : ℕ) = 0 then loopInput.word0
  else if (n : ℕ) = 1 then loopInput.word1
  else if (n : ℕ) % 2 = 0 then (if (n : ℕ) / 2 - 1 = J - 1 then ofK g else ofK 1)
  else if (n : ℕ) / 2 - 1 = J - 1 then ofK 1 else ofK (addressOfIndex (2 * ((n : ℕ) / 2)))

/-- The execution: `J` steps on `loopImage`. -/
def longTrace : Execution loopProg := ⟨22, loopImage, J⟩

theorem two_pow_22 : (2 : ℕ) ^ 22 = 4 * J := by norm_num [J]

theorem loopProg_pcFinal : loopProg.pcFinal = g := pow_one g

theorem loopProg_fetch : loopProg.fetch 1 = some (.jump (addressOfIndex 2) (addressOfIndex 2)
    (addressOfIndex 3)) := by
  have h := loopProg.fetch_gpow ⟨0, by decide⟩
  rw [show addressOfIndex 0 = (1 : K) from pow_zero g] at h
  exact h

theorem one_ne_pcFinal : (1 : K) ≠ loopProg.pcFinal := by
  have := gpow_ne_pcFinal loopProg (n := 0) (by decide)
  rwa [show addressOfIndex 0 = (1 : K) from pow_zero g] at this

/-- The frame of `j`'s words, read. -/
theorem read_frame (j : ℕ) (hj : j < J) :
    loopImage.read (addressOfIndex (2 * j) * addressOfIndex 2) =
        some (if j = J - 1 then ofK g else ofK 1) ∧
      loopImage.read (addressOfIndex (2 * j) * addressOfIndex 3) =
        some (if j = J - 1 then ofK 1 else ofK (addressOfIndex (2 * (j + 1)))) := by
  have := two_pow_22
  rw [← pow_add, ← pow_add]
  refine ⟨(MemoryImage.read_gpow (by decide) loopImage ⟨2 * j + 2, by omega⟩).trans ?_,
    (MemoryImage.read_gpow (by decide) loopImage ⟨2 * j + 3, by omega⟩).trans ?_⟩
  · simp [loopImage, show (2 * j + 2) % 2 = 0 by omega]
  · have h2 : (2 * j + 3) / 2 = j + 1 := by omega
    simp [loopImage, h2, show (2 * j + 3) % 2 = 1 by omega]

/-- The `JUMP` of a frame before the last goes to slot `0` in the next frame. -/
theorem step_loop {j : ℕ} (hj : j + 1 < J) :
    run loopProg loopImage 1 ⟨1, addressOfIndex (2 * j)⟩ = some ⟨1, addressOfIndex (2 * (j +
        1))⟩ := by
  obtain ⟨hc, hf⟩ := read_frame j (by omega)
  have hne : j ≠ J - 1 := by omega
  simp only [hne, ↓reduceIte] at hc hf
  refine run_one one_ne_pcFinal ?_
  rw [step_of_fetch_eq_some (r := ⟨1, addressOfIndex (2 * j)⟩) loopProg_fetch]
  exact executeWith_jump_taken (read := loopImage.read) (c := 1) (d := 1) hc hc hf one_ne_zero

/-- The `JUMP` of the last frame goes to the sentinel with frame pointer `1`. -/
theorem step_last :
    run loopProg loopImage 1 ⟨1, addressOfIndex (2 * (J - 1))⟩ = some (Registers.final
        loopProg) := by
  obtain ⟨hc, hf⟩ := read_frame (J - 1) (by unfold J; omega)
  simp only [↓reduceIte] at hc hf
  refine run_one one_ne_pcFinal ?_
  rw [step_of_fetch_eq_some (r := ⟨1, addressOfIndex (2 * (J - 1))⟩) loopProg_fetch,
      Registers.final,
    loopProg_pcFinal]
  exact executeWith_jump_taken (read := loopImage.read) (c := g) (d := g) (f := 1) hc hc hf
    g_ne_zero

theorem run_frames : ∀ m, m < J →
    run loopProg loopImage m Registers.initial = some ⟨1, addressOfIndex (2 * m)⟩ := by
  intro m
  induction m with
  | zero => intro _; simp [Registers.initial, addressOfIndex]
  | succ m ih => intro hm; exact run_trans (ih (by omega)) (step_loop hm)

/-- **The long run is a valid execution.** -/
theorem longTrace_valid : ValidExecution loopProg loopInput longTrace := by
  refine ⟨⟨by decide, by decide, ?_, ?_⟩, ?_⟩
  · exact (MemoryImage.read_gpow (by decide) loopImage ⟨0, by decide⟩).trans (by simp [loopImage])
  · exact (MemoryImage.read_gpow (by decide) loopImage ⟨1, by decide⟩).trans (by simp [loopImage])
  · have h := run_trans (run_frames (J - 1) (by unfold J; omega)) step_last
    rwa [show J - 1 + 1 = J by unfold J; omega] at h

/-- No instruction of `loopProg` but `JUMP` executes. -/
theorem count_eq_zero {op : Opcode} (hop : op ≠ .jump) : longTrace.opcodeCount op = 0 := by
  unfold Execution.opcodeCount
  generalize longTrace.stepCount = n
  generalize Registers.initial = r
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    unfold opcodeCountInRun
    split
    · rename_i ins _ hf _
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp hf
      simp only [show (loopProg.instructions i).opcode = .jump from rfl, Ne.symm hop,
          ↓reduceIte, ih]
    · rfl

/-- The committed size of an execution of `JUMP`s alone. Stated for any trace: on `longTrace` the
kernel would evaluate its counts, a run of `2^20` steps, when comparing the sums. -/
theorem committedSize_le_of_jumps {prog : LeanIsaProgram} (t : Execution prog)
    (h0 : ∀ op, op ≠ .jump → t.opcodeCount op = 0) {a : ℕ} (hj : 2 ^ Nat.clog 2 (t.opcodeCount
        .jump) ≤ a) :
    t.committedSize ≤ 4 * 2 ^ t.logMemorySize + 2 ^ prog.logSize + 14 * a + 47157 := by
  simp only [Execution.committedSize, h0 .xor (by decide), h0 .mulNative (by decide),
    h0 .setConstant (by decide), h0 .deref (by decide), h0 .keccak (by decide),
    Nat.clog_zero_right, pow_zero, show max 0 9 = 9 from rfl]
  omega

/-- **The long run is within the budget**, -/
theorem longTrace_budget : longTrace.committedSize ≤ 2 ^ 28 := by
  refine (committedSize_le_of_jumps longTrace (fun _ ↦ count_eq_zero)
    (height_le longTrace_valid.2 (le_rfl : longTrace.stepCount ≤ 2 ^ 20) .jump)).trans ?_
  rw [show longTrace.logMemorySize = 22 from rfl, show loopProg.logSize = 1 from rfl]
  norm_num

/-- with more than `2^19` steps, -/
example : 2 ^ 19 < longTrace.stepCount := by decide

/-- so completeness covers it. -/
theorem longTrace_complete {ρ fuel : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let z ← LeanVM.experiment (honestProverRom loopProg loopInput longTrace ρ fuel)}[
      z.1.2 = false] ≤ LeanVM.completenessError fuel :=
  completeness_le longTrace_valid longTrace_budget hρ hfuel

/-! ## The negative case -/

/-- **A `KECCAK` table of more than `2^21` rows is inadmissible**, for every program and every
other size: its height is `2^22`, and `q_keccak` alone has `2^28` cells. -/
theorem not_admissible_of_keccak (prog : LeanIsaProgram) (s : Sizes) (h : s.τ 5 = 22) :
    ¬ s.Admissible prog := by
  intro hs
  have hμ := (blocks_fits prog s).trans (Nat.pow_le_pow_right (by norm_num) hs.2.2.2)
  rw [blocks_total_eq, h] at hμ
  have : 0 < 2 ^ s.logMem := Nat.two_pow_pos _
  have : 0 < 2 ^ prog.logSize := Nat.two_pow_pos _
  unfold maxMu at hμ
  omega

end LeanVMTests.Protocol.EndToEnd.Complete.Small
