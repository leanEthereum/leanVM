import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rpm

/-!
# Tests: the batching's soundness

* `rounds_sound`, `batch_sound`, `children_sound`, `runProof_batchAny`, `batch_rom`,
  `batch_rom_bits`, and in the random-permutation model `batch_rpm`, `batch_rpm_bits` and the
  transfer they use, `LeanVM.Rpm.detRun_le_rom`, rest on Lean's three standard axioms.
* The random-oracle theorem's seeding is the batching's seed (`FiatShamirState::from_label`), and
  has no hash answer carried by a later hash step (so `failBound` is `5N / 2^256`).
* The count is absorbed as `g^n` and three zeros, a whole rate.
* **The condition doing the work.** `rounds_sound` needs the final claim to be `f` at the
  challenges: with no round, a false first claim (`1`, the cube sum of `0` being `0`) leaves no
  bad round, and it is the final check that fails.
* **The bound is attained.** A round's gap has at most two roots (`quadratic_roots`), and
  `x² + x` has exactly two, `0` and `1`, in characteristic two.
-/

namespace LeanVMTests.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Batch

/-- info: 'LeanVM.Guest.Batch.rounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.rounds_sound

/-- info: 'LeanVM.Guest.Batch.batch_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_sound

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.runProof_batchAny' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.runProof_batchAny

/-- info: 'LeanVM.Guest.Batch.batch_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom

/-- info: 'LeanVM.Guest.Batch.batch_rom_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rom_bits

/-- info: 'LeanVM.Guest.Batch.batch_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm

/-- info: 'LeanVM.Guest.Batch.batch_rpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm_bits

/-- info: 'LeanVM.Rpm.detRun_le_rom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.detRun_le_rom

/-- The seeding, deployed, is `Node.batchSeed`; no hash answer is carried by a later step. -/
example : Id.run (batchSeedOf.run keccak256 keccakF1600) = LeanVM.Node.batchSeed ∧
    batchSeeds.offs = [] :=
  ⟨batchSeedOf_run, rfl⟩

/-- The count is a whole rate: `g^n`, then three zeros. -/
example (n : ℕ) : childCountCells n = [Verifier.gpow n, 0, 0, 0] ∧ (childCountCells n).length = rateScalars :=
  ⟨rfl, rfl⟩

/-- Without rounds, a false first claim leaves no bad round: the final check is what fails. -/
example (sp : Sponge) :
    (1 : E) ≠ cubeSum 0 (fun _ ↦ 0) [] ∧ (¬ ∃ j < 0, BadRound 0 (fun _ ↦ 0) [] 1 sp j) ∧
      (rsRun [] 1 sp).1.2 ≠ (fun _ ↦ (0 : E)) (roundChallenges [] 1 sp) := by
  refine ⟨by simp [cubeSum], by simp, ?_⟩
  simp [rsRun]

/-- `x² + x` has exactly two roots, `0` and `1`. -/
example : {x : E | x ^ 2 + x = 0}.ncard = 2 := by
  have : {x : E | x ^ 2 + x = 0} = {0, 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h' : x * (x + 1) = 0 := by rw [← h]; ring
      rcases mul_eq_zero.mp h' with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by
          have := congrArg (· + 1) h1
          simpa [add_assoc, CharTwo.add_self_eq_zero] using this)
    · rintro (rfl | rfl) <;> simp [CharTwo.add_self_eq_zero]
  rw [this, Set.ncard_pair zero_ne_one]

end LeanVMTests.Guest.Batch
