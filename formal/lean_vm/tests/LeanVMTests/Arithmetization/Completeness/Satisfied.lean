import LeanVM.Arithmetization.Completeness.Satisfied
import LeanVMTests.Arithmetization.Completeness.Rows
import LeanVMTests.Arithmetization.Completeness.Fixture

/-!
# Tests: the witness of a list of skeletons satisfies the statement

`skelWitness_satisfiedBy` takes the state balance, the row cap and the public words as hypotheses
and proves the other conjuncts from the construction. The witness of no skeletons has empty
tables, which are within the caps: a table need not be a power of two, the protocol pads it. The
witness of the wrong image is not a witness of the input (`word0_eq`), and a lone skeleton leaves
the state pair unbalanced. The row cap's rejection is the long run of `LongRun`. The `JUMP` table is the one component with
constraints, and its two residuals hold of the honest witnesses and fail for `b = 0` on a nonzero
condition.
-/

namespace LeanVMTests.Arithmetization.Completeness.Satisfied

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open Air.Flat (Component)
open LeanVMTests.Arithmetization.Completeness.Fixture
open LeanVMTests.Arithmetization.Completeness.Rows

/-- The sentinel counter of a `2^11`-slot program, as a literal term, as in `Fixture`. -/
local notation "d₀" => (gpow 2047 : K)

/-! ## The `JUMP` constraints -/

/-- The honest witnesses of a taken jump satisfy the table's constraints. -/
example (data : ProverData K) :
    (⟨jumpTable⟩ : Component K).operations.ConstraintsHold
      (Environment.fromArray (jumpRaw takenRow 1 1) data) :=
  jumpRaw_constraints _ _ _ (by simp [takenRow, CharTwo.add_self_eq_zero])
    (by simp [takenRow, CharTwo.add_self_eq_zero]) data

/-- `b = 0` for a nonzero condition violates the second residual `v_cond · (b + 1) = 0`: the
constraints reject the witness that would push the fall-through for a taken jump. -/
example (w : K) (data : ProverData K) :
    ¬ (⟨jumpTable⟩ : Component K).operations.ConstraintsHold
      (Environment.fromArray (jumpRaw takenRow w 0) data) := by
  rw [jumpRaw_constraints_iff]
  rintro ⟨-, h⟩
  simp [takenRow] at h

/-! ## What the witness satisfies -/

/-- The witness of no skeletons has empty tables, and they are within the caps: no table needs a
power-of-two height, nor the `BLAKE2S` table eight rows. -/
theorem empty_witness_caps (img : MemImage minLogMem) :
    Caps (skelWitness jumpProg badInput img []) :=
  skelWitness_caps jumpProg badInput img [] le_rfl (by decide) fun _ ↦ Nat.zero_le _

/-- Its `XOR` table is empty. -/
example (img : MemImage minLogMem) :
    (opTable img (imageData img) (skelRows img []) .xor).table.length = 0 := rfl

/-- The witness of the all-zero image is not a witness of the input whose first word is `y`: the
first public word is read from the image the data names, and the all-zero image holds `0` there. -/
theorem zero_image_not_satisfied (S : List Skel) :
    ¬ SatisfiedBy jumpProg badInput (skelWitness jumpProg badInput zeroImage S) := by
  intro h
  have hw := h.word0_eq
  change (imageOf (imageData zeroImage)).2.read (gpow 0) = some badInput.word0 at hw
  rw [imageOf_imageData _ (by decide)] at hw
  have h0 : zeroImage.read (gpow 0) = some 0 := read_lit zeroImage 0
  have := h0.symm.trans hw
  have h1 := congrArg (fun e : Option E ↦ e.map (·.limb 1)) this
  simp [badInput, PublicInput.word0, limb_zero] at h1

/-- The state pair does not balance on its own: a single skeleton stepping from `(g^5, 1)` pushes
a state nobody pulls. `skelWitness_satisfiedBy` takes the balance as a hypothesis, and the run's
rotation with the boundary is what discharges it (`Completeness.Theorem`). -/
theorem lone_skeleton_state_unbalanced :
    ¬ (#[1, 1] :: ([(⟨gpow 5, 1, .xor (gpow 0) (gpow 0) (gpow 0)⟩ : Skel)].map fun sk ↦
        #[(nextOf zeroImage sk).pc, (nextOf zeroImage sk).fp])).Perm
      (#[jumpProg.finalPc, 1] :: ([(⟨gpow 5, 1, .xor (gpow 0) (gpow 0) (gpow 0)⟩ : Skel)].map
        fun sk ↦ #[sk.pc, sk.fp])) := by
  intro h
  have hmem : (#[1, 1] : Array K) ∈ (#[jumpProg.finalPc, 1] ::
      ([(⟨gpow 5, 1, .xor (gpow 0) (gpow 0) (gpow 0)⟩ : Skel)].map fun sk ↦ #[sk.pc, sk.fp])) :=
    h.mem_iff.mp List.mem_cons_self
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hfin : jumpProg.finalPc = d₀ := by
    unfold Program.finalPc
    rw [show 2 ^ jumpProg.logSize - 1 = 2047 by decide]
  rcases hmem with h1 | h1
  · have h4 := congrArg Array.toList h1
    simp only [List.cons.injEq] at h4
    rw [hfin] at h4
    exact d₀_ne_one h4.1.symm
  · have h4 := congrArg Array.toList h1
    simp only [List.cons.injEq] at h4
    exact absurd h4.1 (by decide +kernel)

end LeanVMTests.Arithmetization.Completeness.Satisfied
