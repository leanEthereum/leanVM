/-
  LeanVM.Protocol.Spine.Slots

  The slot of every phase on ArkLib's typed framework, with the error charged to each of its
  challenges, as closed forms of the instance, their bounds along every path, and the question
  the protocol asks the stack at the end.
-/

module

public import LeanVM.Protocol.Spine.Errors
public import LeanVM.Protocol.Spine.Seams
public import LeanVM.Protocol.ToArkLib.Typed.Commit
public import LeanVM.Protocol.ToArkLib.Typed.Schedule

/-!
# Typed slots and errors

Each phase's typed component is at the slot written here (the slot is part of its type), and its
security at the errors written here, the numbers `Spine/Errors.lean` charges the same challenges:

* the bus (`busSlot`, `busErrors`): `(α, β)` at `4·2^{μ_bus}/|E|`, the roots at no error, the
  grand-product argument at its errors from the unit `1/|E|`, the boundary values at no error;
* the table sumcheck (`tableSlot`, `tableErrors`): `ξ` at `(B + 2)/|E|`, the `τ_max` rounds of
  degree `3` at `3/|E|` each, the final values at no error;
* the public input (`pubSlot`, `pubErrors`): the challenge `r` at `1/|E|`, then the values of
  the lines marked `sent`;
* Flock (`flockPhaseSlot`, `flockErrors`): Flock's challenges at the errors listed there, or
  nothing without a Flock region;
* the opening (`openingSlot`, `openingErrors`): the batching challenge `λ` at `(J - 1)/|E|`, `J`
  the number of pooled claims.

The protocol ends with one question to the stack (`stackQuestion`): the final weighted claim's
weight, accepted when the answer is the claim's value. `Seam.opened` is what the opening must
reach for the question to pass: the final claim holds of the stack.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters Interaction Interaction.Oracle Typed
open scoped NNReal

@[expose] public section

variable (I : M3Instance)

/-! ## The bus -/

/-- The bus phase's slot: the fingerprint challenges `(α, β)`, the two roots, the grand-product
argument for the three trees, then the boundary columns' values. -/
abbrev busSlot : Slot :=
  (((drawSlot ((Fin 4 → E) × E)).append (saySlot (E × E))).append (gkrSlot E 3 I.μBus)).append
    (saySlot (Vector E I.busClaims))

/-- The bus phase's errors: `4·2^{μ_bus}` on `(α, β)`, then the grand-product argument's at the
unit `1/|E|`. -/
noncomputable abbrev busErrors : Errors (busSlot I).tree (busSlot I).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append (drawSlot ((Fin 4 → E) × E)).tree
    (drawSlot ((Fin 4 → E) × E)).roles (drawErrors _ (overE (4 * 2 ^ I.μBus))) (sayErrors _))
    (gkrErrors E (overE 1) 3 I.μBus)) (sayErrors _)

/-! ## The table sumcheck -/

/-- The table sumcheck's slot: the batching challenge `ξ`, one cubic round per variable, then one
value per column of each sumcheck table. -/
abbrev tableSlot : Slot :=
  ((drawSlot E).append (roundsSlot E 3 I.τmax)).append (saySlot (Vector E I.tableColumns))

/-- The table sumcheck's errors: `B + 2` on `ξ`, `3` per round. -/
noncomputable abbrev tableErrors : Errors (tableSlot I).tree (tableSlot I).roles :=
  Errors.append _ _ (Errors.append _ _ (drawErrors E (overE (I.B + 2))) (roundsErrors E 3 (overE 3)
    I.τmax)) (sayErrors _)

/-! ## The public input -/

/-- The public-input phase's tree: the challenge, then the values sent. -/
abbrev pubTree : Oracle.TypeTree.{0} := .public E fun _ ↦ .public (List E) fun _ ↦ .done

/-- The verifier draws the challenge, the prover sends the values. -/
abbrev pubRoles : pubTree.RoleDecoration := ⟨.receiver, fun _ ↦ ⟨.sender, fun _ ↦ ⟨⟩⟩⟩

/-- The public-input phase's slot: the challenge drawn uniformly, then the values sent. -/
abbrev pubSlot : Slot :=
  ⟨pubTree, pubRoles, ⟨PUnit.unit, fun _ ↦ ⟨PUnit.unit, fun _ ↦ ⟨⟩⟩⟩, ($ᵗ E, fun _ _ ↦ PUnit.unit)⟩

/-- The public-input phase's error: `1/|E|` at the challenge. -/
noncomputable abbrev pubErrors : Errors pubSlot.tree pubSlot.roles :=
  (overE 1, fun _ _ ↦ PUnit.unit)

/-! ## Flock -/

/-- The Flock phase's slot for `2 ^ k` compressions: the `k + 1` coordinates of the point, the 64
values, `z_skip`, `8 + k` zerocheck rounds, the two values `v_a, v_b`, `α_lc`, 8 lincheck
rounds, the 64 values, and the six ring-switching challenges. -/
abbrev flockSlotOf (k : ℕ) : Slot :=
  (((((((((drawsSlot E (k + 1)).append (saySlot (Vector E 64))).append (drawSlot E)).append
    (roundsSlot E 2 8)).append (roundsSlot E 2 k)).append (saySlot (Vector E 2))).append
    (drawSlot E)).append (roundsSlot E 2 8)).append (saySlot (Vector E 64))).append
    (drawsSlot E 6)

/-- The ring-switching challenges' errors: `2^{2^{5−p}−1}` over `|E|` on the `p`-th, that is
`2^31, 2^15, 2^7, 8, 2, 1`. -/
noncomputable abbrev ringErrors : Errors (drawsSlot E 6).tree (drawsSlot E 6).roles :=
  drawsErrorsOf E (fun p ↦ overE (2 ^ (2 ^ (5 - p) - 1))) 6

/-- The Flock phase's errors for `2 ^ k` compressions: `1` on each coordinate of the point, `127`
on `z_skip`, `2` on each within-block and lincheck round, `3` on each batch round and on `α_lc`,
and the ring-switching challenges'. -/
noncomputable abbrev flockErrorsOf (k : ℕ) : Errors (flockSlotOf k).tree (flockSlotOf k).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _
    (Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append _ _
    (drawsErrors E (overE 1) (k + 1)) (sayErrors _)) (drawErrors E (overE 127)))
    (roundsErrors E 2 (overE 2) 8)) (roundsErrors E 2 (overE 3) k)) (sayErrors _))
    (drawErrors E (overE 3))) (roundsErrors E 2 (overE 2) 8)) (sayErrors _)) ringErrors

/-- The Flock slot: the Flock phase for the region's compressions, or nothing. -/
def flockSlotOpt : Option (FlockRegion I.toShape) → Slot
  | none => doneSlot
  | some r => flockSlotOf r.kBatch

/-- The Flock phase's errors on the slot of a region or of none. -/
noncomputable def flockErrorsOpt :
    (o : Option (FlockRegion I.toShape)) → Errors (flockSlotOpt I o).tree (flockSlotOpt I o).roles
  | none => doneErrors
  | some r => flockErrorsOf r.kBatch

/-- The Flock phase's slot. -/
abbrev flockPhaseSlot : Slot := flockSlotOpt I I.flock

/-- The Flock phase's errors. -/
noncomputable abbrev flockErrors : Errors (flockPhaseSlot I).tree (flockPhaseSlot I).roles :=
  flockErrorsOpt I I.flock

/-! ## The opening -/

/-- The opening's slot: the batching challenge `λ`; the one question to the stack is no move. -/
abbrev openingSlot : Slot := drawSlot E

/-- The opening's error: `J − 1` on `λ`, `J` the number of pooled claims. -/
noncomputable abbrev openingErrors : Errors openingSlot.tree openingSlot.roles :=
  drawErrors E (overE (I.poolSize - 1))

/-! ## Each slot's errors along a path -/

/-- The bus phase's errors sum to at most `(4·2^{μ_bus} + (μ_bus + 1)·2 + 2μ_bus² + 3μ_bus + 3)/|E|`
along every path. -/
theorem busErrors_bounded : Errors.Bounded (busSlot I).tree (busSlot I).roles (busErrors I)
    (overE (4 * 2 ^ I.μBus + ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus + 3 * I.μBus + 3))) :=
  ((((drawErrors_bounded _ _).append (sayErrors_bounded _)).append
    (gkrErrors_bounded E (overE 1) 3 I.μBus)).append (sayErrors_bounded _)).mono
    (le_of_eq (by rw [nat_mul_overE, add_zero, add_zero, mul_one, ← overE_add]))

/-- The table sumcheck's errors sum to `(B + 2)/|E| + τ_max · 3/|E|` along every path. -/
theorem tableErrors_bounded : Errors.Bounded (tableSlot I).tree (tableSlot I).roles
    (tableErrors I) (overE (I.B + 2) + I.τmax * overE 3) :=
  (((drawErrors_bounded _ _).append (roundsErrors_bounded E 3 _ I.τmax)).append
    (sayErrors_bounded _)).mono (add_zero _).le

/-- The public-input phase's error sums to `1/|E|`. -/
theorem pubErrors_bounded : Errors.Bounded pubSlot.tree pubSlot.roles pubErrors (overE 1) :=
  fun _ ↦ le_of_eq (add_zero _)

/-- The ring-switching challenges' errors sum to `(2^31 + 2^15 + 2^7 + 8 + 2 + 1)/|E|`. -/
theorem ringErrors_bounded : Errors.Bounded (drawsSlot E 6).tree (drawsSlot E 6).roles ringErrors
    (overE (2 ^ 31 + 2 ^ 15 + 2 ^ 7 + 8 + 2 + 1)) :=
  (drawsErrorsOf_bounded E _ 6).mono (le_of_eq (by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← overE_add]
    norm_num))

/-- The Flock phase's errors for `2 ^ k` compressions sum to `(4k + 302 + 2^31 + 2^15)/|E|`. -/
theorem flockErrorsOf_bounded (k : ℕ) :
    Errors.Bounded (flockSlotOf k).tree (flockSlotOf k).roles (flockErrorsOf k)
      (overE (4 * k + 302 + 2 ^ 31 + 2 ^ 15)) :=
  (((((((((drawsErrors_bounded E _ (k + 1)).append (sayErrors_bounded _)).append
    (drawErrors_bounded _ _)).append (roundsErrors_bounded E 2 _ 8)).append
    (roundsErrors_bounded E 2 _ k)).append (sayErrors_bounded _)).append
    (drawErrors_bounded _ _)).append (roundsErrors_bounded E 2 _ 8)).append
    (sayErrors_bounded _)).append ringErrors_bounded |>.mono (le_of_eq (by
      simp only [add_zero, nat_mul_overE, ← overE_add]
      congr 1
      omega))

/-- The Flock phase's errors, with at most `2^32` compressions, sum to at most
`(4·32 + 302 + 2^31 + 2^15)/|E|`. -/
theorem flockErrors_bounded (hk : ∀ r ∈ I.flock, r.kBatch ≤ 32) :
    Errors.Bounded (flockPhaseSlot I).tree (flockPhaseSlot I).roles (flockErrors I)
      (overE (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15)) := by
  unfold flockPhaseSlot flockErrors
  generalize hf : I.flock = f at hk
  cases f with
  | none => exact doneErrors_bounded.mono zero_le
  | some r =>
    exact (flockErrorsOf_bounded r.kBatch).mono (overE_mono (by have := hk r rfl; omega))

/-- The opening's error sums to `(J − 1)/|E|`. -/
theorem openingErrors_bounded :
    Errors.Bounded openingSlot.tree openingSlot.roles (openingErrors I) (overE (I.poolSize - 1)) :=
  drawErrors_bounded _ _

/-! ## The question to the stack -/

/-- The check on the stack's answer to a claim's weight: the answer is the claim's value. -/
def stackCheck (c : WeightedClaim I) (a : E) : Bool := decide (a = c.value)

/-- The check is the equality. -/
theorem stackCheck_iff (c : WeightedClaim I) (a : E) : stackCheck I c a = true ↔ a = c.value :=
  decide_eq_true_iff

/-- The question the protocol asks the stack at the end: the final claim's weight, accepted when
the answer is the claim's value. -/
def stackQuestion : Question (Column I.μ) (WeightedClaim I) Unit where
  query c := c.weight
  check := stackCheck I
  out _ := ()

/-- Before the question: the stack's answer to the final claim is its value, so that the question
passes into `Seam.done`. -/
def Seam.opened : Set ((WeightedClaim I × ∀ i, TheOracle I i) × Unit) :=
  (stackQuestion I).rel (Seam.done I)

/-- The opened seam is the final claim holding of the stack. -/
theorem Seam.opened_iff (c : WeightedClaim I) (o : ∀ i, TheOracle I i) (w : Unit) :
    ((c, o), w) ∈ Seam.opened I ↔ c.Holds (theStack o) :=
  ⟨fun h ↦ (stackCheck_iff I c _).mp h.1, fun h ↦ ⟨(stackCheck_iff I c _).mpr h, trivial⟩⟩

end
end LeanVM.Protocol
