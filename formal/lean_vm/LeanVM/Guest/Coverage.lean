/-
  LeanVM.Guest.Coverage

  The coverage table as an honest run lays it out (`coveragePlan`, its slots `planSlots`), and
  what the deployed limits (`DeployedLimits`) give of the claims' multiplicities and the
  children's lists.
-/

module

public import Statement.LeanVmGuestCompleteness

/-!
# The coverage plan

The guest program (`G:N`, lines of `crates/rec_aggregation/guests/lean_ethereum.py` at the pin)
writes every claim a node makes, its raw signatures' then its children's, into a slot of its
scheme's region of the coverage table: the declared claims' slots, then duplicate slots
(G:4182-4188, 4206-4220, 4538-4539, 4543-4544). An honest run takes, for each claim in order, its declared
slot if free, else the next duplicate slot (`takeSlot`, `coveragePlan`); the table's slots are
`planSlots`, under `DeployedLimits` the number of claims made (`coverageSlots`, `B1/Main/Plan.lean`'s
`planSlots_eq`).

What `DeployedLimits` gives here: each declared claim's count at most its count among the claims
made (`DeployedLimits.xmssClaimsHeldWithMultiplicity`, `sphincsClaimsHeldWithMultiplicity`, of
the sub-multiset). Every child's lists below `2^23` is `GuestLimits.childClaimListsBelow2Pow23`
(`Limits.lean`), under the coverage table's bound.
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Protocol LeanVM.Node

/-- **The coverage table's slots** (`n_total`, G:4715): one for each raw signature and each entry
of a child's signature lists, every slot written once (G:4749-4754: the writes G:4774, 4779, 4364,
4229, counted by `written`, G:4798-4799, 4824-4825). -/
def coverageSlots (witness : NodeWitness) : ℕ :=
  witness.xmssSignatures.length + witness.sphincsSignatures.length +
    (witness.children.map fun child ↦
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length).sum

namespace Coverage

/-- A claim takes its declared slot if it is free, else the next duplicate slot (`take_slot`).
The state is which declared slots are taken, and the duplicates so far. -/
def takeSlot {α : Type} [BEq α] (declared : List α) (slotState : List Bool × List α) (claim : α) :
    ℕ × (List Bool × List α) :=
  match (List.range declared.length).find? fun j ↦
      declared[j]? == some claim && !(slotState.1.getD j true) with
  | some j => (j, (slotState.1.set j true, slotState.2))
  | none => (declared.length + slotState.2.length, (slotState.1, slotState.2 ++ [claim]))

/-- The slots of claims taken in order. -/
def takeSlots {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List α → List ℕ × (List Bool × List α)
  | slotState, [] => ([], slotState)
  | slotState, claim :: claims =>
    let (slot, slotState) := takeSlot declared slotState claim
    let (slots, slotState) := takeSlots declared slotState claims
    (slot :: slots, slotState)

/-- The slots of lists of claims taken in order. -/
def takeSlotsAll {α : Type} [BEq α] (declared : List α) :
    List Bool × List α → List (List α) → List (List ℕ) × (List Bool × List α)
  | slotState, [] => ([], slotState)
  | slotState, claims :: claimLists =>
    let (slots, slotState) := takeSlots declared slotState claims
    let (slotLists, slotState) := takeSlotsAll declared slotState claimLists
    (slots :: slotLists, slotState)

/-- One region of the coverage table: its duplicate claims, in slot order, and the slot of every
raw claim and of every child's claims. -/
structure CoverageRegion (α : Type) where
  /-- The duplicate claims, in slot order. -/
  duplicates : List α
  /-- The slot of each raw signature's claim. -/
  directSlots : List ℕ
  /-- The slots of each child's claims. -/
  childSlots : List (List ℕ)

/-- The region of the declared claims: the raw claims take their slots, then the children's. -/
def coveragePlan {α : Type} [BEq α] (declared raw : List α) (children : List (List α)) :
    CoverageRegion α :=
  let (raw, slotState) := takeSlots declared (declared.map fun _ ↦ false, []) raw
  let (children, slotState) := takeSlotsAll declared slotState children
  ⟨slotState.2, raw, children⟩

/-- **The coverage table's slots as an honest run lays them out** (`n_total`, G:4715): each
region's declared claims and its duplicates, as `coveragePlan` assigns them. Under
`DeployedLimits`, `coverageSlots` (`B1/Main/Plan.lean`'s `planSlots_eq`). -/
def planSlots (statement : NodeStatement) (witness : NodeWitness) : ℕ :=
  let claims := statement.claims
  let children := witness.children
  claims.xmss.length + (coveragePlan claims.xmss (witness.xmssSignatures.map (·.1))
      (children.map (·.statement.claims.xmss))).duplicates.length +
    claims.sphincs.length + (coveragePlan claims.sphincs (witness.sphincsSignatures.map (·.1))
      (children.map (·.statement.claims.sphincs))).duplicates.length

end Coverage

namespace DeployedLimits

variable {statement : NodeStatement} {witness : NodeWitness}

/-- A leanXMSS claim declared `n` times is made at least `n` times, by raw signatures or in the
children's lists. -/
theorem xmssClaimsHeldWithMultiplicity (limits : DeployedLimits statement witness) :
    ∀ x, statement.claims.xmss.count x ≤ (witness.xmssSignatures.map (·.1)).count x +
      (witness.children.map fun child ↦ child.statement.claims.xmss.count x).sum := by
  intro x
  have h := limits.claimsHeldWithMultiplicity.1.count_le x
  simpa [List.count_append, List.count_flatten, Function.comp_def] using h

/-- Likewise for the leanSPHINCS claims. -/
theorem sphincsClaimsHeldWithMultiplicity (limits : DeployedLimits statement witness) :
    ∀ x, statement.claims.sphincs.count x ≤ (witness.sphincsSignatures.map (·.1)).count x +
      (witness.children.map fun child ↦ child.statement.claims.sphincs.count x).sum := by
  intro x
  have h := limits.claimsHeldWithMultiplicity.2.count_le x
  simpa [List.count_append, List.count_flatten, Function.comp_def] using h

end DeployedLimits

end LeanVM.Guest
