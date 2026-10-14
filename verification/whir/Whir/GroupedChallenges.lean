import Whir.CausalGame

/-! Numerical error accounting distinguishes an entire query-vector/adjacent-lambda
message from its coordinates. The estimates below are definitions, not assumed
WHIR escape bounds; a PCS theorem must derive every component from its invariant. -/
namespace Whir.GroupedChallenges
open scoped BigOperators
open Whir.CausalGame Whir.Protocol

structure LevelEstimate where
  listSize : Nat
  mcaNumerator : ℚ
  agreementFraction : ℚ
  deriving Repr

abbrev Estimates (c : Config) := Fin c.folds.size → LevelEstimate

def fieldSize : ℚ := 2 ^ (192 : Nat)

def initialBatch (c : Config) (est : Estimates c) (claims : Nat) : ℚ :=
  if h : 0 < c.folds.size then
    ((claims - 1 : Nat) : ℚ) * (est ⟨0, h⟩).listSize / fieldSize
  else 0

def foldError (c : Config) (est : Estimates c) (i : Fin c.folds.size) : ℚ :=
  (2 * (est i).listSize + (est i).mcaNumerator) / fieldSize

def oodError (c : Config) (est : Estimates c) (i : Fin c.folds.size) : ℚ :=
  if h : i.val + 1 < c.folds.size then
    (oodCount c i : ℚ) * ((est ⟨i.val + 1, h⟩).listSize.choose 2 : ℚ) *
      (remaining c i : ℚ) / fieldSize
  else 0

/-- There is no prover message between these two challenge components. Conditional
query and batching losses add inside a single oracle-query opportunity. -/
def queryBatchError (c : Config) (est : Estimates c) (i : Fin c.folds.size) : ℚ :=
  (est i).agreementFraction ^ c.queries[i.val]! +
  if h : i.val + 1 < c.folds.size then
    ((c.queries[i.val]! + oodCount c i : Nat) : ℚ) *
      (est ⟨i.val + 1, h⟩).listSize / fieldSize
  else (c.queries[i.val]! : ℚ) / fieldSize

/-- No grinding multiplier is deducted from the ideal-interactive errors. -/
def interactiveError (c : Config) (est : Estimates c) (claims : Nat) : ℚ :=
  initialBatch c est claims +
    (∑ i : Fin c.folds.size,
      ((c.folds[i.val]! : ℚ) * foldError c est i + oodError c est i + queryBatchError c est i))
    + (c.logN - c.folds.toList.sum : Nat) * (2 / fieldSize)

/-- The ordinary-soundness ROM budget multiplies the maximum grouped message loss,
not the maximum loss of a coordinate inside a grouped message. -/
def groupedMaximum (c : Config) (est : Estimates c) (claims : Nat) : ℚ :=
  max (initialBatch c est claims) (max (2 / fieldSize)
    ((List.ofFn fun i : Fin c.folds.size =>
      max (foldError c est i) (max (oodError c est i) (queryBatchError c est i))).foldl max 0))

/-- A conservative resource-bound expression. Primitive-mode, authentication and
other external reductions must be stated as their own games and proved reductions. -/
def ordinaryError (vectors : Nat) (eta mode binding auxiliary : ℚ) : ℚ :=
  min 1 ((vectors : ℚ) * eta + mode + binding + auxiliary)

section Counting
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Conditional errors remain charged even if the second bad event depends on the
first challenge. No independence of the two bad events is asserted. -/
theorem grouped_bad_count (badFirst : Finset X) (badSecond : X → Finset Y)
    (bound : Nat) (bounded : ∀ x, (badSecond x).card ≤ bound) :
    (Finset.univ.filter (fun xy : X × Y => xy.1 ∈ badFirst ∨ xy.2 ∈ badSecond xy.1)).card ≤
      badFirst.card * Fintype.card Y + Fintype.card X * bound := by
  classical
  let first : Finset (X × Y) := badFirst ×ˢ Finset.univ
  let second : Finset (X × Y) := Finset.univ.biUnion fun x => ({x} : Finset X) ×ˢ badSecond x
  have subset : (Finset.univ.filter fun xy : X × Y =>
      xy.1 ∈ badFirst ∨ xy.2 ∈ badSecond xy.1) ⊆ first ∪ second := by
    intro xy hxy
    rcases (Finset.mem_filter.mp hxy).2 with h | h
    · exact Finset.mem_union_left _ (by simp [first, h])
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨xy.1, Finset.mem_univ _, Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, h⟩⟩
  calc
    _ ≤ (first ∪ second).card := Finset.card_le_card subset
    _ ≤ first.card + second.card := Finset.card_union_le _ _
    _ ≤ badFirst.card * Fintype.card Y + ∑ x : X, (badSecond x).card := by
      simp only [first, Finset.card_product, Finset.card_univ]
      apply Nat.add_le_add_left
      exact (Finset.card_biUnion_le).trans_eq (by simp)
    _ ≤ _ := by
      apply Nat.add_le_add_left
      have h : (∑ x : X, (badSecond x).card) ≤ ∑ _x : X, bound :=
        Finset.sum_le_sum fun x _ => bounded x
      simpa using h

end Counting
end Whir.GroupedChallenges
