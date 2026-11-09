/-
  LeanVM.Guest.B1.Whir.QueriesOpen

  A level's queries, from `opening_queries`' meaning: the openings the Spec reads, each passing
  `openOne`, and the queries' sum the Spec's `enforcedSum`.
-/

module

public import LeanVM.Guest.B1.Whir.QueryBits
public import LeanVM.Guest.B1.Merkle.Climb
public import LeanVM.Guest.B1.Opening.QueriesRun
public import LeanVM.Protocol.WithHash

/-!
# The queries' openings and sum (TRIAGE G #39, #40)

`queries_open`: `opening_queries`' meaning (B1-a's `MeaningOpeningQueries`) over a cap the cap check
holds (`MeaningVerifyMerkleCap`) with the level's root, at positions whose bits the decodes wrote
(`positions_of_decodes`), gives the Spec's openings (`⟨row, below-cap siblings ++ cap siblings⟩`,
each passing `openOne`, `query_openOne`) and the queries' sum is `enforcedSum` of their rows
(`oqChain_powers`, `enforcedSum_eq`), the rows read as the Spec reads them (`specRow`) when a
row's `rowDot` with the weights at `wp` is its `dot` with `eqKernel` of the level's folds.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- Two positions below `2^d` with the same `d` bits are equal. -/
theorem eq_of_bits {a b d : ℕ} (ha : a < 2 ^ d) (hb : b < 2 ^ d)
    (h : ∀ l < d, a.testBit l = b.testBit l) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro l
  rcases Nat.lt_or_ge l d with hl | hl
  · exact h l hl
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hl)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hl))]

/-- Choices below `n` as a list (any type). -/
theorem exists_list_of_forall' {α : Type} [Inhabited α] {P : ℕ → α → Prop} {n : ℕ}
    (h : ∀ j < n, ∃ v, P j v) : ∃ l : List α, l.length = n ∧ ∀ j (hj : j < l.length), P j l[j] := by
  classical
  refine ⟨(List.range n).map fun j ↦ if hj : j < n then Classical.choose (h j hj) else default,
    by simp, fun j hj ↦ ?_⟩
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range, hj, ↓reduceDIte]
  exact Classical.choose_spec (h j hj)

instance : Inhabited Opening := ⟨⟨0, [], []⟩⟩

end
end LeanVM.Guest.B1.Whir
