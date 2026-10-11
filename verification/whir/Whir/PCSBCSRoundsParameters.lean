import Whir.PCSBCSRounds

/-! Exact PCS-only BCS resource parameters from the audited modeled schedule,
not the two-stage ring proof decomposition and not the whole-system transcript. -/
namespace Whir.PCSBCSRounds
open Concrete Protocol CausalGame CausalProbability WHIRHistory
open scoped BigOperators

/-- Joint initial message contributes exactly one. Zero-OOD levels add zero
OOD rounds; every tail scalar, including the response-free last, contributes one. -/
theorem k_exact (c : Config) :
    k c = 1 + (∑ i : Fin c.folds.size, (c.folds[i.val]! + oodCount c i.val + 1)) +
      (c.logN - c.folds.toList.sum) := by
  unfold k
  rw [Fintype.card_congr (Coordinate.proxyTypeEquiv c).symm]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_unit]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  omega

private theorem fold_max_le (xs : List Nat) (a b : Nat) :
    xs.foldl max a ≤ b ↔ a ≤ b ∧ ∀ n ∈ xs, n ≤ b := by
  induction xs generalizing a with
  | nil => simp
  | cons n xs ih => simp [List.foldl_cons, ih, and_assoc]

/-- Universal and converse bound: rmax is the actual maximum of the raw field
widths, not merely a convenient overestimate. -/
theorem rmax_le_iff (c : Config) (fields : Nat) :
    rmax c ≤ 192 * fields ↔ ∀ q : Coordinate c, rawWidth q ≤ fields := by
  unfold rmax
  rw [mul_le_mul_iff_of_pos_left (by decide : 0 < (192 : Nat)), fold_max_le]
  simp only [Nat.zero_le, true_and, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h q
    exact h (rawWidth q) q (coordinate_mem_schedule q) rfl
  · intro h n q member equal
    subst n
    exact h q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact production round cap, checked over all 56 actual configurations. -/
theorem production_k_cap : ∀ p : ParameterBounds.Profile,
    k (ParameterBounds.config p) ≤ 40 := by
  intro p
  rw [k_exact]
  revert p
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact maximum raw message length over the 56 schedules: 30 full E draws.
The cap and attainment are kernel checked, not inferred from a benchmark. -/
theorem production_rmax_exact :
    (∀ p : ParameterBounds.Profile, rmax (ParameterBounds.config p) ≤ 5760) ∧
      (∃ p : ParameterBounds.Profile, rmax (ParameterBounds.config p) = 5760) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The production k cap is attained, without counting the first group twice. -/
theorem production_k_attained :
    ∃ p : ParameterBounds.Profile, k (ParameterBounds.config p) = 40 := by
  simp_rw [k_exact]
  decide +kernel

/-- Raw min-entropy is 192 and does not acquire the separate Merkle/mode 256-bit
budget. The book constructor must sample the entire dependent raw alphabet. -/
theorem book_raw_requirement (p : ParameterBounds.Profile) :
    ∀ q : Coordinate (ParameterBounds.config p), 2^192 ≤ Fintype.card (Raw q) :=
  raw_entropy192 p

/-- The minimum is exactly 192, not just at least 192: every production tail
contains a genuine single-E draw. Hence one cannot borrow 256-bit hash entropy. -/
theorem book_raw_min_exact (p : ParameterBounds.Profile) :
    (∀ q : Coordinate (ParameterBounds.config p), 2^192 ≤ Fintype.card (Raw q)) ∧
      ∃ q : Coordinate (ParameterBounds.config p), Fintype.card (Raw q) = 2^192 := by
  refine ⟨book_raw_requirement p, ?_⟩
  let j : Fin ((ParameterBounds.config p).logN -
      (ParameterBounds.config p).folds.toList.sum) := ⟨0,(production_edges p).1⟩
  exact ⟨.tail j, by simp⟩

#print axioms k_exact
#print axioms rmax_le_iff
#print axioms production_k_cap
end Whir.PCSBCSRounds
