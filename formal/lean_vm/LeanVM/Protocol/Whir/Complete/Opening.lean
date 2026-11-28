/-
  LeanVM.Protocol.Whir.Complete.Opening

  The stacked opening's ladder, its batched claims' tables, and the commitment it opens.
-/

module

import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Whir.Complete.Encoding
public import Statement.Prover.Whir
public import LeanVM.Protocol.EndToEnd.Claims
import LeanVM.Parameters.Whir

/-!
# The stacked opening's starting claim

The verifier is `LeanVM.Protocol.Verifier.verifyStackedOpening` / `verifyWhir`
(`crates/verifier/src/lib.rs`, `whir.rs`), with the commitment `commitStack`.

* The ladder of an admissible pair starts with the lane fold at the announced rate
  (`exists_ladder`).
* `batchedBasis`, `basisTable`: the claims batched by the powers of the batching challenge, and
  their table at the rotated cube point. `dot_values_eq_dot`: claims that hold give the batched
  value as the pairing of the basis table with the stack table; `multilinearEval_basisTable`: the
  batched basis at the rotated point is the extension of the basis table.
* `stackCommit μ R q`: the commitment the opening opens at level `0`.

The honest opening's run against the verifier is `LeanVM.Prover.Complete.Whir.Levels`.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Protocol.Tables


open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  LeanVM.Protocol.Compile LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## The ladder -/

private theorem admissible_bounded {μ R : ℕ} (h : Whir.Admissible μ R) :
    μ < Whir.maxLogStack + 1 ∧ R < 5 := by
  obtain ⟨_, h2, _, h4⟩ := h
  exact ⟨Nat.lt_succ_of_le h2, Nat.lt_succ_of_le h4⟩

/-- Every admissible ladder starts with the lane fold at the announced rate, and its folds fit
in the stack. -/
theorem ladder_head_sum {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∀ levels, Whir.ladder μ R = some levels →
      levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, R) ∧
        (levels.map (·.fold)).sum ≤ μ := by
  have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
      ∀ levels, Whir.ladder μ r = some levels →
        levels.head?.map (fun l ↦ (l.fold, l.logInvRate)) = some (laneBits, r) ∧
          (levels.map (·.fold)).sum ≤ μ := by decide +kernel
  obtain ⟨h1, h2⟩ := admissible_bounded h
  exact key μ h1 R h2 h

/-- The ladder of an admissible pair, with its first level made explicit. -/
theorem exists_ladder {μ R : ℕ} (h : Whir.Admissible μ R) :
    ∃ q₀ rest, Whir.ladder μ R = some (⟨laneBits, R, q₀⟩ :: rest) ∧
      laneBits + (rest.map (·.fold)).sum ≤ μ := by
  obtain ⟨config, hc⟩ := Option.isSome_iff_exists.mp (Whir.ladder_isSome h)
  obtain ⟨hhead, hsum⟩ := ladder_head_sum h config hc
  rcases config with _ | ⟨⟨f, r, q₀⟩, rest⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hhead
    obtain ⟨rfl, rfl⟩ := hhead
    refine ⟨q₀, rest, hc, ?_⟩
    simpa using hsum

/-! ## The stack claims -/

/-- The batched basis of the stack claims, `p ↦ Σ_k s_k·w_k(p)` (`verify_stacked_opening`'s
`evaluate_basis`). -/
def batchedBasis (scales : List E) (claims : List StackClaim) : List E → E :=
  fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-- The batched basis of multilinear weights is multilinear. -/
theorem isMultilinearFn_batchedBasis {m : ℕ} :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, IsMultilinearFn m c.1) →
      IsMultilinearFn m (batchedBasis scales claims)
  | [], _, _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | _ :: _, [], _ => isMultilinearFn_congr (isMultilinearFn_const_zero m) fun p _ ↦ by
      simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    refine isMultilinearFn_congr (isMultilinearFn_add (isMultilinearFn_const_mul (h c (by simp)) a)
      (isMultilinearFn_batchedBasis scales claims fun c' hc' ↦ h c' (by simp [hc'])))
      fun p _ ↦ ?_
    simp [batchedBasis, dot_cons]

/-- The batched value of claims that hold is the batched basis paired with the stack. -/
theorem dot_values_eq_sum {μ : ℕ} (q : Column μ) :
    ∀ (scales : List E) (claims : List StackClaim), (∀ c ∈ claims, StackClaim.Holds μ c q) →
      dot scales (claims.map (·.2)) =
        ∑ x ∈ range (2 ^ μ), batchedBasis scales claims (boolPoint μ x) * ofK (q.values.getD x 0)
  | [], _, _ => by simp [batchedBasis]
  | _ :: _, [], _ => by simp [batchedBasis]
  | a :: scales, c :: claims, h => by
    have hc := h c (by simp)
    rw [StackClaim.Holds, Fin.sum_univ_eq_sum_range
      (fun x ↦ c.1 (boolPoint μ x) * ofK (q.values.getD x 0))] at hc
    simp only [List.map_cons, dot_cons, batchedBasis] at *
    rw [dot_values_eq_sum q scales claims fun c' hc' ↦ h c' (by simp [hc']), ← hc, mul_sum,
      ← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by simp only [batchedBasis]; ring

/-- The batched basis at the rotated point: the weight table of the opening's starting claim. -/
def basisTable (μ : ℕ) (scales : List E) (claims : List StackClaim) : List E :=
  tableOf μ fun p ↦ batchedBasis scales claims (p.drop laneBits ++ p.take laneBits)

/-- **The starting claim.** The batched value of claims that hold is the pairing of the basis
table with the stack table, both in the WHIR variable order. -/
theorem dot_values_eq_dot {μ : ℕ} (hμ : laneBits ≤ μ) (q : Column μ) (scales : List E)
    (claims : List StackClaim) (h : ∀ c ∈ claims, StackClaim.Holds μ c q) :
    dot scales (claims.map (·.2)) = dot (basisTable μ scales claims) (stackTable μ q) := by
  rw [dot_values_eq_sum q scales claims h, basisTable, dot_tableOf _ _ _ (length_stackTable μ q)]
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hn : laneBits + n - laneBits = n := by omega
  have hrot := sum_rotIndex laneBits n
    (fun x ↦ batchedBasis scales claims (boolPoint (n + laneBits) x) *
      ofK (q.values.getD x 0))
  rw [Nat.add_comm n laneBits] at hrot
  rw [← hrot]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : i < 2 ^ (laneBits + n) := mem_range.mp hi
  have hb := boolPoint_rotIndex laneBits n i hi'
  rw [Nat.add_comm n laneBits] at hb
  simp only [stackTable, hn]
  rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range, hb]

/-- The batched basis at the rotated point is the extension of the basis table. -/
theorem multilinearEval_basisTable {μ : ℕ} (hμ : laneBits ≤ μ) (scales : List E)
    (claims : List StackClaim) (hml : ∀ c ∈ claims, IsMultilinearFn μ c.1) (p : List E)
    (hp : p.length = μ) :
    multilinearEval (basisTable μ scales claims) p =
      batchedBasis scales claims (p.drop laneBits ++ p.take laneBits) := by
  obtain ⟨n, rfl⟩ : ∃ n, μ = laneBits + n := ⟨μ - laneBits, by omega⟩
  have hB := isMultilinearFn_batchedBasis scales claims hml
  rw [Nat.add_comm] at hB
  exact multilinearEval_tableOf (isMultilinearFn_rotate hB) p hp

/-- The commitment the opening opens at level `0`: the stack's word, `2^(μ−6+R)` leaves of `64`
words. -/
def stackCommit (μ R : ℕ) (q : Column μ) : ℕ × ℕ × Word :=
  (μ - laneBits + R, 2 ^ laneBits, stackWord μ R q)

end
end LeanVM.Protocol.Whir.Complete
