module

public import LeanVM.Cost.Bounds.PMBasis.Defs
public import Mathlib.Order.MinMax
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-!
# PM-basis's price: the divide-and-conquer recursion, solved

For a price `T` on the recursion's states `x` (fuel, problem, shift) whose maximal order is
`ord x`:

* **`le_pmTree`**: a leaf (maximal order `≤ c` or `≤ 1`) priced at most `L`, an inner node at
  most `N (ord x)` and its two children's prices, the children at the maximal orders
  `ord x / 2` and `ord x − ord x / 2` (exactly), give `T x ≤ pmTree c L N (ord x)`;
* **`pmTreePair_eq`**: `pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1))` for
  `q + 1 ≤ 2^f` (the evaluation in `f` steps);
* **`le_two_pow_clog2`**, **`clog2_le`**: `clog2 e` is the least `j` with `e ≤ 2^j`;
  `clog2_mono`.
-/

namespace LeanVM.Cost.Bounds.PMBasis

public section

theorem pmTree_eq (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) :
    pmTree c L N o = if o ≤ c ∨ o ≤ 1 then L
      else N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2) := by
  rw [pmTree]

theorem pmTree_leaf {c L : ℕ} {N : ℕ → ℕ} {o : ℕ} (h : o ≤ c ∨ o ≤ 1) : pmTree c L N o = L := by
  rw [pmTree_eq]
  split_ifs
  rfl

theorem pmTree_node {c L : ℕ} {N : ℕ → ℕ} {o : ℕ} (hc : c < o) (h1 : 1 < o) :
    pmTree c L N o = N o + pmTree c L N (o / 2) + pmTree c L N (o - o / 2) := by
  rw [pmTree_eq]
  split_ifs with h'
  · omega
  · rfl

/-! ## The recursion's price -/

/-- **The divide-and-conquer price**: on states `x` of an invariant `I`, a leaf (`ord x ≤ c` or
`ord x ≤ 1`) at most `L`; an inner node (`c < ord x`, `1 < ord x`) at most `N (ord x)` and the
prices of two children of `I` at the maximal orders `ord x / 2` and `ord x − ord x / 2`. Then
`T x ≤ pmTree c L N (ord x)`. -/
theorem le_pmTree {α : Type*} (I : α → Prop) (ord T : α → ℕ) (c L : ℕ) (N : ℕ → ℕ)
    (hleaf : ∀ x, I x → (ord x ≤ c ∨ ord x ≤ 1) → T x ≤ L)
    (hnode : ∀ x, I x → c < ord x → 1 < ord x → ∃ y z, I y ∧ I z ∧ ord y = ord x / 2 ∧
      ord z = ord x - ord x / 2 ∧ T x ≤ N (ord x) + T y + T z) :
    ∀ x, I x → T x ≤ pmTree c L N (ord x) := by
  intro x hx
  induction hm : ord x using Nat.strong_induction_on generalizing x with
  | _ o ih =>
    subst hm
    by_cases h : ord x ≤ c ∨ ord x ≤ 1
    · rw [pmTree_leaf h]; exact hleaf x hx h
    · obtain ⟨y, z, hy, hz, hoy, hoz, hT⟩ := hnode x hx (by omega) (by omega)
      rw [pmTree_node (by omega) (by omega)]
      have := ih (ord y) (by omega) y hy rfl
      have := ih (ord z) (by omega) z hz rfl
      rw [hoy] at *; rw [hoz] at *
      omega

/-! ## The evaluation in `log₂ o` steps -/

theorem pmTreeStep_eq (c L : ℕ) (N : ℕ → ℕ) (h x : ℕ) (hx : x / 2 = h ∨ x / 2 = h + 1)
    (hx' : x - x / 2 = h ∨ x - x / 2 = h + 1) :
    pmTreeStep c L N h (pmTree c L N h) (pmTree c L N (h + 1)) x = pmTree c L N x := by
  have sel : ∀ y, (y = h ∨ y = h + 1) →
      (if y = h then pmTree c L N h else pmTree c L N (h + 1)) = pmTree c L N y := by
    intro y hy
    rcases hy with rfl | rfl
    · simp
    · simp
  unfold pmTreeStep
  rw [pmTree_eq c L N x, sel _ hx, sel _ hx']

/-- **The evaluation**: `pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1))` when
`q + 1 ≤ 2^f`. -/
theorem pmTreePair_eq (c L : ℕ) (N : ℕ → ℕ) :
    ∀ f q, q + 1 ≤ 2 ^ f → pmTreePair c L N f q = (pmTree c L N q, pmTree c L N (q + 1)) := by
  intro f
  induction f with
  | zero =>
    intro q hq
    simp at hq
    subst hq
    simp only [pmTreePair, pmTree_leaf (show (0 : ℕ) ≤ c ∨ 0 ≤ 1 by omega),
      pmTree_leaf (show (0 + 1 : ℕ) ≤ c ∨ 0 + 1 ≤ 1 by omega)]
  | succ f ih =>
    intro q hq
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by ring
    rw [pmTreePair, ih (q / 2) (by omega)]
    simp only
    rw [pmTreeStep_eq c L N _ q (by omega) (by omega),
      pmTreeStep_eq c L N _ (q + 1) (by omega) (by omega)]

/-! ## `clog2` -/

theorem le_two_pow_clog2Loop (e : ℕ) :
    ∀ fuel j, e ≤ j + fuel → e ≤ 2 ^ clog2Loop e fuel j
  | 0, j, h => by
    rw [clog2Loop]
    exact (Nat.le_of_lt_succ (by omega : e < j + 1)).trans (Nat.lt_two_pow_self).le
  | fuel + 1, j, h => by
    rw [clog2Loop]
    split
    · assumption
    · exact le_two_pow_clog2Loop e fuel (j + 1) (by omega)

theorem le_two_pow_clog2 (e : ℕ) : e ≤ 2 ^ clog2 e :=
  le_two_pow_clog2Loop e e 0 (by omega)

theorem clog2Loop_le (e : ℕ) {j : ℕ} (hj : e ≤ 2 ^ j) :
    ∀ fuel j₀, j₀ ≤ j → clog2Loop e fuel j₀ ≤ j
  | 0, _, h => h
  | fuel + 1, j₀, h => by
    rw [clog2Loop]
    split
    · exact h
    · rename_i hlt
      have : j₀ < j := by
        by_contra hc
        exact hlt (hj.trans (Nat.pow_le_pow_right (by omega) (by omega)))
      exact clog2Loop_le e hj fuel (j₀ + 1) this

/-- `clog2 e` is the least: `e ≤ 2^j` gives `clog2 e ≤ j`. -/
theorem clog2_le {e j : ℕ} (hj : e ≤ 2 ^ j) : clog2 e ≤ j :=
  clog2Loop_le e hj e 0 (Nat.zero_le _)

theorem clog2_mono {a b : ℕ} (h : a ≤ b) : clog2 a ≤ clog2 b :=
  clog2_le (h.trans (le_two_pow_clog2 b))

/-- **`pmTreeEval` is `pmTree`.** -/
theorem pmTreeEval_eq (c L : ℕ) (N : ℕ → ℕ) (o : ℕ) : pmTreeEval c L N o = pmTree c L N o := by
  rw [pmTreeEval, pmTreePair_eq c L N _ o (le_two_pow_clog2 (o + 1))]

end

end LeanVM.Cost.Bounds.PMBasis
