/-
  LeanVM.Guest.Batch.Group

  The batching's group of challenges, `λ` then the column challenges: a nonzero polynomial of
  total degree `d` in them vanishes at a fraction at most `d/|E|` of them.
-/

module

public import LeanVM.Protocol.Compile.SpecRules.Leaves
public import LeanVM.Protocol.Compile.Rom.Encoding
public import LeanVM.Protocol.ToCompPoly.PowerBatching
public import LeanVM.Facts.Hotwire
public import LeanVM.Protocol.Tables
import LeanVM.ToMathlib.Finset

/-!
# A group of challenges

After its proof of work the batching draws `λ`, then `k = splitLog` column challenges `c`, with no
prover move between them: one group, whose escape probability is the fraction of `(λ, c)` at which
the batched gap vanishes. That gap is `Σ_{m < N} a_m(c)·λ^m`, `a_{2i}(c) = Σ_j eq(c, j)·d_{ij}` the
fold of a fresh claim's errors (multilinear in `c`), `a_{2i+1}` a carried claim's error, a
constant. Schwartz-Zippel, the top coefficient first:

* `avgL k f` is the average of `f` over `k` uniform challenges, the expectation `retExp` takes over
  `sampleChallenges k` (`retExp_sampleChallenges`), and averages commute (`avgL_comm`);
* `avgL_eqAt_le`: a multilinear `Σ_j eq(c, j)·d_j`, not all `d_j` zero, vanishes at a fraction at
  most `k/|E|` of the `c` (one bad value per coordinate);
* `avg_roots_le`: a polynomial in `λ` of degree below `N`, not zero, at most `(N - 1)/|E|`;
* `avgL_poly_le`: the polynomial `Σ_m a_m(c)·λ^m`, by its top coefficient not identically zero
  `a_m*`: where `a_m*(c) ≠ 0` at most `m*` roots in `λ`, and `a_m*(c) = 0` at a fraction `δ_m*` of
  the `c`, so at most `m*/|E| + δ_m*`.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Hotwire (eqAt)
open Finset
open scoped ENNReal

@[expose] public section

-- `E`'s enumeration is `LeanVM.Parameters.instFintypeK`'s, the calculus's (`Spec.sampleE`).
attribute [local instance 1100] LeanVM.Parameters.instFintypeK

/-- `|E|⁻¹`, one challenge's share. -/
noncomputable abbrev invE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹

theorem card_E_ne_zero : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

theorem card_E_ne_top : (Fintype.card E : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _

/-- The average of a constant over the challenges is the constant. -/
theorem avg_const (v : ℝ≥0∞) : invE * ∑ _c : E, v = v := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel card_E_ne_zero card_E_ne_top, one_mul]

/-- An average of an indicator is the fraction of the challenges where it holds. -/
theorem sum_ind_eq_card (p : E → Prop) [DecidablePred p] :
    ∑ x : E, ind (p x) = ((univ.filter p).card : ℝ≥0∞) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : p x <;> simp [ind, h]

/-! ## Averages over `k` challenges -/

/-- **The average of `f` over `k` uniform challenges**, the first drawn first. -/
noncomputable def avgL : ℕ → (List E → ℝ≥0∞) → ℝ≥0∞
  | 0, f => f []
  | k + 1, f => invE * ∑ x : E, avgL k fun cs ↦ f (x :: cs)

theorem avgL_const : ∀ (k : ℕ) (v : ℝ≥0∞), avgL k (fun _ ↦ v) = v
  | 0, _ => rfl
  | k + 1, v => by simp only [avgL, avgL_const k v, avg_const]

/-- Only the lists of `k` challenges count. -/
theorem avgL_mono : ∀ (k : ℕ) {f g : List E → ℝ≥0∞}, (∀ cs, cs.length = k → f cs ≤ g cs) →
    avgL k f ≤ avgL k g
  | 0, _, _, h => h [] rfl
  | k + 1, f, g, h => by
    simp only [avgL]
    gcongr with x
    exact avgL_mono k fun cs hcs ↦ h (x :: cs) (by simp [hcs])

theorem avgL_add : ∀ (k : ℕ) (f g : List E → ℝ≥0∞),
    avgL k (fun cs ↦ f cs + g cs) = avgL k f + avgL k g
  | 0, _, _ => rfl
  | k + 1, f, g => by
    simp only [avgL, avgL_add k, Finset.sum_add_distrib, mul_add]

/-- **Averages commute**: one challenge `λ` averaged inside or outside `k` others. -/
theorem avgL_comm : ∀ (k : ℕ) (f : E → List E → ℝ≥0∞),
    avgL k (fun cs ↦ invE * ∑ y : E, f y cs) = invE * ∑ y : E, avgL k (f y)
  | 0, _ => rfl
  | k + 1, f => by
    have ih := fun x : E ↦ avgL_comm k fun y cs ↦ f y (x :: cs)
    simp only [avgL, ih]
    congr 1
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]

/-- `retExp` over `k` challenges then a continuation is the average over them. -/
theorem retExp_sampleChallenges {α : Type} (g : α → List Ev → ℝ≥0∞) (h₀ : List Ev) :
    ∀ (k : ℕ) (f : List E → VerifierProgram α) (l : List Ev),
      VerifierProgram.retExp g h₀ l (VerifierProgram.sampleChallenges k >>= f) =
        avgL k fun cs ↦ VerifierProgram.retExp g h₀ (l ++ cs.map Ev.sample) (f cs)
  | 0, f, l => by simp [VerifierProgram.sampleChallenges, avgL]
  | k + 1, f, l => by
    have e : VerifierProgram.sampleChallenges (k + 1) >>= f =
        VerifierProgram.sample fun x ↦ VerifierProgram.sampleChallenges k >>= fun xs ↦ f (x :: xs) := by
      simp only [VerifierProgram.sampleChallenges, VerifierProgram.sampleChallenge,
        VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.pure_eq,
        VerifierProgram.ret_bind]
      rfl
    rw [e, VerifierProgram.retExp, avgL]
    refine congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)
    rw [retExp_sampleChallenges g h₀ k _ (l ++ [Ev.sample x])]
    simp [List.append_assoc]

/-! ## A multilinear function of the challenges -/

/-- **A multilinear function vanishes rarely**: `Σ_{j < 2^k} eq(c, j)·d_j`, some `d_j ≠ 0`, is
zero at a fraction at most `k/|E|` of the points `c` of `k` coordinates. -/
theorem avgL_eqAt_le : ∀ (k : ℕ) (d : ℕ → E), (∃ j < 2 ^ k, d j ≠ 0) →
    avgL k (fun c ↦ ind (∑ j ∈ range (2 ^ k), eqAt c j * d j = 0)) ≤ k * invE
  | 0, d, ⟨j, hj, hd⟩ => by
    obtain rfl : j = 0 := by simpa using hj
    simp only [avgL, pow_zero, range_one, sum_singleton, Nat.cast_zero, zero_mul]
    rw [ind_of_not (by simpa [Hotwire.eqAt] using hd)]
  | k + 1, d, ⟨j, hj, hd⟩ => by
    -- the first coordinate `x`: `Σ_j eq(x :: c, j)·d_j = Σ_j eq(c, j)·e_x(j)`
    set e : E → ℕ → E := fun x j ↦ (1 + x) * d (2 * j) + x * d (2 * j + 1)
    have hsplit : ∀ (x : E) (c : List E), ∑ j ∈ range (2 ^ (k + 1)), eqAt (x :: c) j * d j =
        ∑ j ∈ range (2 ^ k), eqAt c j * e x j := by
      intro x c
      rw [pow_succ, mul_comm, Finset.sum_range_two_mul]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [Hotwire.eqAt_cons_two_mul, Hotwire.eqAt_cons_two_mul_add_one, CharTwo.sub_eq_add]
      simp only [e]
      ring
    -- the bad first coordinates: those killing every `e_x`; at most one
    obtain ⟨j', hj', hj'd⟩ : ∃ j' < 2 ^ k, d (2 * j') ≠ 0 ∨ d (2 * j' + 1) ≠ 0 := by
      refine ⟨j / 2, by rw [pow_succ] at hj; omega, ?_⟩
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact Or.inl (by simpa [show 2 * i / 2 = i by omega] using hd)
      · exact Or.inr (by simpa [show (2 * i + 1) / 2 = i by omega] using hd)
    have hbad : ∑ x : E, ind (e x j' = 0) ≤ 1 := by
      refine sum_ind_le_one fun x y hx hy ↦ ?_
      simp only [e] at hx hy
      by_contra hxy
      have h2 : (2 : E) = 0 := Tables.two_eq_zero_E
      have hab : d (2 * j') = d (2 * j' + 1) := by
        have : (x - y) * (d (2 * j' + 1) - d (2 * j')) = 0 := by
          linear_combination hx - hy + (y - x) * d (2 * j') * h2
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (sub_eq_zero.mp h) hxy
        · exact (sub_eq_zero.mp h).symm
      have : d (2 * j') = 0 := by
        rw [← hab] at hx
        linear_combination hx - x * d (2 * j') * h2
      rcases hj'd with h | h
      · exact h this
      · exact h (hab ▸ this)
    have hx : ∀ x : E, avgL k (fun c ↦ ind (∑ j ∈ range (2 ^ k), eqAt c j * e x j = 0)) ≤
        ind (e x j' = 0) + k * invE := by
      intro x
      by_cases h0 : e x j' = 0
      · rw [ind_of h0]
        exact (avgL_mono k fun _ _ ↦ ind_le_one _).trans ((avgL_const k 1).le.trans le_self_add)
      · rw [ind_of_not h0, zero_add]
        exact avgL_eqAt_le k (e x) ⟨j', hj', h0⟩
    simp only [avgL]
    simp_rw [hsplit]
    calc invE * ∑ x : E, avgL k (fun c ↦ ind (∑ j ∈ range (2 ^ k), eqAt c j * e x j = 0))
        ≤ invE * ∑ x : E, (ind (e x j' = 0) + k * invE) := by gcongr with x; exact hx x
      _ ≤ invE * 1 + k * invE := by
          rw [Finset.sum_add_distrib, mul_add, avg_const]
          gcongr
      _ = (k + 1 : ℕ) * invE := by push_cast; ring

/-! ## A polynomial in `λ` -/

/-- **A nonzero polynomial of degree below `N` has at most `N - 1` roots**: the fraction of `λ`
killing `Σ_{m < N} a_m·λ^m`, some `a_m ≠ 0`. -/
theorem avg_roots_le (N : ℕ) (a : ℕ → E) (ha : ∃ m < N, a m ≠ 0) :
    invE * ∑ y : E, ind (∑ m ∈ range N, a m * y ^ m = 0) ≤ invE * (N - 1 : ℕ) := by
  classical
  rw [sum_ind_eq_card]
  gcongr
  obtain ⟨m, hm, hne⟩ := ha
  have h := LeanVM.Protocol.card_false_batch_le (fun j : Fin N ↦ a j) (fun _ ↦ 0)
    ⟨⟨m, hm⟩, hne⟩
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, LeanVM.Protocol.powerBatch, zero_mul,
    Finset.sum_const_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ a j * y ^ j)]

/-- **The top coefficient bounds a polynomial in `λ` with coefficients in `c`.** For coefficients
`a_m(c)`, `m < N`, each identically zero on the points of `k` coordinates or zero at a fraction at
most `δ_m` of them with `m/|E| + δ_m ≤ B`, not all identically zero, the fraction of `(c, λ)`
killing `Σ_m a_m(c)·λ^m` is at most `B`. -/
theorem avgL_poly_le (k : ℕ) (a : ℕ → List E → E) (δ : ℕ → ℝ≥0∞) (B : ℝ≥0∞) :
    ∀ N : ℕ, (∀ m < N, (¬ ∀ c : List E, c.length = k → a m c = 0) →
        avgL k (fun c ↦ ind (a m c = 0)) ≤ δ m ∧ invE * m + δ m ≤ B) →
      (∃ m < N, ¬ ∀ c : List E, c.length = k → a m c = 0) →
      avgL k (fun c ↦ invE * ∑ y : E, ind (∑ m ∈ range N, a m c * y ^ m = 0)) ≤ B
  | 0, _, ⟨_, hm, _⟩ => absurd hm (Nat.not_lt_zero _)
  | N + 1, ha, hne => by
    by_cases hz : ∀ c : List E, c.length = k → a N c = 0
    · -- the top coefficient vanishes: drop it
      obtain ⟨m, hm, hm0⟩ := hne
      have hmN : m < N := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | rfl
        · exact h
        · exact absurd hz hm0
      refine le_trans (avgL_mono k fun c hc ↦ le_of_eq ?_)
        (avgL_poly_le k a δ B N (fun m hm ↦ ha m (by omega)) ⟨m, hmN, hm0⟩)
      simp only [Finset.sum_range_succ, hz c hc, zero_mul, add_zero]
    · obtain ⟨hδ, hB⟩ := ha N (Nat.lt_succ_self N) hz
      have hpt : ∀ c : List E, invE * ∑ y : E, ind (∑ m ∈ range (N + 1), a m c * y ^ m = 0) ≤
          invE * N + ind (a N c = 0) := by
        intro c
        by_cases h0 : a N c = 0
        · rw [ind_of h0]
          calc invE * ∑ y : E, ind (∑ m ∈ range (N + 1), a m c * y ^ m = 0)
              ≤ invE * ∑ _y : E, (1 : ℝ≥0∞) := by gcongr with y; exact ind_le_one _
            _ = 1 := avg_const 1
            _ ≤ invE * N + 1 := le_add_self
        · rw [ind_of_not h0, add_zero]
          have := avg_roots_le (N + 1) (fun m ↦ a m c) ⟨N, Nat.lt_succ_self N, h0⟩
          simpa using this
      calc avgL k (fun c ↦ invE * ∑ y : E, ind (∑ m ∈ range (N + 1), a m c * y ^ m = 0))
          ≤ avgL k (fun c ↦ invE * N + ind (a N c = 0)) := avgL_mono k fun c _ ↦ hpt c
        _ = invE * N + avgL k (fun c ↦ ind (a N c = 0)) := by
          rw [avgL_add, avgL_const]
        _ ≤ invE * N + δ N := by gcongr
        _ ≤ B := hB

/-! ## No move in the group -/

/-- A program of challenges only: samples, then a return. -/
def OnlySamples {α : Type} : VerifierProgram α → Prop
  | .ret _ => True
  | .sample k => ∀ x, OnlySamples (k x)
  | _ => False

theorem OnlySamples.after {α : Type} {p : VerifierProgram α} (hp : OnlySamples p) :
    ∀ {l : List Ev} {q : VerifierProgram α}, p.after l = some q → OnlySamples q := by
  intro l
  induction l generalizing p with
  | nil => intro q h; simp only [VerifierProgram.after, Option.some.injEq] at h; exact h ▸ hp
  | cons e es ih =>
    intro q h
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq, OnlySamples] at h hp
    exact ih (hp _) h

theorem OnlySamples.not_isMove {α : Type} {p : VerifierProgram α} (hp : OnlySamples p) :
    ¬ p.IsMove := by
  cases p <;> simp_all [OnlySamples, VerifierProgram.IsMove]

theorem onlySamples_sampleChallenges {α : Type} (f : List E → VerifierProgram α)
    (hf : ∀ cs, OnlySamples (f cs)) :
    ∀ k, OnlySamples (VerifierProgram.sampleChallenges k >>= f)
  | 0 => by simpa [VerifierProgram.sampleChallenges] using hf []
  | k + 1 => by
    intro x
    simpa [VerifierProgram.sampleChallenges, VerifierProgram.sampleChallenge,
      VerifierProgram.bind_eq, VerifierProgram.bind_assoc, VerifierProgram.bind] using
      onlySamples_sampleChallenges (fun xs ↦ f (x :: xs)) (fun cs ↦ hf _) k

end
end LeanVM.Guest.Batch
