/-
The last level: transitions M4 (the final polynomial, its point check and its queries) and M5 (a
tail sumcheck round) of Theorem 5.2 of the paper (Section 5.4), and M4 of Theorem 5.6
(Section 5.5).
-/
import Rounds.Query

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K]

/-- The count behind M4: if `P ∈ List(w; A, d)` and the point check together force `P` to violate
the running claim, then at most `(A - 1)^t` position vectors are such that the point check and
the query check pass and `P` satisfies the running claim. -/
theorem final_core (D : Finset K) (w : K → K) (A : ℕ) {s : ℕ} (ζ v : Fin s → K)
    (W : K[X] →ₗ[K] K) (σ : K) (P : K[X])
    (hI : A ≤ (D.filter (fun x => P.eval x = w x)).card → (∀ m, P.eval (ζ m) = v m) → W P ≠ σ)
    (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
      (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ)).card ≤
      (A - 1) ^ t := by
  by_cases hA : A ≤ (D.filter (fun x => P.eval x = w x)).card
  · have hempty : (Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
        (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ) = ∅ :=
      filter_eq_empty_iff.mpr (fun x _ hx => hI hA hx.1 hx.2.2)
    rw [hempty, card_empty]
    exact Nat.zero_le _
  · refine (card_le_card ?_).trans (card_queries_agree_le D w P (not_le.mp hA) t)
    intro x hx
    obtain ⟨hxD, _, hq, _⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxD, hq⟩

/-- **Transition M4 of Theorem 5.2 and of Theorem 5.6 of the paper** (Sections 5.4 and 5.5),
counting form.

At the end of the last level the fold is the one-lane word `w`, the carried claims are `(ζ, v)`,
the running claim is `(W, σ)` and `(I^B_{Λ-1,ℓ})` holds (`hI`). The prover sends a polynomial `P`
of degree at most `d` in the clear. The verifier checks `P(ζ_m) = v_m` for every `m` (Protocol 4.2,
step 3) and `P(x_q) = w(x_q)` at `t` query positions.

Conclusion: at most `(A - 1)^t` of the `n^t` position vectors are such that both checks pass, `P`
satisfies the running claim (so that the tail sumcheck starts from a true claim), and it is not
the case that `P` is in the list with `¬ B(P)`. So, except on those vectors: a check fails, or
the running claim is false for `P`, or `P ∈ List(w; A, d)` and `¬ B(P)`, the conclusion of
Theorem 5.6 for an accepting run. -/
theorem final_transition (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ} (ζ v : Fin s → K)
    (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop) (hI : Doomed₁ D w d A ζ v W σ B)
    (P : K[X]) (hP : P.natDegree ≤ d) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
      (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ ∧
        ¬ (A ≤ (D.filter (fun x => P.eval x = w x)).card ∧ ¬ B P))).card ≤ (A - 1) ^ t := by
  by_cases hB : A ≤ (D.filter (fun x => P.eval x = w x)).card ∧ ¬ B P
  · have hempty : (Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
        (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ ∧
          ¬ (A ≤ (D.filter (fun x => P.eval x = w x)).card ∧ ¬ B P)) = ∅ :=
      filter_eq_empty_iff.mpr (fun x _ hx => hx.2.2.2 hB)
    rw [hempty, card_empty]
    exact Nat.zero_le _
  · refine (card_le_card ?_).trans (final_core D w A ζ v W σ P (fun hA hpt => ?_) t)
    · intro x hx
      obtain ⟨hxD, hpt, hq, hW, _⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxD, hpt, hq, hW⟩
    · refine hI P hP hA ?_ hpt
      by_contra hnB
      exact hB ⟨hA, hnB⟩

/-- **Transition M4 of Theorem 5.2 of the paper** (plain soundness): at most `(A - 1)^t` position
vectors are such that the point check and the query check pass and `P` satisfies the running
claim. -/
theorem final_transition_plain (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ} (ζ v : Fin s → K)
    (W : K[X] →ₗ[K] K) (σ : K) (hI : Doomed₁ D w d A ζ v W σ (fun _ => True))
    (P : K[X]) (hP : P.natDegree ≤ d) (t : ℕ) :
    ((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
      (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ)).card ≤
      (A - 1) ^ t :=
  final_core D w A ζ v W σ P (fun hA hpt => hI P hP hA trivial hpt) t

/-- Transition M4 as a density over `t` independent uniform positions: at most `((A - 1)/n)^t`,
row M4 of Theorem 5.2 of the paper. -/
theorem final_transition_density (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ} (ζ v : Fin s → K)
    (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop) (hI : Doomed₁ D w d A ζ v W σ B)
    (P : K[X]) (hP : P.natDegree ≤ d) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => D)).filter (fun x =>
      (∀ m, P.eval (ζ m) = v m) ∧ (∀ q, P.eval (x q) = w (x q)) ∧ W P = σ ∧
        ¬ (A ≤ (D.filter (fun x => P.eval x = w x)).card ∧ ¬ B P))).card : ℚ) /
        ((Fintype.piFinset (fun _ : Fin t => D)).card : ℚ) ≤
      (((A - 1 : ℕ) : ℚ) / (D.card : ℚ)) ^ t := by
  have h := final_transition D w d A ζ v W σ B hI P hP t
  have hcard : (Fintype.piFinset (fun _ : Fin t => D)).card = D.card ^ t := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
  rw [hcard, div_pow]
  push_cast
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact_mod_cast h

variable [Fintype K]

/-- **Transition M5 of Theorem 5.2 of the paper** (a tail sumcheck round of degree two), counting
form.

The claim before the round is `∑_{b, x} W(b, x) f(b, x) = σ` over `{0,1} × Y`, with
`W₀ = W(0, ·)`, `W₁ = W(1, ·)` and the same for `f`; it is false (`hfalse`). The prover sends a
round polynomial `h` of degree at most two, the verifier checks `h(0) + h(1) = σ` and samples
`r`, and the claim after the round is `∑_x W(r, x) f(r, x) = h(r)`, where `W(r, ·)` and `f(r, ·)`
are the multilinear extensions in the first variable, `(1 - r) W₀ + r W₁` (in characteristic two,
`(1 + r) W₀ + r W₁`).

Conclusion: at most two values of `r` are such that the check passes and the claim after the
round is true. -/
theorem tail_round_transition {Y : Type*} [Fintype Y] (W₀ W₁ f₀ f₁ : Y → K) (σ : K)
    (hfalse : ∑ x, (W₀ x * f₀ x + W₁ x * f₁ x) ≠ σ) (h : K[X]) (hh : h.natDegree ≤ 2) :
    (univ.filter (fun r : K => h.eval 0 + h.eval 1 = σ ∧
      ∑ x, ((1 - r) * W₀ x + r * W₁ x) * ((1 - r) * f₀ x + r * f₁ x) = h.eval r)).card ≤ 2 := by
  by_cases hchk : h.eval 0 + h.eval 1 = σ
  swap
  · rw [filter_eq_empty_iff.mpr (fun r _ hr => hchk hr.1), card_empty]
    exact Nat.zero_le _
  let g : K[X] := ∑ x, ((1 - X) * C (W₀ x) + X * C (W₁ x)) * ((1 - X) * C (f₀ x) + X * C (f₁ x))
  have hg : ∀ r : K, g.eval r =
      ∑ x, ((1 - r) * W₀ x + r * W₁ x) * ((1 - r) * f₀ x + r * f₁ x) := by
    intro r
    simp only [g, eval_finsetSum, eval_mul, eval_add, eval_sub, eval_one, eval_X, eval_C]
  have hlin : ∀ a b : K, ((1 - X) * C a + X * C b : K[X]).natDegree ≤ 1 := by
    intro a b
    compute_degree
  have hgd : g.natDegree ≤ 2 :=
    natDegree_sum_le_of_forall_le _ _ (fun x _ => natDegree_mul_le_of_le (hlin _ _) (hlin _ _))
  have hne : g - h ≠ 0 := by
    intro heq
    apply hfalse
    rw [← hchk, ← sub_eq_zero.mp heq, hg, hg, ← sum_add_distrib]
    refine sum_congr rfl (fun x _ => ?_)
    ring
  calc (univ.filter (fun r : K => h.eval 0 + h.eval 1 = σ ∧
        ∑ x, ((1 - r) * W₀ x + r * W₁ x) * ((1 - r) * f₀ x + r * f₁ x) = h.eval r)).card
      ≤ (univ.filter (fun r : K => (g - h).eval r = 0)).card := by
        refine card_le_card (fun r hr => ?_)
        obtain ⟨_, _, hr2⟩ := mem_filter.mp hr
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rw [eval_sub, hg, hr2, sub_self]
    _ ≤ (g - h).natDegree := card_roots_le hne
    _ ≤ 2 := natDegree_sub_le_of_le hgd hh

/-- Transition M5 as a density: at most `2/q`, row M5 of Theorem 5.2 of the paper. -/
theorem tail_round_transition_density {Y : Type*} [Fintype Y] (W₀ W₁ f₀ f₁ : Y → K) (σ : K)
    (hfalse : ∑ x, (W₀ x * f₀ x + W₁ x * f₁ x) ≠ σ) (h : K[X]) (hh : h.natDegree ≤ 2) :
    ((univ.filter (fun r : K => h.eval 0 + h.eval 1 = σ ∧
      ∑ x, ((1 - r) * W₀ x + r * W₁ x) * ((1 - r) * f₀ x + r * f₁ x) = h.eval r)).card : ℚ) /
        (Fintype.card K : ℚ) ≤ 2 / (Fintype.card K : ℚ) := by
  have h2 := tail_round_transition W₀ W₁ f₀ f₁ σ hfalse h hh
  have hq : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  refine div_le_div_of_nonneg_right ?_ hq.le
  exact_mod_cast h2

end Rounds
