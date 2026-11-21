/-
A level of the protocol, and Lemma 4.12 of the paper for it with one batch of points: the
exponents `e_j` of Definition 4.1, the words of a level and their folds, the potential, and the
goodness of points of Section 5.3.

A word with `r` lane variables has lanes `Lane r`, where `Lane (r + 1) = Lane r ⊕ Lane r`: the
first summand is the half whose first remaining lane variable is `0` (the half `F`, `O₀`), the
second the half where it is `1` (`G`, `O₁`). A round folds the first remaining variable. After
`k` rounds of a level, the exponent map of a tuple with `r` lane variables is `exL k r`, the
`e_k` of the paper, and `thr k` is the agreement threshold of the lists of the words folded `k`
times (`A^{(i,k)}`).
-/
import DeepFold.Main
import Protocol.Pinning

open Polynomial Finset
open scoped Classical

namespace Protocol

open DeepFold

/-- The lanes of an interleaved word with `r` lane variables: `{0,1}^r`, as an iterated sum. -/
def Lane : ℕ → Type
  | 0 => Unit
  | r + 1 => Lane r ⊕ Lane r

instance Lane.instFintype : ∀ r, Fintype (Lane r)
  | 0 => inferInstanceAs (Fintype Unit)
  | r + 1 =>
      haveI := Lane.instFintype r
      inferInstanceAs (Fintype (Lane r ⊕ Lane r))

/-- The exponents `e_j` of Definition 4.1 of the paper, for a tuple with `r` lane variables
`u_{j+1}, …, u_{j+r}` after `j` rounds: `e_j(u) = ∑_k (1 - u_k) 2^(k-1)`. The half with
`u_{j+1} = 0` carries the extra exponent `2^j`. -/
def exL : ℕ → ∀ r, Lane r → ℕ
  | _, 0 => fun _ => 0
  | j, r + 1 => Sum.elim (fun u => 2 ^ j + exL (j + 1) r u) (exL (j + 1) r)

theorem exL_succ (j r : ℕ) :
    exL j (r + 1) = Sum.elim (fun u => 2 ^ j + exL (j + 1) r u) (exL (j + 1) r) := rfl

/-- Every exponent of `e_j` is a multiple of `2^j`. -/
theorem two_pow_dvd_exL : ∀ (r j : ℕ) (u : Lane r), 2 ^ j ∣ exL j r u
  | 0, _, _ => dvd_zero _
  | r + 1, j, u => by
      have h : ∀ v : Lane r, 2 ^ j ∣ exL (j + 1) r v := fun v =>
        (pow_dvd_pow 2 (Nat.le_succ j)).trans (two_pow_dvd_exL r (j + 1) v)
      rcases u with u | u
      · exact (Nat.dvd_add_right (dvd_refl _)).mpr (h u)
      · exact h u

/-- The largest exponent of `e_j` on `r` lane variables is `2^(j+r) - 2^j`. -/
theorem exL_add_le : ∀ (r j : ℕ) (u : Lane r), exL j r u + 2 ^ j ≤ 2 ^ (j + r)
  | 0, j, _ => by simp [exL]
  | r + 1, j, u => by
      have h : ∀ v : Lane r, exL (j + 1) r v + 2 ^ (j + 1) ≤ 2 ^ (j + (r + 1)) := fun v => by
        have := exL_add_le r (j + 1) v
        rwa [show j + 1 + r = j + (r + 1) by omega] at this
      have h2 : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [pow_succ]; omega
      have h3 : 0 < 2 ^ j := pow_pos (by norm_num) j
      rcases u with u | u
      · have := h u
        simp only [exL_succ, Sum.elim_inl]
        omega
      · have := h u
        simp only [exL_succ, Sum.elim_inr]
        omega

/-- The exponents of `e_j` are pairwise distinct (binary digits): the hypothesis `hex` of
`DeepFold`. -/
theorem exL_injective : ∀ (r j : ℕ), Function.Injective (exL j r)
  | 0, _ => fun u v _ => Subsingleton.elim (α := Unit) u v
  | r + 1, j => by
      have hodd : ∀ u v : Lane r, 2 ^ j + exL (j + 1) r u ≠ exL (j + 1) r v := by
        intro u v h
        obtain ⟨a, ha⟩ := two_pow_dvd_exL r (j + 1) u
        obtain ⟨b, hb⟩ := two_pow_dvd_exL r (j + 1) v
        rw [ha, hb, pow_succ] at h
        have h' : 2 ^ j * (1 + 2 * a) = 2 ^ j * (2 * b) := by
          rw [mul_add, mul_one, ← mul_assoc, ← mul_assoc]
          exact h
        have := Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num : 0 < 2) j) h'
        omega
      intro u v h
      rcases u with u | u <;> rcases v with v | v
      · simp only [exL_succ, Sum.elim_inl] at h
        exact congrArg Sum.inl (exL_injective r (j + 1) (Nat.add_left_cancel h))
      · simp only [exL_succ, Sum.elim_inl, Sum.elim_inr] at h
        exact absurd h (hodd u v)
      · simp only [exL_succ, Sum.elim_inl, Sum.elim_inr] at h
        exact absurd h.symm (hodd v u)
      · simp only [exL_succ, Sum.elim_inr] at h
        exact congrArg Sum.inr (exL_injective r (j + 1) h)

variable {K : Type*} [Field K]

/-- (E2) of Lemma 4.4 of the paper for the exponents `e_j`:
`ev^{(j)}_z(U) = θ^(2^j) ev^{(j+1)}_z(F) + ev^{(j+1)}_z(G)` for the halves `F`, `G` of `U`. -/
theorem evL_exL_halves (j r : ℕ) (z : K × K) (U : Lane (r + 1) → K[X]) :
    evL (exL j (r + 1)) z U =
      z.1 ^ 2 ^ j * evL (exL (j + 1) r) z (fun u => U (Sum.inl u)) +
        evL (exL (j + 1) r) z (fun u => U (Sum.inr u)) :=
  evL_halves (exL (j + 1) r) (2 ^ j) z U

/-- An interleaved word with `r` lane variables: a value for each column `x` and lane. -/
abbrev Word (K : Type*) (r : ℕ) := K → Lane r → K

section Halves

variable {ι : Type*}

/-- The half `O₀` of a word: the lanes whose folded variable is `0`. -/
def half₀ (O : K → ι ⊕ ι → K) : K → ι → K := fun x u => O x (Sum.inl u)

/-- The half `O₁` of a word: the lanes whose folded variable is `1`. -/
def half₁ (O : K → ι ⊕ ι → K) : K → ι → K := fun x u => O x (Sum.inr u)

/-- The fold `O_c = O₁ + a_c O₀` of a word by the challenge `c = (α, β)`. No prover message
enters. -/
def foldW (O : K → ι ⊕ ι → K) (c : K × K) : K → ι → K := foldPair (half₀ O) (half₁ O) c

theorem foldW_apply (O : K → ι ⊕ ι → K) (c : K × K) (x : K) (u : ι) :
    foldW O c x u = O x (Sum.inr u) + (c.1 + c.2 * x) * O x (Sum.inl u) := rfl

end Halves

variable [Fintype K]

/-- `Exc_{k+1}(O)` of Definition 4.8 of the paper with threshold `B`, for a word `O` of a level
that has been folded `k` times and has `r + 1` lane variables left: the exceptional set of the
candidates `𝒯` of `O` at the agreement `thr (k + 1)`, with the exponents `e_{k+1}`. -/
noncomputable def excW (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (s B k r : ℕ)
    (O : Word K (r + 1)) : Finset (Fin s → K × K) :=
  ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) s B

/-- The potential `Ψ_k` of Lemma 4.12 of the paper for a level with one batch, with the indicator
of the exceptional set as the cost of a round: a function of the word `O` (the committed word
folded by the `k` challenges so far, `r` rounds to come), the points `z` and nothing else. -/
noncomputable def levelPot (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (s B : ℕ)
    (z : Fin s → K × K) : ℕ → ∀ r : ℕ, Word K r → ℚ :=
  potT (A := fun _ r => Word K r) (C := fun _ _ => K × K) τ (fun _ _ O c => foldW O c)
    (fun k r O z => z ∈ excW D d thr s B k r O) z

variable {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {s B : ℕ}

/-- `Ψ_ℓ = 0`. -/
@[simp] theorem levelPot_zero (z : Fin s → K × K) (k : ℕ) (O : Word K 0) :
    levelPot τ D d thr s B z k 0 O = 0 := rfl

/-- The recursion that defines the potential: the indicator that the points are exceptional for
the current word, plus `τ⁻¹` times the mean over the next challenge. -/
theorem levelPot_succ (z : Fin s → K × K) (k r : ℕ) (O : Word K (r + 1)) :
    levelPot τ D d thr s B z k (r + 1) O = (if z ∈ excW D d thr s B k r O then 1 else 0) +
      τ⁻¹ * avg (fun c : K × K => levelPot τ D d thr s B z (k + 1) r (foldW O c)) := by
  unfold levelPot
  rw [potT_succ]
  by_cases hz : z ∈ excW D d thr s B k r O <;> simp [hz]

/-- The potential as the sum of equation (8) of the paper: `Ψ_k = ∑_j τ^(-j) π_j`, where `π_j` is
the probability over the next `j` challenges that `z` is exceptional for the word they lead to. -/
theorem levelPot_eq_sum (z : Fin s → K × K) (k r : ℕ) (O : Word K r) :
    levelPot τ D d thr s B z k r O = ∑ j ∈ range r, τ⁻¹ ^ j *
      probBad (A := fun _ r => Word K r) (C := fun _ _ => K × K) (fun _ _ O c => foldW O c)
        (fun k r O z => z ∈ excW D d thr s B k r O) z j k r O :=
  potT_eq_sum (A := fun _ r => Word K r) (C := fun _ _ => K × K) z k r O

/-- The same with `π_j` as a count: the number of sequences of `j` challenges that lead to a
word for which `z` is exceptional, over `(q^2)^j`. This is the sum of equation (8) of the paper,
with `j = 0` the current round. -/
theorem levelPot_eq_sum_card (z : Fin s → K × K) (k r : ℕ) (O : Word K r) :
    levelPot τ D d thr s B z k r O = ∑ j ∈ range r, τ⁻¹ ^ j *
      ((badSeqs (A := fun _ r => Word K r) (C := fun _ _ => K × K) (fun _ _ O c => foldW O c)
        (fun k r O z => z ∈ excW D d thr s B k r O) z j k r O : ℚ) /
          ((Fintype.card K : ℚ) ^ 2) ^ j) := by
  rw [levelPot_eq_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [probBad_eq_card (A := fun _ r => Word K r) (C := fun _ _ => K × K)
    (Q := Fintype.card K ^ 2) (fun _ _ => by rw [Fintype.card_prod, sq])]
  push_cast
  rfl

theorem levelPot_nonneg (hτ : 0 ≤ τ) (z : Fin s → K × K) (k r : ℕ) (O : Word K r) :
    0 ≤ levelPot τ D d thr s B z k r O :=
  potT_nonneg (A := fun _ r => Word K r) (C := fun _ _ => K × K) hτ z k r O

/-- Lemma 4.12(b) of the paper for a level with one batch. The points `z` are fixed, `O` is the
committed word folded by the `k` challenges so far. If `Ψ_k < 1`, then `z` is outside the
exceptional set of Lemma 4.10 for the current round's word, in the form `lemmaF_round` takes, and
the next challenge makes `Ψ_{k+1} ≥ 1` with probability less than `τ`. -/
theorem levelPot_step (hτ : 0 < τ) {z : Fin s → K × K} {k r : ℕ} {O : Word K (r + 1)}
    (h : levelPot τ D d thr s B z k (r + 1) O < 1) :
    z ∉ ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) s B ∧
      dens (fun c : K × K => 1 ≤ levelPot τ D d thr s B z (k + 1) r (foldW O c)) < τ :=
  potT_step (A := fun _ r => Word K r) (C := fun _ _ => K × K) hτ h

/-- The exceptional set of one round has density at most `L^3 q^6 ε^s / B` when the lists of
the folds have at most `L` members: Lemma 4.10(1) of the paper for a word of the level. -/
theorem dens_excW_le (hB : 0 < B) {L : ℕ} {E k r : ℕ} (hE : 2 ^ (k + 1 + r) ≤ E + 2 ^ (k + 1))
    (O : Word K (r + 1))
    (hL : ∀ c : K × K, (listW D (foldW O c) d (thr (k + 1))).card ≤ L) :
    dens (fun z : Fin s → K × K => z ∈ excW D d thr s B k r O) ≤
      (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s / B := by
  rw [dens_mem]
  refine lemmaF_exc D (half₀ O) (half₁ O) d (thr (k + 1)) (exL_injective r (k + 1))
    (fun u => ?_) L (fullT_fiber_le D _ _ d _ hL) s hB
  have := exL_add_le r (k + 1) u
  omega

/-- Lemma 4.12(a) of the paper for a level with one batch. `O` is a word folded `k` times with `r`
rounds to come (the committed word is `k = 0`, `r = ℓ`). If every word folded `k' > k` times has
at most `L` list members at the agreement `thr k'` (the hypothesis `ListBound`), then over `s`
independent uniform points `Ψ_k ≥ 1` with probability at most `ε_* ∑_{j < r} τ^(-j)`, where
`ε_* = L^3 q^6 ε^s / B` and `ε = (d + 1 + 2^(k+r) - 2^(k+1)) / q`. -/
theorem levelPot_init (hτ : 0 ≤ τ) (hB : 0 < B) {L : ℕ} (k r : ℕ)
    (hL : ∀ k' r', k' + r' = k + r → k < k' → ∀ O' : Word K r',
      (listW D O' d (thr k')).card ≤ L) (O : Word K r) :
    dens (fun z : Fin s → K × K => 1 ≤ levelPot τ D d thr s B z k r O) ≤
      (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + (2 ^ (k + r) - 2 ^ (k + 1)) : ℕ) : ℚ) / Fintype.card K) ^ s / B *
          ∑ j ∈ range r, τ⁻¹ ^ j := by
  refine potT_init_const (A := fun _ r => Word K r) (C := fun _ _ => K × K) hτ k r ?_ O
  intro k' r' hkk hsum O'
  refine dens_excW_le hB ?_ O' (fun c => hL (k' + 1) r' (by omega) (by omega) _)
  have h1 : 2 ^ (k + 1) ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (k' + 1) ≤ 2 ^ (k' + 1 + r') := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show k + r = k' + 1 + r' by omega]
  omega

/-- The hypothesis `ListBound_i(L)` (Hypothesis 5.1 of the paper), in the form the statements here
take it. If every word with at most `ℓ` lane variables has at most `L` list members at the agreement
`A₀` (`A^{(i,0)}`), and no threshold of the level is below `A₀`, then every word of the level folded
`k` times has at most `L` list members at its own threshold `thr k`. -/
theorem listBound_level {L ℓ A₀ : ℕ}
    (hLB : ∀ r, r ≤ ℓ → ∀ O' : Word K r, (listW D O' d A₀).card ≤ L) (hthr : ∀ k, A₀ ≤ thr k) :
    ∀ k r, k + r = ℓ → ∀ O' : Word K r, (listW D O' d (thr k)).card ≤ L :=
  fun k r hkr O' => (card_listW_le D O' d (hthr k)).trans (hLB r (by omega) O')

/-- The points `z` are good for the committed word `O` of a level with `ℓ` lane variables
(Section 5.3 of the paper): they separate `List(O; thr 0, d)` and the potential `Ψ_0` is below
one. -/
def Good (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (s B ℓ : ℕ) (O : Word K ℓ)
    (z : Fin s → K × K) : Prop :=
  z ∉ NonSep (listW D O d (thr 0)) (exL 0 ℓ) s ∧ levelPot τ D d thr s B z 0 ℓ O < 1

/-- The error of the point message (row M0 of Theorem 5.2 of the paper, one batch): if every word
of the level folded `k` times has at most `L` list members at the agreement `thr k`, the points
fail to be good for the committed word with probability at most
`[C(L, 2) + L^3 q^6 / B · ∑_{j < ℓ} τ^(-j)] ε^s`, `ε = (d + 2^ℓ - 1) / q`. -/
theorem dens_not_good_le (hτ : 0 ≤ τ) (hB : 0 < B) {L ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hL : ∀ k r, k + r = ℓ → ∀ O' : Word K r, (listW D O' d (thr k)).card ≤ L)
    (O : Word K ℓ) :
    dens (fun z : Fin s → K × K => ¬ Good τ D d thr s B ℓ O z) ≤
      ((L.choose 2 : ℚ) + (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 / B *
          ∑ j ∈ range ℓ, τ⁻¹ ^ j) * (((d + 2 ^ ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ s := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hP := lemmaP D O d (thr 0) (exL_injective ℓ 0) (E := 2 ^ ℓ - 1)
    (fun u => by
      have := exL_add_le ℓ 0 u
      simp only [pow_zero, zero_add] at this
      omega) (hL 0 ℓ (by omega) O) s
  have hT := levelPot_init (τ := τ) (D := D) (d := d) (thr := thr) (s := s) hτ hB 0 ℓ
    (fun k' r' hsum _ O' => hL k' r' (by omega) O') O
  rw [show d + (2 ^ ℓ - 1) = d + 2 ^ ℓ - 1 by omega] at hP
  rw [show d + 1 + (2 ^ (0 + ℓ) - 2 ^ (0 + 1)) = d + 2 ^ ℓ - 1 by
    simp only [zero_add, pow_one]; omega] at hT
  have hsub : dens (fun z : Fin s → K × K => ¬ Good τ D d thr s B ℓ O z) ≤
      dens (fun z : Fin s → K × K => z ∈ NonSep (listW D O d (thr 0)) (exL 0 ℓ) s ∨
        1 ≤ levelPot τ D d thr s B z 0 ℓ O) := by
    apply dens_mono
    intro z hz
    by_contra hcon
    push Not at hcon
    exact hz ⟨hcon.1, hcon.2⟩
  refine (hsub.trans (dens_or_le _ _)).trans ((add_le_add hP hT).trans_eq ?_)
  ring

end Protocol
