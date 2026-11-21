/-
Lemma 4.12 of the paper for a schedule (the ladder potential, Section 4.8): fresh points are added
before later rounds, in the same verifier message as the previous fold challenge, and every round
uses all points sampled so far.

The state after a verifier message is the pair (current word, points held), the message of round
`k + 1` is the pair (fold challenge, batch of `bt k` fresh points), and the cost of a round is
`N / B`: the number of triples of Definition 4.8 that vanish at all points held, over the
threshold. The potential is `Protocol.pot` for this process, so Lemma 4.12(b) is `pot_step`, and
Lemma 4.12(a) is the exchange of means below.
-/
import Protocol.Level

open Polynomial Finset
open scoped Classical

namespace Protocol

open DeepFold

section Abstract

variable {A : ℕ → ℕ → Type*} {C : ℕ → ℕ → Type*} [∀ k r, Fintype (C k r)]
  {Pt : Type*} [Fintype Pt]

/-- The potential of Lemma 4.12 of the paper for a schedule. The state is `(a, pts)`: the word `a`
folded by the challenges so far and the list `pts` of all points sampled so far. The verifier
message of the round played from `a : A k (r + 1)` is `(c, p)`: a fold challenge and `bt k` fresh
points, after which the state is `(fold a c, pts ++ p)`. `cost k r a pts ≥ 0` is the cost of that
round with the points `pts` (in the paper, `N_j / Θ`). -/
noncomputable def potS (τ : ℚ) (fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r) (bt : ℕ → ℕ)
    (cost : ∀ k r, A k (r + 1) → List Pt → ℚ) : ∀ (k r : ℕ), A k r × List Pt → ℚ :=
  pot (H := fun k r => A k r × List Pt) (M := fun k r => C k r × (Fin (bt k) → Pt)) τ
    (fun k r h m => (fold k r h.1 m.1, h.2 ++ List.ofFn m.2)) (fun k r h => cost k r h.1 h.2)

variable {τ : ℚ} {fold : ∀ k r, A k (r + 1) → C k r → A (k + 1) r} {bt : ℕ → ℕ}
  {cost : ∀ k r, A k (r + 1) → List Pt → ℚ}

@[simp] theorem potS_zero (k : ℕ) (h : A k 0 × List Pt) : potS τ fold bt cost k 0 h = 0 := rfl

theorem potS_succ (k r : ℕ) (a : A k (r + 1)) (pts : List Pt) :
    potS τ fold bt cost k (r + 1) (a, pts) = cost k r a pts +
      τ⁻¹ * avg (fun m : C k r × (Fin (bt k) → Pt) =>
        potS τ fold bt cost (k + 1) r (fold k r a m.1, pts ++ List.ofFn m.2)) := rfl

theorem potS_nonneg (hτ : 0 ≤ τ) (hc : ∀ k r a pts, 0 ≤ cost k r a pts) (k r : ℕ)
    (h : A k r × List Pt) : 0 ≤ potS τ fold bt cost k r h :=
  pot_nonneg (H := fun k r => A k r × List Pt) (M := fun k r => C k r × (Fin (bt k) → Pt)) hτ
    (fun k r h => hc k r h.1 h.2) r k h

/-- Lemma 4.12(b) of the paper for a schedule. If the potential is below one before the round
played from `a` with the points `pts`, then the cost of that round is below one, and the next
verifier message (a fold challenge with its batch of fresh points) brings the potential to one or
more with probability less than `τ`. -/
theorem potS_step (hτ : 0 < τ) (hc : ∀ k r a pts, 0 ≤ cost k r a pts) {k r : ℕ}
    {a : A k (r + 1)} {pts : List Pt} (h : potS τ fold bt cost k (r + 1) (a, pts) < 1) :
    cost k r a pts < 1 ∧
      dens (fun m : C k r × (Fin (bt k) → Pt) =>
        1 ≤ potS τ fold bt cost (k + 1) r (fold k r a m.1, pts ++ List.ofFn m.2)) < τ :=
  pot_step (H := fun k r => A k r × List Pt) (M := fun k r => C k r × (Fin (bt k) → Pt)) hτ
    (fun k r h => hc k r h.1 h.2) h

/-- Two independent uniform batches of `n` and `m` points are one uniform batch of `n + m`. -/
theorem avg_ofFn_append (n m : ℕ) (G : List Pt → ℚ) :
    avg (fun p : Fin n → Pt => avg (fun p' : Fin m → Pt => G (List.ofFn p ++ List.ofFn p'))) =
      avg (fun q : Fin (n + m) → Pt => G (List.ofFn q)) := by
  rw [← avg_equiv (Fin.appendEquiv n m) (fun q => G (List.ofFn q)),
    avg_prod (fun pp : (Fin n → Pt) × (Fin m → Pt) => G (List.ofFn (Fin.appendEquiv n m pp)))]
  simp only [Fin.appendEquiv, Equiv.coe_fn_mk, List.ofFn_fin_append]

/-- The number of points held at the round played `j` messages after a round with `n` points:
`σ = n + bt k + … + bt (k + j - 1)`. -/
def held (bt : ℕ → ℕ) (k n j : ℕ) : ℕ := n + ∑ i ∈ range j, bt (k + i)

theorem held_zero (bt : ℕ → ℕ) (k n : ℕ) : held bt k n 0 = n := by simp [held]

theorem held_succ (bt : ℕ → ℕ) (k n j : ℕ) :
    held bt k n (j + 1) = held bt (k + 1) (n + bt k) j := by
  simp only [held, sum_range_succ', Nat.add_zero]
  rw [show ∑ i ∈ range j, bt (k + (i + 1)) = ∑ i ∈ range j, bt (k + 1 + i) from
    sum_congr rfl (fun i _ => by rw [show k + (i + 1) = k + 1 + i by omega])]
  omega

variable [∀ k r, Nonempty (C k r)]

/-- The mean of the ladder potential over the points held, all uniform and independent. The
hypothesis bounds the mean cost of every round to come, for every word of its shape and every
number `n` of uniform points. -/
theorem avg_potS_le (hτ : 0 ≤ τ) (e : ℕ → ℕ → ℕ → ℚ) :
    ∀ (r k : ℕ), (∀ k' r', k ≤ k' → k' + r' + 1 = k + r → ∀ (a : A k' (r' + 1)) (n : ℕ),
        avg (fun p : Fin n → Pt => cost k' r' a (List.ofFn p)) ≤ e k' r' n) →
      ∀ (a : A k r) (n : ℕ),
        avg (fun p : Fin n → Pt => potS τ fold bt cost k r (a, List.ofFn p)) ≤
          ∑ j ∈ range r, τ⁻¹ ^ j * e (k + j) (r - 1 - j) (held bt k n j)
  | 0, _, _, _, n => by
      rw [range_zero, sum_empty]
      exact le_of_eq (avg_zero (α := Fin n → Pt))
  | r + 1, k, he, a, n => by
      have hfun : (fun p : Fin n → Pt => potS τ fold bt cost k (r + 1) (a, List.ofFn p)) =
          fun p => cost k r a (List.ofFn p) +
            τ⁻¹ * avg (fun m : C k r × (Fin (bt k) → Pt) =>
              potS τ fold bt cost (k + 1) r (fold k r a m.1, List.ofFn p ++ List.ofFn m.2)) :=
        funext fun _ => potS_succ k r a _
      rw [hfun, avg_add, avg_mul_left, sum_range_succ']
      simp only [pow_zero, one_mul, add_zero, Nat.add_sub_cancel, Nat.sub_zero, held_zero]
      rw [add_comm]
      refine add_le_add ?_ (he k r le_rfl rfl a n)
      have hswap : avg (fun p : Fin n → Pt => avg (fun m : C k r × (Fin (bt k) → Pt) =>
            potS τ fold bt cost (k + 1) r (fold k r a m.1, List.ofFn p ++ List.ofFn m.2))) =
          avg (fun c : C k r => avg (fun q : Fin (n + bt k) → Pt =>
            potS τ fold bt cost (k + 1) r (fold k r a c, List.ofFn q))) := by
        have h1 : ∀ p : Fin n → Pt, avg (fun m : C k r × (Fin (bt k) → Pt) =>
              potS τ fold bt cost (k + 1) r (fold k r a m.1, List.ofFn p ++ List.ofFn m.2)) =
            avg (fun c : C k r => avg (fun p' : Fin (bt k) → Pt =>
              potS τ fold bt cost (k + 1) r (fold k r a c, List.ofFn p ++ List.ofFn p'))) :=
          fun p => avg_prod _
        simp only [h1]
        rw [avg_comm]
        exact congrArg avg (funext fun c => avg_ofFn_append n (bt k)
          (fun l => potS τ fold bt cost (k + 1) r (fold k r a c, l)))
      have hrec : ∀ c : C k r, avg (fun q : Fin (n + bt k) → Pt =>
            potS τ fold bt cost (k + 1) r (fold k r a c, List.ofFn q)) ≤
          ∑ j ∈ range r, τ⁻¹ ^ j * e (k + 1 + j) (r - 1 - j) (held bt (k + 1) (n + bt k) j) :=
        fun c => avg_potS_le hτ e r (k + 1)
          (fun k' r' hk hs => he k' r' (by omega) (by omega)) (fold k r a c) (n + bt k)
      rw [hswap]
      calc τ⁻¹ * avg (fun c : C k r => avg (fun q : Fin (n + bt k) → Pt =>
              potS τ fold bt cost (k + 1) r (fold k r a c, List.ofFn q)))
          ≤ τ⁻¹ * ∑ j ∈ range r,
              τ⁻¹ ^ j * e (k + 1 + j) (r - 1 - j) (held bt (k + 1) (n + bt k) j) :=
            mul_le_mul_of_nonneg_left ((avg_mono hrec).trans_eq (avg_const _))
              (inv_nonneg.mpr hτ)
        _ = ∑ j ∈ range r,
              τ⁻¹ ^ (j + 1) * e (k + (j + 1)) (r - (j + 1)) (held bt k n (j + 1)) := by
            rw [mul_sum]
            refine sum_congr rfl (fun j _ => ?_)
            rw [show k + 1 + j = k + (j + 1) by omega, show r - 1 - j = r - (j + 1) by omega,
              pow_succ, held_succ]
            ring

/-- Lemma 4.12(a) of the paper for a schedule. `a` is the committed word and the `n` points of the
first batch are uniform. If the mean cost of the round `(k', r')` played with `n'` uniform points
is at most `e k' r' n'`, the potential is one or more after the first batch with probability at
most `∑_j τ^(-j) e_j(σ_j)`, where `σ_j = held bt k n j` is the number of points held at that
round. -/
theorem potS_init (hτ : 0 ≤ τ) (hc : ∀ k r a pts, 0 ≤ cost k r a pts) (e : ℕ → ℕ → ℕ → ℚ)
    (k r : ℕ)
    (he : ∀ k' r', k ≤ k' → k' + r' + 1 = k + r → ∀ (a : A k' (r' + 1)) (n : ℕ),
      avg (fun p : Fin n → Pt => cost k' r' a (List.ofFn p)) ≤ e k' r' n)
    (a : A k r) (n : ℕ) :
    dens (fun p : Fin n → Pt => 1 ≤ potS τ fold bt cost k r (a, List.ofFn p)) ≤
      ∑ j ∈ range r, τ⁻¹ ^ j * e (k + j) (r - 1 - j) (held bt k n j) :=
  (dens_le_avg fun _ => potS_nonneg hτ hc k r _).trans (avg_potS_le hτ e r k he a n)

end Abstract

section Level

variable {K : Type*} [Field K] [Fintype K]

/-- `N`: the number of ordered triples of `T` with pairwise different challenges, `Δ ≠ 0`, and
`ev_z(Δ) = 0` at every point `z` of the list `pts` (the count that defines `ExcL`). -/
noncomputable def NcountL {ι : Type*} [Fintype ι] (T : Finset (CandL ι K)) (ex : ι → ℕ)
    (pts : List (K × K)) : ℕ :=
  Ncount T DepL (fun e₁ e₂ e₃ z => evL ex z (DeltaL e₁ e₂ e₃) = 0)
    (fun i : Fin pts.length => pts.get i)

/-- A list of points is outside the exceptional set of Definition 4.8 of the paper exactly when its
count is below the threshold. -/
theorem not_mem_ExcL_iff {ι : Type*} [Fintype ι] (T : Finset (CandL ι K)) (ex : ι → ℕ) (B : ℕ)
    (pts : List (K × K)) :
    (fun i : Fin pts.length => pts.get i) ∉ ExcL T ex pts.length B ↔ NcountL T ex pts < B := by
  simp [ExcL, Exc, NcountL]

omit [Fintype K] in
/-- The count of a list of points given by a vector is the count `Ncount` of that vector. -/
theorem NcountL_ofFn {ι : Type*} [Fintype ι] (T : Finset (CandL ι K)) (ex : ι → ℕ) {n : ℕ}
    (p : Fin n → K × K) :
    NcountL T ex (List.ofFn p) =
      Ncount T DepL (fun e₁ e₂ e₃ z => evL ex z (DeltaL e₁ e₂ e₃) = 0) p := by
  unfold NcountL Ncount
  congr 1
  refine filter_congr (fun t _ => and_congr_right (fun _ => ?_))
  constructor
  · intro h j
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ((List.mem_ofFn' p (p j)).mpr ⟨j, rfl⟩)
    rw [← hi]
    exact h i
  · intro h i
    obtain ⟨j, hj⟩ := (List.mem_ofFn' p _).mp (List.get_mem (List.ofFn p) i)
    show evL ex ((List.ofFn p).get i) _ = 0
    rw [← hj]
    exact h j

/-- The mean of `N` over `n` independent uniform points is at most `L^3 q^6 ε^n` when the lists
of the folds have at most `L` members: the expectation in the proof of Theorem 4.9(1) of the
paper. -/
theorem avg_NcountL_le {ι : Type*} [Fintype ι] (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ)
    {ex : ι → ℕ} (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) {L : ℕ}
    (hL : ∀ c : K × K, (listW D (foldPair O₀ O₁ c) d A).card ≤ L) (n : ℕ) :
    avg (fun p : Fin n → K × K => (NcountL (fullT D O₀ O₁ d A) ex (List.ofFn p) : ℚ)) ≤
      (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ n := by
  have hq : (0 : ℚ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have h1 : (∑ p : Fin n → K × K, (NcountL (fullT D O₀ O₁ d A) ex (List.ofFn p) : ℚ)) ≤
      ((fullT D O₀ O₁ d A).card : ℚ) ^ 3 * (((d + 1 + E : ℕ) : ℚ) * Fintype.card K) ^ n := by
    have h := sum_Ncount_le (fullT D O₀ O₁ d A) DepL
      (fun e₁ e₂ e₃ z => evL ex z (DeltaL e₁ e₂ e₃) = 0)
      (deltaL_zeros_le hex hE (fullT_natDegree_le D O₀ O₁ d A)) n
    simp only [NcountL_ofFn]
    exact_mod_cast h
  have h2 : ((fullT D O₀ O₁ d A).card : ℚ) ≤ (L : ℚ) * (Fintype.card K : ℚ) ^ 2 := by
    exact_mod_cast card_T_le (fullT D O₀ O₁ d A) (fun e => e.1) L
      (fullT_fiber_le D O₀ O₁ d A hL)
  have h3 : ((fullT D O₀ O₁ d A).card : ℚ) ^ 3 ≤ (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 := by
    calc ((fullT D O₀ O₁ d A).card : ℚ) ^ 3 ≤ ((L : ℚ) * (Fintype.card K : ℚ) ^ 2) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h2 3
      _ = (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 := by ring
  have hcard : (Fintype.card (Fin n → K × K) : ℚ) = ((Fintype.card K : ℚ) ^ 2) ^ n := by
    simp [Fintype.card_prod, sq]
  unfold avg
  rw [hcard, div_le_iff₀ (by positivity)]
  refine h1.trans ((mul_le_mul_of_nonneg_right h3 (by positivity)).trans_eq ?_)
  rw [div_pow, mul_pow]
  field_simp
  ring

/-- The cost of a round of the ladder: `N / B`, for the word `O` folded `k` times with `r + 1`
lane variables left and the points `pts` held. -/
noncomputable def ladderCost (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (B k r : ℕ)
    (O : Word K (r + 1)) (pts : List (K × K)) : ℚ :=
  (NcountL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) pts : ℚ) / B

/-- The potential `Ψ` of Lemma 4.12 of the paper (equation (8)) for a level and a schedule, with
the threshold `B`: a function of the current word, the points held, and nothing else. `bt k` is
the number of fresh points sent with the fold challenge of round `k + 1`. -/
noncomputable def ladderPot (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (bt : ℕ → ℕ) (B : ℕ) :
    ℕ → ∀ r : ℕ, Word K r × List (K × K) → ℚ :=
  potS (A := fun _ r => Word K r) (C := fun _ _ => K × K) τ (fun _ _ O c => foldW O c) bt
    (ladderCost D d thr B)

variable {τ : ℚ} {D : Finset K} {d : ℕ} {thr : ℕ → ℕ} {bt : ℕ → ℕ} {B : ℕ}

@[simp] theorem ladderPot_zero (k : ℕ) (h : Word K 0 × List (K × K)) :
    ladderPot τ D d thr bt B k 0 h = 0 := rfl

theorem ladderPot_succ (k r : ℕ) (O : Word K (r + 1)) (pts : List (K × K)) :
    ladderPot τ D d thr bt B k (r + 1) (O, pts) = ladderCost D d thr B k r O pts +
      τ⁻¹ * avg (fun m : (K × K) × (Fin (bt k) → K × K) =>
        ladderPot τ D d thr bt B (k + 1) r (foldW O m.1, pts ++ List.ofFn m.2)) := rfl

theorem ladderCost_nonneg (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (B k r : ℕ)
    (O : Word K (r + 1)) (pts : List (K × K)) : 0 ≤ ladderCost D d thr B k r O pts :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Lemma 4.12(b) of the paper for a level and a schedule. If the potential is below one before the
round played from the word `O` with the points `pts` held, then these points are outside the
exceptional set of Lemma 4.10 for `O`, in the form `lemmaF_round` takes, and the next verifier
message (the fold challenge and its `bt k` fresh points) makes the potential one or more with
probability less than `τ`. -/
theorem ladderPot_step (hτ : 0 < τ) (hB : 0 < B) {k r : ℕ} {O : Word K (r + 1)}
    {pts : List (K × K)} (h : ladderPot τ D d thr bt B k (r + 1) (O, pts) < 1) :
    (fun i : Fin pts.length => pts.get i) ∉
        ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) pts.length B ∧
      dens (fun m : (K × K) × (Fin (bt k) → K × K) =>
        1 ≤ ladderPot τ D d thr bt B (k + 1) r (foldW O m.1, pts ++ List.ofFn m.2)) < τ := by
  obtain ⟨h1, h2⟩ := potS_step (A := fun _ r => Word K r) (C := fun _ _ => K × K) hτ
    (ladderCost_nonneg D d thr B) h
  refine ⟨(not_mem_ExcL_iff _ _ _ _).mpr ?_, h2⟩
  have hB' : (0 : ℚ) < B := by exact_mod_cast hB
  unfold ladderCost at h1
  rw [div_lt_one hB'] at h1
  exact_mod_cast h1

/-- Lemma 4.12(a) of the paper for a level and a schedule. `O` is a word folded `k` times with `r`
rounds to come (the committed word is `k = 0`, `r = ℓ`) and the `n` points of the first batch are
uniform. If every word folded `k' > k` times has at most `L` list members at the agreement
`thr k'`, the potential is one or more with probability at most
`(L^3 q^6 / B) ∑_{j < r} τ^(-j) ε^(σ_j)`, `σ_j = held bt k n j` the number of points held at the
round played `j` messages later. -/
theorem ladderPot_init (hτ : 0 ≤ τ) {L : ℕ} (k r : ℕ)
    (hL : ∀ k' r', k' + r' = k + r → k < k' → ∀ O' : Word K r',
      (listW D O' d (thr k')).card ≤ L) (O : Word K r) (n : ℕ) :
    dens (fun p : Fin n → K × K => 1 ≤ ladderPot τ D d thr bt B k r (O, List.ofFn p)) ≤
      ∑ j ∈ range r, τ⁻¹ ^ j * ((L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + (2 ^ (k + r) - 2 ^ (k + 1)) : ℕ) : ℚ) / Fintype.card K) ^ held bt k n j /
          B) := by
  refine potS_init (A := fun _ r => Word K r) (C := fun _ _ => K × K) hτ
    (ladderCost_nonneg D d thr B)
    (fun _ _ n' => (L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
      (((d + 1 + (2 ^ (k + r) - 2 ^ (k + 1)) : ℕ) : ℚ) / Fintype.card K) ^ n' / B) k r ?_ O n
  intro k' r' hkk hsum O' n'
  have hE : ∀ u : Lane r', exL (k' + 1) r' u ≤ 2 ^ (k + r) - 2 ^ (k + 1) := by
    intro u
    have h0 := exL_add_le r' (k' + 1) u
    have h1 : 2 ^ (k + 1) ≤ 2 ^ (k' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [show k + r = k' + 1 + r' by omega]
    omega
  have h := avg_NcountL_le D (half₀ O') (half₁ O') d (thr (k' + 1))
    (exL_injective r' (k' + 1)) hE (fun c => hL (k' + 1) r' (by omega) (by omega) _) n'
  unfold ladderCost
  have hfun : (fun p : Fin n' → K × K =>
      (NcountL (fullT D (half₀ O') (half₁ O') d (thr (k' + 1))) (exL (k' + 1) r')
        (List.ofFn p) : ℚ) / B) = fun p => (B : ℚ)⁻¹ *
      (NcountL (fullT D (half₀ O') (half₁ O') d (thr (k' + 1))) (exL (k' + 1) r')
        (List.ofFn p) : ℚ) := funext fun p => by rw [div_eq_inv_mul]
  rw [hfun, avg_mul_left, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- The points of the first batch are good for the committed word `O` on the ladder: they
separate `List(O; thr 0, d)` and the ladder potential is below one. -/
def GoodS (τ : ℚ) (D : Finset K) (d : ℕ) (thr : ℕ → ℕ) (bt : ℕ → ℕ) (B ℓ : ℕ) (O : Word K ℓ)
    {n : ℕ} (p : Fin n → K × K) : Prop :=
  p ∉ NonSep (listW D O d (thr 0)) (exL 0 ℓ) n ∧
    ladderPot τ D d thr bt B 0 ℓ (O, List.ofFn p) < 1

/-- The error of the first point message on the ladder (row M0 of Theorem 5.2 of the paper for a
schedule): the `n = s_1` points fail to be good with probability at most
`C(L, 2) ε^(σ_1) + (L^3 q^6 / B) ∑_{j < ℓ} τ^(-j) ε^(σ_{j+1})`, `ε = (d + 2^ℓ - 1) / q`,
`σ_{j+1} = held bt 0 n j`. -/
theorem dens_not_goodS_le (hτ : 0 ≤ τ) {L ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hL : ∀ k r, k + r = ℓ → ∀ O' : Word K r, (listW D O' d (thr k)).card ≤ L)
    (O : Word K ℓ) (n : ℕ) :
    dens (fun p : Fin n → K × K => ¬ GoodS τ D d thr bt B ℓ O p) ≤
      (L.choose 2 : ℚ) * (((d + 2 ^ ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ n +
        ∑ j ∈ range ℓ, τ⁻¹ ^ j * ((L : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
          (((d + 2 ^ ℓ - 1 : ℕ) : ℚ) / Fintype.card K) ^ held bt 0 n j / B) := by
  have h2 : 2 ≤ 2 ^ ℓ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hℓ
  have hP := lemmaP D O d (thr 0) (exL_injective ℓ 0) (E := 2 ^ ℓ - 1)
    (fun u => by
      have := exL_add_le ℓ 0 u
      simp only [pow_zero, zero_add] at this
      omega) (hL 0 ℓ (by omega) O) n
  have hT := ladderPot_init (τ := τ) (D := D) (d := d) (thr := thr) (bt := bt) (B := B) hτ 0 ℓ
    (fun k' r' hsum _ O' => hL k' r' (by omega) O') O n
  rw [show d + (2 ^ ℓ - 1) = d + 2 ^ ℓ - 1 by omega] at hP
  rw [show d + 1 + (2 ^ (0 + ℓ) - 2 ^ (0 + 1)) = d + 2 ^ ℓ - 1 by
    simp only [zero_add, pow_one]; omega] at hT
  have hsub : dens (fun p : Fin n → K × K => ¬ GoodS τ D d thr bt B ℓ O p) ≤
      dens (fun p : Fin n → K × K => p ∈ NonSep (listW D O d (thr 0)) (exL 0 ℓ) n ∨
        1 ≤ ladderPot τ D d thr bt B 0 ℓ (O, List.ofFn p)) := by
    apply dens_mono
    intro p hp
    by_contra hcon
    push Not at hcon
    exact hp ⟨hcon.1, hcon.2⟩
  exact (hsub.trans (dens_or_le _ _)).trans (add_le_add hP hT)

end Level

end Protocol
