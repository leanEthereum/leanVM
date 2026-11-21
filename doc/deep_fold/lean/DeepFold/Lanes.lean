/-
The DEEP fold theorem for interleaved words (several lanes) with monomial lane weights:
Definition 4.1, Lemma 4.4, Lemmas 4.6 and 4.7 and Theorem 4.9 of the paper, with lanes.

A tuple is `U : ι → K[X]`, one polynomial per lane. A point is `z = (θ, ζ)`, and with an exponent
map `ex : ι → ℕ` the point evaluation is `ev_z(U) = ∑_u θ^(ex u) U_u(ζ)`. In the paper the lanes
after round `j` are `u ∈ {0,1}^(ℓ-j)` and `ex = e_j`, which is injective with values at most
`2^ℓ - 2^j`. Only injectivity and a bound `E` on the exponents are used here.
-/
import DeepFold.Class
import DeepFold.Agreement
import DeepFold.Counting

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

local notation "φ" => algebraMap K[X] (RatFunc K)

/-- A candidate with lanes: a challenge and a tuple of polynomials. -/
abbrev CandL (ι K : Type*) [Field K] := (K × K) × (ι → K[X])

/-- Lane `u` of a candidate. -/
abbrev lane (e : CandL ι K) (u : ι) : Cand K := (e.1, e.2 u)

/-- The tuple `Δ` of three candidates (Definition 4.5 of the paper): `Delta` lane by lane. -/
noncomputable def DeltaL (e₁ e₂ e₃ : CandL ι K) : ι → K[X] :=
  fun u => Delta (lane e₁ u) (lane e₂ u) (lane e₃ u)

/-- Definition 4.1 of the paper: `ev_z(U) = ∑_u θ^(ex u) U_u(ζ)` at the point `z = (θ, ζ)`. -/
noncomputable def evL (ex : ι → ℕ) (z : K × K) (U : ι → K[X]) : K :=
  ∑ u, z.1 ^ ex u * (U u).eval z.2

/-- (E1) of Lemma 4.4 of the paper, additivity. -/
theorem evL_add (ex : ι → ℕ) (z : K × K) (U V : ι → K[X]) :
    evL ex z (U + V) = evL ex z U + evL ex z V := by
  simp only [evL, Pi.add_apply, eval_add, mul_add, sum_add_distrib]

/-- (E3), which contains (E1)'s homogeneity: `ev_z(a U) = a(ζ) ev_z(U)` for a polynomial `a`. -/
theorem evL_mul (ex : ι → ℕ) (z : K × K) (a : K[X]) (U : ι → K[X]) :
    evL ex z (fun u => a * U u) = a.eval z.2 * evL ex z U := by
  simp only [evL, eval_mul, mul_sum]
  refine sum_congr rfl (fun u _ => ?_)
  ring

/-- (E2): for a tuple on two copies of the lanes, the first copy (the half `F`, lane variable
`u_j = 0`) carrying the extra exponent `w` (`2^(j-1)` in the paper),
`ev(U) = θ^w ev(F) + ev(G)`. -/
theorem evL_halves (ex : ι → ℕ) (w : ℕ) (z : K × K) (U : ι ⊕ ι → K[X]) :
    evL (Sum.elim (fun u => w + ex u) ex) z U =
      z.1 ^ w * evL ex z (fun u => U (Sum.inl u)) + evL ex z (fun u => U (Sum.inr u)) := by
  simp only [evL, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, pow_add, mul_sum, mul_assoc]

/-- The evaluation of a fold: `ev_z(G + a_c F) = ev_z(G) + a_c(ζ) ev_z(F)`. -/
theorem evL_fold (ex : ι → ℕ) (z : K × K) {c : K × K} {P F₀ G₀ : ι → K[X]}
    (h : ∀ u, P u = G₀ u + aff c * F₀ u) :
    evL ex z P = evL ex z G₀ + (c.1 + c.2 * z.2) * evL ex z F₀ := by
  unfold evL
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun u _ => ?_)
  rw [h u]
  simp only [eval_add, eval_mul, aff_eval]
  ring

/-- `(c, P)` is consistent with the answer `(a, b)` at the point `z = (θ, ζ)`:
`ev_z(P) = b + (α + β ζ) a`. -/
def ConsL (ex : ι → ℕ) (e : CandL ι K) (z : K × K) (a b : K) : Prop :=
  evL ex z e.2 = b + (e.1.1 + e.1.2 * z.2) * a

/-- Lemma 4.6(c) of the paper: three candidates consistent with one answer at `z` have
`ev_z(Δ) = 0`. -/
theorem evL_DeltaL_eq_zero {ex : ι → ℕ} {e₁ e₂ e₃ : CandL ι K} {z : K × K} {a b : K}
    (h₁ : ConsL ex e₁ z a b) (h₂ : ConsL ex e₂ z a b) (h₃ : ConsL ex e₃ z a b) :
    evL ex z (DeltaL e₁ e₂ e₃) = 0 := by
  have key : evL ex z (DeltaL e₁ e₂ e₃) =
      evL ex z e₁.2 * ((e₃.1.1 + e₃.1.2 * z.2) - (e₂.1.1 + e₂.1.2 * z.2)) +
      evL ex z e₂.2 * ((e₁.1.1 + e₁.1.2 * z.2) - (e₃.1.1 + e₃.1.2 * z.2)) +
      evL ex z e₃.2 * ((e₂.1.1 + e₂.1.2 * z.2) - (e₁.1.1 + e₁.1.2 * z.2)) := by
    unfold evL
    rw [sum_mul, sum_mul, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun u _ => ?_)
    simp only [DeltaL, Delta, eval_add, eval_mul, eval_sub, aff_eval]
    ring
  unfold ConsL at h₁ h₂ h₃
  rw [key, h₁, h₂, h₃]
  ring

omit [Fintype ι] in
/-- The lanes of `Δ` have degree at most `d + 1`. -/
theorem DeltaL_natDegree_le {e₁ e₂ e₃ : CandL ι K} {d : ℕ}
    (h₁ : ∀ u, (e₁.2 u).natDegree ≤ d) (h₂ : ∀ u, (e₂.2 u).natDegree ≤ d)
    (h₃ : ∀ u, (e₃.2 u).natDegree ≤ d) (u : ι) : (DeltaL e₁ e₂ e₃ u).natDegree ≤ d + 1 :=
  Delta_natDegree_le (h₁ u) (h₂ u) (h₃ u)

/-- `(c, P)` is the fold of the tuple pair `(F, G)` of rational functions, lane by lane. -/
def IsFoldL (F G : ι → RatFunc K) (e : CandL ι K) : Prop :=
  ∀ u, IsFold (F u) (G u) (lane e u)

/-- The rational tuples `F`, `G` of two candidates. -/
noncomputable def pairFL (e₁ e₂ : CandL ι K) : ι → RatFunc K :=
  fun u => pairF (lane e₁ u) (lane e₂ u)

noncomputable def pairGL (e₁ e₂ : CandL ι K) : ι → RatFunc K :=
  fun u => pairG (lane e₁ u) (lane e₂ u)

omit [Fintype ι] in
theorem isFoldL_pair_left (e₁ e₂ : CandL ι K) : IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e₁ :=
  fun u => isFold_pair_left (lane e₁ u) (lane e₂ u)

omit [Fintype ι] in
theorem isFoldL_pair_right {e₁ e₂ : CandL ι K} (h : e₁.1 ≠ e₂.1) :
    IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e₂ :=
  fun u => isFold_pair_right (e₁ := lane e₁ u) (e₂ := lane e₂ u) h

omit [Fintype ι] in
/-- Lemma 4.6(a) of the paper, uniqueness. -/
theorem isFoldL_unique {F G : ι → RatFunc K} {e₁ e₂ : CandL ι K} (h : e₁.1 ≠ e₂.1)
    (h₁ : IsFoldL F G e₁) (h₂ : IsFoldL F G e₂) : F = pairFL e₁ e₂ ∧ G = pairGL e₁ e₂ :=
  ⟨funext fun u => (isFold_unique (e₁ := lane e₁ u) (e₂ := lane e₂ u) h (h₁ u) (h₂ u)).1,
    funext fun u => (isFold_unique (e₁ := lane e₁ u) (e₂ := lane e₂ u) h (h₁ u) (h₂ u)).2⟩

omit [Fintype ι] in
/-- Lemma 4.6(b) of the paper: for `c₁ ≠ c₂`, `Δ = 0` exactly when the third candidate is in the
class of the first two. -/
theorem DeltaL_eq_zero_iff {e₁ e₂ : CandL ι K} (h : e₁.1 ≠ e₂.1) (e₃ : CandL ι K) :
    DeltaL e₁ e₂ e₃ = 0 ↔ IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e₃ := by
  rw [funext_iff]
  exact forall_congr' (fun u =>
    Delta_eq_zero_iff (e₁ := lane e₁ u) (e₂ := lane e₂ u) h (lane e₃ u))

omit [Fintype ι] in
theorem isFoldL_ext {F G : ι → RatFunc K} {e e' : CandL ι K} (he : IsFoldL F G e)
    (he' : IsFoldL F G e') (h : e.1 = e'.1) : e = e' := by
  refine Prod.ext h (funext fun u => ?_)
  exact congrArg Prod.snd (isFold_ext (he u) (he' u) h)

section Finite

variable [Fintype K]

/-- (E4) of Lemma 4.4 of the paper, counting form: a nonzero tuple with lanes of degree at most
`d`, evaluated with injective exponents bounded by `E`, vanishes at no more than `(d + E) q` of
the `q^2` points. -/
theorem card_evL_zero_le (ex : ι → ℕ) (hex : Function.Injective ex) {E d : ℕ}
    (hE : ∀ u, ex u ≤ E) (Q : ι → K[X]) (hQ : Q ≠ 0) (hd : ∀ u, (Q u).natDegree ≤ d) :
    (univ.filter (fun z : K × K => evL ex z Q = 0)).card ≤ (d + E) * Fintype.card K := by
  obtain ⟨u₀, hu₀⟩ : ∃ u, Q u ≠ 0 := by
    by_contra h
    exact hQ (funext fun u => not_not.mp (not_exists.mp h u))
  let R : K → K[X] := fun ζ => ∑ u, C ((Q u).eval ζ) * X ^ ex u
  have hR : ∀ θ ζ : K, (R ζ).eval θ = evL ex (θ, ζ) Q := by
    intro θ ζ
    simp only [R, evL, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact sum_congr rfl (fun u _ => mul_comm _ _)
  have hRcoeff : ∀ ζ : K, (R ζ).coeff (ex u₀) = (Q u₀).eval ζ := by
    intro ζ
    simp only [R, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [sum_eq_single u₀]
    · simp
    · intro u _ hu
      have hne : ex u₀ ≠ ex u := fun h => hu (hex h).symm
      simp only [hne, ite_false, mul_zero]
    · intro h
      exact absurd (mem_univ u₀) h
  have hRdeg : ∀ ζ : K, (R ζ).natDegree ≤ E := by
    intro ζ
    apply natDegree_sum_le_of_forall_le
    intro u _
    exact (natDegree_C_mul_X_pow_le _ _).trans (hE u)
  have hfiber : ∀ ζ : K, (univ.filter (fun θ : K => evL ex (θ, ζ) Q = 0)).card ≤
      (if (Q u₀).eval ζ = 0 then Fintype.card K else 0) + E := by
    intro ζ
    by_cases h0 : (Q u₀).eval ζ = 0
    · simp only [h0, ite_true]
      exact (card_le_univ _).trans (Nat.le_add_right _ _)
    · simp only [h0, ite_false, zero_add]
      have hRne : R ζ ≠ 0 := by
        intro h
        apply h0
        rw [← hRcoeff ζ, h, coeff_zero]
      have h1 := card_roots_le hRne
      simp only [hR] at h1
      exact h1.trans (hRdeg ζ)
  calc (univ.filter (fun z : K × K => evL ex z Q = 0)).card
      = ∑ ζ : K, (univ.filter (fun θ : K => evL ex (θ, ζ) Q = 0)).card := by
        simp only [card_filter]
        rw [Fintype.sum_prod_type_right]
    _ ≤ ∑ ζ : K, ((if (Q u₀).eval ζ = 0 then Fintype.card K else 0) + E) :=
        sum_le_sum (fun ζ _ => hfiber ζ)
    _ = (univ.filter (fun ζ : K => (Q u₀).eval ζ = 0)).card * Fintype.card K +
          Fintype.card K * E := by
        rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← sum_filter, sum_const,
          smul_eq_mul]
    _ ≤ d * Fintype.card K + Fintype.card K * E := by
        gcongr
        exact (card_roots_le hu₀).trans (hd u₀)
    _ = (d + E) * Fintype.card K := by ring

/-- Three candidates are dependent: if their challenges are pairwise different, then `Δ = 0`. So
"not dependent" is "pairwise different challenges and `Δ ≠ 0`". -/
def DepL (e₁ e₂ e₃ : CandL ι K) : Prop :=
  (e₁.1 ≠ e₂.1 ∧ e₁.1 ≠ e₃.1 ∧ e₂.1 ≠ e₃.1) → DeltaL e₁ e₂ e₃ = 0

/-- The exceptional set `Exc_j(O)` of Definition 4.8 of the paper with threshold `B`: the vectors
of `s` points for which at least `B` ordered triples of `T` have pairwise different challenges,
`Δ ≠ 0` and `ev_{z_i}(Δ) = 0` for all `i`. -/
noncomputable def ExcL (T : Finset (CandL ι K)) (ex : ι → ℕ) (s B : ℕ) :
    Finset (Fin s → K × K) :=
  Exc T DepL (fun e₁ e₂ e₃ z => evL ex z (DeltaL e₁ e₂ e₃) = 0) s B

theorem deltaL_zeros_le {T : Finset (CandL ι K)} {ex : ι → ℕ} (hex : Function.Injective ex)
    {E d : ℕ} (hE : ∀ u, ex u ≤ E) (hT : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, ∀ t₃ ∈ T, ¬ DepL t₁ t₂ t₃ →
      (univ.filter (fun z : K × K => evL ex z (DeltaL t₁ t₂ t₃) = 0)).card ≤
        (d + 1 + E) * Fintype.card K :=
  fun t₁ h₁ t₂ h₂ t₃ h₃ hnd =>
    card_evL_zero_le ex hex hE _ (Classical.not_imp.mp hnd).2
      (DeltaL_natDegree_le (hT t₁ h₁) (hT t₂ h₂) (hT t₃ h₃))

/-- Theorem 4.9(1) of the paper, counting form: `|Exc| · B ≤ |T|^3 ((d + 1 + E) q)^s`, among
`(q^2)^s` point vectors. -/
theorem card_ExcL_mul_le {T : Finset (CandL ι K)} {ex : ι → ℕ} (hex : Function.Injective ex)
    {E d : ℕ} (hE : ∀ u, ex u ≤ E) (hT : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d) (s B : ℕ) :
    (ExcL T ex s B).card * B ≤ T.card ^ 3 * ((d + 1 + E) * Fintype.card K) ^ s :=
  card_Exc_mul_le T _ _ (deltaL_zeros_le hex hE hT) s B

/-- Theorem 4.9(1) of the paper as a probability over `s` independent uniform points of `K^2`: at
most `|T|^3 ε^s / B` with `ε = (d + 1 + E) / q`. -/
theorem density_ExcL_le {T : Finset (CandL ι K)} {ex : ι → ℕ} (hex : Function.Injective ex)
    {E d : ℕ} (hE : ∀ u, ex u ≤ E) (hT : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d)
    (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((ExcL T ex s B).card : ℚ) / (Fintype.card (Fin s → K × K) : ℚ) ≤
      (T.card : ℚ) ^ 3 * (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s / B := by
  have h := density_Exc_le T _ _ (deltaL_zeros_le hex hE hT) s hB
  have hq : (Fintype.card K : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (((d + 1 + E) * Fintype.card K : ℕ) : ℚ) / (Fintype.card (K × K) : ℚ) =
      ((d + 1 + E : ℕ) : ℚ) / Fintype.card K := by
    rw [Fintype.card_prod]
    push_cast
    rw [mul_div_mul_right _ _ hq]
  rw [he] at h
  exact h

/-- Theorem 4.9(2) of the paper with lanes: outside the exceptional set, every set of at least `K₀`
candidates with pairwise different challenges that are consistent with one answer vector contains
more than `M` elements of one class. -/
theorem deepFoldL_class {ex : ι → ℕ} {T : Finset (CandL ι K)} {s K₀ M : ℕ}
    {z : Fin s → K × K} (hz : z ∉ ExcL T ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → K × K) {W : Finset (CandL ι K)} (hWT : W ⊆ T)
    (hWc : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e')
    (hW : ∀ e ∈ W, ∀ i, ConsL ex e (z i) (m i).1 (m i).2) (hK : K₀ ≤ W.card) :
    ∃ e₁ ∈ W, ∃ e₂ ∈ W, e₁.1 ≠ e₂.1 ∧
      M < (W.filter (fun e => IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e)).card := by
  obtain ⟨e₁, he₁, e₂, he₂, hne, hbig⟩ := exists_big_class T
    DepL (fun e₁ e₂ e₃ z => evL ex z (DeltaL e₁ e₂ e₃) = 0)
    (fun (e : CandL ι K) (z : K × K) (m : K × K) => ConsL ex e z m.1 m.2)
    (fun _ _ _ _ _ h₁ h₂ h₃ => evL_DeltaL_eq_zero h₁ h₂ h₃) hz m hWT hW hK
  have hc : e₁.1 ≠ e₂.1 := fun h => hne (hWc e₁ he₁ e₂ he₂ h)
  refine ⟨e₁, he₁, e₂, he₂, hc, lt_of_lt_of_le hbig (card_le_card ?_)⟩
  intro e he
  obtain ⟨heW, hdep⟩ := mem_filter.mp he
  refine mem_filter.mpr ⟨heW, ?_⟩
  by_cases h1 : e₁.1 = e.1
  · rw [← hWc e₁ he₁ e heW h1]
    exact isFoldL_pair_left e₁ e₂
  · by_cases h2 : e₂.1 = e.1
    · rw [← hWc e₂ he₂ e heW h2]
      exact isFoldL_pair_right hc
    · exact (DeltaL_eq_zero_iff hc e).mp (hdep ⟨hc, h1, h2⟩)

/-- The consequence of Lemma 4.7(a), (b) of the paper that the fold round uses, with lanes, for a
class with more than `q` elements: its rational pair is a pair of polynomial tuples with
`deg F < d`, `deg G ≤ d`. -/
theorem classL_poly_of_card_gt {F G : ι → RatFunc K} {W : Finset (CandL ι K)} {d : ℕ}
    (hW : ∀ e ∈ W, IsFoldL F G e ∧ ∀ u, (e.2 u).natDegree ≤ d)
    (hq : Fintype.card K < W.card) :
    ∃ F₀ G₀ : ι → K[X], (∀ u, F u = φ (F₀ u)) ∧ (∀ u, G u = φ (G₀ u)) ∧
      (∀ u, (F₀ u).degree < (d : WithBot ℕ)) ∧ ∀ u, (G₀ u).natDegree ≤ d := by
  have hinj : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e' := fun e he e' he' h =>
    isFoldL_ext (hW e he).1 (hW e' he').1 h
  by_cases hβ : ∃ e ∈ W, ∃ e' ∈ W, e.1.2 ≠ e'.1.2
  · obtain ⟨e, he, e', he', hβ⟩ := hβ
    have hdich := fun u => fold_anchor_dichotomy (e := lane e u) (e' := lane e' u) hβ
      ((hW e he).1 u) ((hW e' he').1 u) ((hW e he).2 u) ((hW e' he').2 u)
    by_cases hall : ∀ u, ∃ F₀ G₀ : K[X], F u = φ F₀ ∧ G u = φ G₀ ∧
        F₀.degree < (d : WithBot ℕ) ∧ G₀.natDegree ≤ d
    · choose F₀ G₀ h1 h2 h3 h4 using hall
      exact ⟨F₀, G₀, h1, h2, h3, h4⟩
    · obtain ⟨u, hu⟩ := not_forall.mp hall
      have hline := (hdich u).resolve_left hu
      exact absurd (card_le_of_line (ch := fun e : CandL ι K => e.1) hinj
        (fun e'' he'' => hline (lane e'' u) ((hW e'' he'').1 u))) (not_le.mpr hq)
  · obtain ⟨e, he⟩ : W.Nonempty := card_pos.mp (by omega)
    have hconst : ∀ e' ∈ W, e'.1.2 = e.1.2 := by
      intro e' he'
      by_contra hne
      exact hβ ⟨e', he', e, he, hne⟩
    exact absurd (card_le_of_snd_const (ch := fun e : CandL ι K => e.1) hinj hconst)
      (not_le.mpr hq)

end Finite

/-- The agreement set of `(c, P)` with the fold `O₁ + a_c O₀` of the interleaved words: the
columns `x ∈ D` where all lanes agree. -/
noncomputable def agrL (D : Finset K) (O₀ O₁ : K → ι → K) (e : CandL ι K) : Finset K :=
  D.filter (fun x => ∀ u, (e.2 u).eval x = O₁ x u + (e.1.1 + e.1.2 * x) * O₀ x u)

/-- `𝒜_{F,G}` of Lemma 4.7(c) of the paper: the columns where the pair of polynomial tuples agrees
with the pair of words. -/
noncomputable def agrPairL (D : Finset K) (O₀ O₁ : K → ι → K) (F₀ G₀ : ι → K[X]) : Finset K :=
  D.filter (fun x => ∀ u, (F₀ u).eval x = O₀ x u ∧ (G₀ u).eval x = O₁ x u)

/-- Lemma 4.7(c) of the paper with lanes: in the class of a pair of polynomial tuples, at most
`C(n - |𝒜_{F,G}|, 2)` elements have two or more agreement columns outside `𝒜_{F,G}`. -/
theorem card_agrL_outside_le (D : Finset K) (O₀ O₁ : K → ι → K) (F₀ G₀ : ι → K[X])
    (W : Finset (CandL ι K)) (hW : ∀ e ∈ W, ∀ u, e.2 u = G₀ u + aff e.1 * F₀ u) :
    (W.filter (fun e => 2 ≤ (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card)).card ≤
      (D.card - (agrPairL D O₀ O₁ F₀ G₀).card).choose 2 := by
  have hZD : agrPairL D O₀ O₁ F₀ G₀ ⊆ D := filter_subset _ _
  have hcard : (D \ agrPairL D O₀ O₁ F₀ G₀).card = D.card - (agrPairL D O₀ O₁ F₀ G₀).card :=
    card_sdiff_of_subset hZD
  have hinter : ∀ e, agrL D O₀ O₁ e ∩ (D \ agrPairL D O₀ O₁ F₀ G₀) =
      agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀ := by
    intro e
    ext x
    simp only [agrL, mem_inter, mem_sdiff, mem_filter]
    tauto
  have hch : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e' := by
    intro e he e' he' h
    refine Prod.ext h (funext fun u => ?_)
    rw [hW e he u, hW e' he' u, h]
  have hscal : ∀ e ∈ W, ∀ x ∈ D \ agrPairL D O₀ O₁ F₀ G₀, x ∈ agrL D O₀ O₁ e →
      ∀ u, (e.1.1 + e.1.2 * x) * (O₀ x u - (F₀ u).eval x) = (G₀ u).eval x - O₁ x u := by
    intro e he x _ hx u
    have hxa := (mem_filter.mp hx).2 u
    rw [hW e he u] at hxa
    simp only [eval_add, eval_mul, aff_eval] at hxa
    linear_combination -hxa
  have key := card_two_points_le W (fun e => e.1) hch (D \ agrPairL D O₀ O₁ F₀ G₀)
    (agrL D O₀ O₁) (by
      intro e he e' he' x hxR hx hx'
      have h1 := hscal e he x hxR hx
      have h2 := hscal e' he' x hxR hx'
      have hxD := (mem_sdiff.mp hxR).1
      have hxZ := (mem_sdiff.mp hxR).2
      obtain ⟨u, hu⟩ : ∃ u, O₀ x u - (F₀ u).eval x ≠ 0 := by
        by_contra hno
        apply hxZ
        refine mem_filter.mpr ⟨hxD, fun u => ?_⟩
        have h0 : O₀ x u - (F₀ u).eval x = 0 := not_not.mp (not_exists.mp hno u)
        have h3 := h1 u
        rw [h0, mul_zero] at h3
        exact ⟨(sub_eq_zero.mp h0).symm, (sub_eq_zero.mp h3.symm)⟩
      exact mul_right_cancel₀ hu ((h1 u).trans (h2 u).symm))
  simp only [hinter] at key
  rw [hcard] at key
  exact key

/-- Lemma 4.7(c) of the paper, the near-tuple clause: a class of a pair of polynomial tuples with
more than `C(n, 2)` elements has an element with at most one agreement column outside
`𝒜_{F,G}`. -/
theorem exists_nearL (D : Finset K) (O₀ O₁ : K → ι → K) (F₀ G₀ : ι → K[X])
    (W : Finset (CandL ι K)) (hW : ∀ e ∈ W, ∀ u, e.2 u = G₀ u + aff e.1 * F₀ u)
    (hcard : D.card.choose 2 < W.card) :
    ∃ e ∈ W, (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 := by
  have h1 := card_agrL_outside_le D O₀ O₁ F₀ G₀ W hW
  have h2 : (D.card - (agrPairL D O₀ O₁ F₀ G₀).card).choose 2 ≤ D.card.choose 2 :=
    Nat.choose_le_choose 2 (Nat.sub_le _ _)
  by_contra hcon
  have hall : ∀ e ∈ W, 2 ≤ (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card := by
    intro e he
    by_contra hlt
    exact hcon ⟨e, he, by omega⟩
  rw [filter_true_of_mem hall] at h1
  omega

/-- If an element with at least `A` agreement columns has at most one outside `𝒜_{F,G}`, then
`|𝒜_{F,G}| ≥ A - 1`. -/
theorem agrPairL_card_ge (D : Finset K) (O₀ O₁ : K → ι → K) (F₀ G₀ : ι → K[X]) {e : CandL ι K}
    {A : ℕ} (hA : A ≤ (agrL D O₀ O₁ e).card)
    (hnear : (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1) :
    A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 := by
  have h4 : (agrL D O₀ O₁ e).card ≤
      (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card + (agrPairL D O₀ O₁ F₀ G₀).card :=
    card_le_card_sdiff_add_card
  omega

/-- Theorem 4.9(2) of the paper joined with Lemma 4.7, with lanes and monomial lane weights (the
first half of the proof of Lemma 4.10(2)).

`D` is the domain, `O₀, O₁` the two halves of the interleaved word, `T` a set of candidates
`(c, P)` whose lanes have degree at most `d` and which agree with `O₁ + a_c O₀` on at least `A`
columns. Let `M ≥ max(q, C(n, 2))`. For `z` outside the exceptional set of `T` and every answer
vector `m = (y^F_i, y^G_i)`: every `W ⊆ T` with pairwise different challenges, at least `K₀`
elements, all consistent with `m`, contains more than `M` folds `G₀ + a_c F₀` of one pair of
polynomial tuples with `deg F₀ < d`, `deg G₀ ≤ d`, which agrees with `(O₀, O₁)` on at least
`A - 1` columns, is a near tuple of one of these folds, and has `ev_{z_i}(F₀) = y^F_i`,
`ev_{z_i}(G₀) = y^G_i` for all `i`. -/
theorem deepFoldL_theorem3 [Fintype K] (D : Finset K) (O₀ O₁ : K → ι → K) {d A : ℕ}
    (ex : ι → ℕ) {T : Finset (CandL ι K)} (hTd : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d)
    (hTA : ∀ e ∈ T, A ≤ (agrL D O₀ O₁ e).card)
    {s K₀ M : ℕ} (hMq : Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K} (hz : z ∉ ExcL T ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → K × K) {W : Finset (CandL ι K)} (hWT : W ⊆ T)
    (hWc : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e')
    (hW : ∀ e ∈ W, ∀ i, ConsL ex e (z i) (m i).1 (m i).2) (hK : K₀ ≤ W.card) :
    ∃ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) ∧ (∀ u, (G₀ u).natDegree ≤ d) ∧
      A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 ∧
      M < (W.filter (fun e => ∀ u, e.2 u = G₀ u + aff e.1 * F₀ u)).card ∧
      (∃ e ∈ W, (∀ u, e.2 u = G₀ u + aff e.1 * F₀ u) ∧
        (agrL D O₀ O₁ e \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1) ∧
      ∀ i, evL ex (z i) F₀ = (m i).1 ∧ evL ex (z i) G₀ = (m i).2 := by
  obtain ⟨e₁, he₁, e₂, he₂, hc, hbig⟩ := deepFoldL_class hz m hWT hWc hW hK
  set Cl := W.filter (fun e => IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e) with hCl
  have hClW : ∀ e ∈ Cl, e ∈ W := fun e he => (mem_filter.mp he).1
  have hClfold : ∀ e ∈ Cl, IsFoldL (pairFL e₁ e₂) (pairGL e₁ e₂) e ∧
      ∀ u, (e.2 u).natDegree ≤ d :=
    fun e he => ⟨(mem_filter.mp he).2, hTd e (hWT (hClW e he))⟩
  have hqC : Fintype.card K < Cl.card := lt_of_le_of_lt hMq hbig
  obtain ⟨F₀, G₀, hF, hG, hFd, hGd⟩ := classL_poly_of_card_gt hClfold hqC
  have hCleq : ∀ e ∈ Cl, ∀ u, e.2 u = G₀ u + aff e.1 * F₀ u := by
    intro e he u
    have h1 := (hClfold e he).1 u
    unfold IsFold at h1
    rw [hF u, hG u, ← map_mul, ← map_add] at h1
    exact phi_injective h1
  have hinjC : ∀ e ∈ Cl, ∀ e' ∈ Cl, e.1 = e'.1 → e = e' := fun e he e' he' h =>
    hWc e (hClW e he) e' (hClW e' he') h
  obtain ⟨e₀, he₀, hnear⟩ := exists_nearL D O₀ O₁ F₀ G₀ Cl hCleq (lt_of_le_of_lt hMn hbig)
  refine ⟨F₀, G₀, hFd, hGd, ?_, ?_, ⟨e₀, hClW e₀ he₀, hCleq e₀ he₀, hnear⟩, ?_⟩
  · exact agrPairL_card_ge D O₀ O₁ F₀ G₀ (hTA e₀ (hWT (hClW e₀ he₀))) hnear
  · refine lt_of_lt_of_le hbig (card_le_card ?_)
    intro e he
    exact mem_filter.mpr ⟨hClW e he, hCleq e he⟩
  · intro i
    have hev : ∀ e ∈ Cl, evL ex (z i) G₀ + (e.1.1 + e.1.2 * (z i).2) * evL ex (z i) F₀ =
        (m i).2 + (e.1.1 + e.1.2 * (z i).2) * (m i).1 := by
      intro e he
      have h1 := hW e (hClW e he) i
      unfold ConsL at h1
      rw [evL_fold ex (z i) (hCleq e he)] at h1
      exact h1
    by_contra hcon
    have hF' : evL ex (z i) F₀ ≠ (m i).1 := by
      intro hFeq
      apply hcon
      refine ⟨hFeq, ?_⟩
      have h1 := hev e₀ he₀
      rw [hFeq] at h1
      exact add_right_cancel h1
    have hline : ∀ e ∈ Cl, e.1.1 + (z i).2 * e.1.2 =
        ((m i).2 - evL ex (z i) G₀) / (evL ex (z i) F₀ - (m i).1) := by
      intro e he
      rw [eq_div_iff (sub_ne_zero.mpr hF')]
      linear_combination hev e he
    exact absurd (card_le_of_line (ch := fun e : CandL ι K => e.1) hinjC hline)
      (not_le.mpr hqC)

end DeepFold
