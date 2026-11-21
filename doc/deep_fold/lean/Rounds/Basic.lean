/-
The state of the round-by-round theorem (Section 5.3 of the paper), and the updates a fold round
makes to it (Protocol 4.2, step 1(d)).

`Doomed` is the invariant `(I_{i,j})`, and with a predicate `B` the relativised invariant
`(I^B_{i,j})` of Definition 5.4: no member of the list of the current word that satisfies `B`
satisfies the running claim together with all carried point claims.
-/
import DeepFold.Main

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The agreement set of a polynomial tuple `U` with an interleaved word `O` on the domain `D`:
the columns `x` with `U_u(x) = O[u, x]` for every lane `u` (Definition 2.1 of the paper, from
Annex B of the leanVM specification). -/
noncomputable def agr (D : Finset K) (O : K → ι → K) (U : ι → K[X]) : Finset K :=
  D.filter (fun x => ∀ u, (U u).eval x = O x u)

/-- `U ∈ List(O; A, d)`: every lane of `U` has degree at most `d`, and `U` agrees with `O` on at
least `A` columns. -/
def InList (D : Finset K) (O : K → ι → K) (d A : ℕ) (U : ι → K[X]) : Prop :=
  (∀ u, (U u).natDegree ≤ d) ∧ A ≤ (agr D O U).card

/-- A near tuple of `O` on `S` (Definition 5.4 of the paper): of degree at most `d`, agreeing
with `O` on all but at most one column of `S`. -/
def NearT (D : Finset K) (O : K → ι → K) (d : ℕ) (S : Finset K) (U : ι → K[X]) : Prop :=
  (∀ u, (U u).natDegree ≤ d) ∧ (S \ agr D O U).card ≤ 1

/-- The half `O₀` of a word with lanes `ι ⊕ ι`: the lanes whose folded variable is `0`. -/
def half₀ (O : K → ι ⊕ ι → K) : K → ι → K := fun x u => O x (Sum.inl u)

/-- The half `O₁`: the lanes whose folded variable is `1`. -/
def half₁ (O : K → ι ⊕ ι → K) : K → ι → K := fun x u => O x (Sum.inr u)

/-- The affine fold `O_c = O₁ + (α + β x) O₀` of a word, `c = (α, β)` (Definition 2.2 of the
paper, from Annex B of the leanVM specification). -/
def foldWord (c : K × K) (O : K → ι ⊕ ι → K) : K → ι → K :=
  fun x u => O x (Sum.inr u) + (c.1 + c.2 * x) * O x (Sum.inl u)

/-- The fold of a polynomial tuple: `G + (α + β X) F` for `U = (F, G)`. -/
noncomputable def foldTuple (c : K × K) (U : ι ⊕ ι → K[X]) : ι → K[X] :=
  fun u => U (Sum.inr u) + aff c * U (Sum.inl u)

/-- The pull-back of a predicate along the fold challenge `c` (Definition 5.4 of the paper):
`(pull B)(P)` says that if `P` agrees with the fold `O_c` on at least `A` columns, then every
near tuple of `O` on the agreement set of `P` with `O_c` satisfies `B`. -/
def pull (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (c : K × K)
    (B : (ι ⊕ ι → K[X]) → Prop) : (ι → K[X]) → Prop :=
  fun P => A ≤ (agr D (foldWord c O) P).card →
    ∀ U : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) U → B U

/-- The embedding of a first half as a tuple with lanes `ι ⊕ ι`: `F ↦ (F, 0)`. -/
noncomputable def inlL : (ι → K[X]) →ₗ[K] (ι ⊕ ι → K[X]) where
  toFun F := Sum.elim F 0
  map_add' F G := by
    funext u
    cases u <;> simp
  map_smul' a F := by
    funext u
    cases u <;> simp

/-- The embedding of a second half: `G ↦ (0, G)`. -/
noncomputable def inrL : (ι → K[X]) →ₗ[K] (ι ⊕ ι → K[X]) where
  toFun G := Sum.elim 0 G
  map_add' F G := by
    funext u
    cases u <;> simp
  map_smul' a F := by
    funext u
    cases u <;> simp

/-- The weight after the fold challenge: `W̃(α, ·) = (1 + α) W₀ + α W₁`, where `W₀`, `W₁` are the
restrictions of `W` to the two halves (Section 2.2 of the paper). -/
noncomputable def foldWeight (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (c : K × K) : (ι → K[X]) →ₗ[K] K :=
  (1 + c.1) • (W ∘ₗ inlL) + c.1 • (W ∘ₗ inrL)

/-- The running claim after the fold challenge (equation (1) of the paper, from Annex B of the
leanVM specification):
`σ' = v_G + α (v_G + σ) + α² v_F + β σ₀ + α β (σ₀ + σ₁)`. -/
def foldClaim (σ vG vF σ₀ σ₁ : K) (c : K × K) : K :=
  vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁)

/-- The carried point values after the fold challenge (equation (4) of the paper):
`v'_m = v_m + (θ_m^w + α + β ζ_m) φ_m`, with `w = 2^(j-1)`. -/
def foldVal {s : ℕ} (w : ℕ) (z : Fin s → K × K) (v φm : Fin s → K) (c : K × K) : Fin s → K :=
  fun m => v m + ((z m).1 ^ w + c.1 + c.2 * (z m).2) * φm m

/-- The exponents of the point evaluation before the fold: the first half carries the extra
exponent `w` (`e_{j-1}(0, u) = 2^(j-1) + e_j(u)`, `e_{j-1}(1, u) = e_j(u)`; (E2) of Lemma 4.4 of
the paper). -/
def exHalves (w : ℕ) (ex : ι → ℕ) : ι ⊕ ι → ℕ := Sum.elim (fun u => w + ex u) ex

/-- The invariant `(I_{i,j})` of Section 5.3 of the paper, relativised to a predicate `B`
(Definition 5.4): no `U ∈ List(O; A, d)` with `B(U)` satisfies the running claim `(W, σ)` and all
carried point claims `(z_m, v_m)`. For plain soundness `B` is `fun _ => True`. -/
def Doomed (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    (z : Fin s → K × K) (v : Fin s → K) (W : (ι → K[X]) →ₗ[K] K) (σ : K)
    (B : (ι → K[X]) → Prop) : Prop :=
  ∀ U : ι → K[X], InList D O d A U → B U → (∀ m, evL ex (z m) U = v m) → W U ≠ σ

/-- A state doomed for a predicate is doomed for every stronger predicate. -/
theorem Doomed.mono {D : Finset K} {O : K → ι → K} {d A : ℕ} {ex : ι → ℕ} {s : ℕ}
    {z : Fin s → K × K} {v : Fin s → K} {W : (ι → K[X]) →ₗ[K] K} {σ : K}
    {B B' : (ι → K[X]) → Prop} (h : Doomed D O d A ex z v W σ B) (hB : ∀ U, B' U → B U) :
    Doomed D O d A ex z v W σ B' :=
  fun U hU hBU hpt => h U hU (hB U hBU) hpt

/-- The agreement set with a fold is the `agrL` of `DeepFold`. -/
theorem agr_foldWord (D : Finset K) (O : K → ι ⊕ ι → K) (c : K × K) (P : ι → K[X]) :
    agr D (foldWord c O) P = agrL D (half₀ O) (half₁ O) (c, P) := by
  rfl

/-- The agreement set of a pair of halves is the `agrPairL` (the set `𝒜_{F,G}`) of `DeepFold`. -/
theorem agr_elim (D : Finset K) (O : K → ι ⊕ ι → K) (F₀ G₀ : ι → K[X]) :
    agr D O (Sum.elim F₀ G₀) = agrPairL D (half₀ O) (half₁ O) F₀ G₀ := by
  ext x
  simp only [agr, agrPairL, half₀, half₁, mem_filter, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    forall_and]

omit [Fintype ι] in
/-- A tuple with lanes `ι ⊕ ι` is the pair of its halves. -/
theorem elim_halves (U : ι ⊕ ι → K[X]) :
    Sum.elim (fun u => U (Sum.inl u)) (fun u => U (Sum.inr u)) = U := by
  funext u
  cases u <;> rfl

omit [Fintype ι] in
/-- `⟨W, U⟩ = ⟨W₀, F⟩ + ⟨W₁, G⟩` for `U = (F, G)`. -/
theorem weight_elim (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (F₀ G₀ : ι → K[X]) :
    W (Sum.elim F₀ G₀) = (W ∘ₗ inlL) F₀ + (W ∘ₗ inrL) G₀ := by
  have h : (Sum.elim F₀ G₀ : ι ⊕ ι → K[X]) = inlL F₀ + inrL G₀ := by
    funext u
    cases u <;> simp [inlL, inrL]
  rw [h, map_add]
  rfl

/-- The agreement set of the fold of a tuple contains the agreement set of the tuple. -/
theorem agr_subset_agr_foldTuple (D : Finset K) (O : K → ι ⊕ ι → K) (c : K × K)
    (U : ι ⊕ ι → K[X]) : agr D O U ⊆ agr D (foldWord c O) (foldTuple c U) := by
  intro x hx
  obtain ⟨hxD, hxU⟩ := mem_filter.mp hx
  refine mem_filter.mpr ⟨hxD, fun u => ?_⟩
  simp only [foldTuple, foldWord, eval_add, eval_mul, aff_eval, hxU]

end Rounds
