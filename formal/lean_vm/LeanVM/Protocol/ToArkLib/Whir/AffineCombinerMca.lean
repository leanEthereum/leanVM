/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerMca

  The affine MCA count for interleaved words and the escape count of one affine fold round, at
  admissible interpolation parameters. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFold
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerPacking
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerParams
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerInterpolation

/-!
# Affine MCA and the fold round, assembled

Annex B of the leanVM specification (branch `f128`), `thm:mca-affine` and `lem:fold-list`, in
counting form, over a finite field `F` with `q = |F|`, a domain of `n` points, and words with any
finite number of lanes.

* `card_excSet_le_persistent_add`: the exceptional pairs of the lanes number at most the
  persistent term `jl n B (d + 1) max(q, C(n, 2))` plus the non-persistent exceptional pairs of the
  packed word over any packing field ([CYWZ26, preprint], Lemmas 4.4 and 4.5, and Section 5.1).
* `NonpersistentCount L dom d A m D B`: every word pair over `L` has at most
  `D² + 4 d² M² D³ (n/(A - B))²` non-persistent exceptional pairs ([CYWZ26, Lemmas 4.2, 4.3 and
  4.7]); `nonpersistentCount_of_interpolant` derives it, through Lemma 4.2
  (`exists_interpolant`), from `InterpolantCount`, the statement of Lemmas 4.3 and 4.7 for the
  interpolant, the one input not proved here.
* `card_excSet_le_nAff` (`thm:mca-affine`): under `InterpolantCount` over the algebraic closure,
  at most `nAff q n d A m D B = q² ε_aff` exceptional pairs.
* `card_foldBad_le_nAff` (`lem:fold-list`): the escapes `(α, β)` of a fold round number at most
  `nAff + 2 L q`, that is the Annex's `ε_aff + 2L/|E|` times `q²`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F : Type*} [Field F] [Fintype F] {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- **The exceptional pairs, persistent part proved**: for any packing `b`, `π` into `L`, at most
`jl n B (d + 1) max(q, C(n, 2))` plus the non-persistent exceptional pairs of the packed word. -/
theorem card_excSet_le_persistent_add {L : Type*} [Field L] [Algebra F L] (dom : ι ↪ F)
    (b : ρ → L) (π : L →ₗ[F] (ρ → F))
    (hπ : ∀ c : ρ → F, π (∑ r, algebraMap F L (c r) * b r) = c)
    (f g : ρ → ι → F) {d A B : ℕ} (hgap : Fintype.card ι * (d + 1) < B * B) :
    (excSet dom f g d A).card ≤ nAffPersistent (Fintype.card F) (Fintype.card ι) d B +
      (nonpersSet dom (packW b f) (packW b g) d A B).card := by
  refine (card_le_card (excSet_subset_excSetL dom b π hπ f g d A)).trans
    ((card_excSetL_le dom _ _ d A B).trans ?_)
  exact Nat.add_le_add_right (card_persSet_le dom _ _ hgap) _

/-- **The non-persistent count** ([CYWZ26, Lemmas 4.2, 4.3 and 4.7]) over a field `L` of words:
every pair of words `f g : ι → L` has at most `D² + 4 d² M² D³ (n / (A - B))²` pairs `(α, β)` with
a non-persistent exceptional triple. -/
def NonpersistentCount (L : Type*) [Field L] [Algebra F L] (dom : ι ↪ F) (d A m D B : ℕ) : Prop :=
  ∀ f g : ι → L, ((nonpersSet dom f g d A B).card : ℚ) ≤ nAffRest (Fintype.card ι) d A m D B

/-- **The excluded and non-persistent counts** ([CYWZ26, Lemmas 4.3 and 4.7]) over a field `L` of
words: for every pair of words `f g : ι → L` and every nonzero `Q ∈ L[X, Y, Z]` with
`deg_{Y,Z} Q ≤ D` and `deg_Z Q ≤ M` that vanishes along every exceptional triple
(`Q(X, α + β X, P(X)) = 0`), at most `D² + 4 d² M² D³ (n / (A - B))²` pairs `(α, β)` have a
non-persistent exceptional triple. Lemma 4.2 (`exists_interpolant`) supplies `Q`, so this implies
`NonpersistentCount` (`nonpersistentCount_of_interpolant`). -/
def InterpolantCount (L : Type*) [Field L] [Algebra F L] (dom : ι ↪ F) (d A m D B : ℕ) : Prop :=
  ∀ (f g : ι → L) (Q : MvPolynomial (Fin 3) L), Q ≠ 0 →
    (∀ s ∈ Q.support, s 1 + s 2 ≤ D ∧ s 2 ≤ bigM d A m D) →
    (∀ α β P, IsExcTriple dom f g d A α β P → MvPolynomial.aeval ![X, linL α β, P] Q = 0) →
    ((nonpersSet dom f g d A B).card : ℚ) ≤ nAffRest (Fintype.card ι) d A m D B

omit [DecidableEq ι] in
/-- Lemma 4.2 reduces the non-persistent count to `InterpolantCount`. -/
theorem nonpersistentCount_of_interpolant {L : Type*} [Field L] [Algebra F L] (dom : ι ↪ F)
    {d A m D B : ℕ} (hadm : Admissible (Fintype.card ι) d A m D B)
    (hQ : InterpolantCount L dom d A m D B) : NonpersistentCount L dom d A m D B := by
  intro f g
  obtain ⟨Q, hQ0, hsupp, hvan⟩ := exists_interpolant dom f g hadm.2.2.1 hadm.2.2.2.2.1
  refine hQ f g Q hQ0 (fun s hs ↦ ⟨(hsupp s hs).1, (hsupp s hs).2.1⟩) fun α β P hP ↦ ?_
  exact hvan (linL α β) P (natDegree_linL_le α β) hP.1 _ hP.2.1 fun x hx ↦
    (mem_agreeL dom f g P α β x).mp hx

/-- **Affine MCA, counting form** (Annex B, `thm:mca-affine`; [CYWZ26, Thm. 1.1, Lemma 4.1,
Section 5.1]): at admissible `(m, D, B)`, and given Lemmas 4.3 and 4.7 (`InterpolantCount`) over the
algebraic closure of `F`, every pair of interleaved words has at most `nAff q n d A m D B` exceptional
pairs. -/
theorem card_excSet_le_nAff (dom : ι ↪ F) {d A m D B : ℕ}
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (hN : InterpolantCount (AlgebraicClosure F) dom d A m D B) (f g : ρ → ι → F) :
    ((excSet dom f g d A).card : ℚ) ≤ nAff (Fintype.card F) (Fintype.card ι) d A m D B := by
  obtain ⟨b, π, hπ⟩ := exists_packing (F := F) (ρ := ρ)
  have hN := nonpersistentCount_of_interpolant dom hadm hN
  have h := card_excSet_le_persistent_add dom b π hπ f g (d := d) (A := A) hadm.2.2.2.2.2.2.2
  unfold nAff
  calc ((excSet dom f g d A).card : ℚ)
      ≤ (nAffPersistent (Fintype.card F) (Fintype.card ι) d B : ℚ) +
          ((nonpersSet dom (packW b f) (packW b g) d A B).card : ℚ) := by exact_mod_cast h
    _ ≤ _ := by gcongr; exact hN _ _

/-- **One affine fold round** (Annex B, `lem:fold-list`, counting form). Let `(A - 1)² > n d`,
`(m, D, B)` admissible for `(n, d, A)`, and `InterpolantCount` hold over the algebraic closure.
If every pair of `lst(f, g; A - 1, d)` violates `Λ₀ F + Λ₁ G = c`, then for every table at most `nAff + 2 jl n (A - 1) d q` challenges `(α, β)` let a tuple of
`lst(fold; A, d)` satisfy the new claim: probability `ε_aff + 2 L / q`. -/
theorem card_foldBad_le_nAff [DecidableEq F] (dom : ι ↪ F) (f g : ρ → ι → F) {d A m D B : ℕ}
    (hgap : Fintype.card ι * d < (A - 1) * (A - 1))
    (hadm : Admissible (Fintype.card ι) d A m D B)
    (hN : InterpolantCount (AlgebraicClosure F) dom d A m D B)
    (Λ₀ Λ₁ : (ρ → F[X]) →ₗ[F] F) (c : F)
    (hviol : ∀ p ∈ pairList dom f g (A - 1) d, Λ₀ p.1 + Λ₁ p.2 ≠ c) (u₀ v c₀ c₁ : F) :
    ((foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁).card : ℚ) ≤
      nAff (Fintype.card F) (Fintype.card ι) d A m D B +
        2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by
  have h := card_foldBad_le dom f g hgap Λ₀ Λ₁ c hviol u₀ v c₀ c₁
  have hmca := card_excSet_le_nAff dom hadm hN g f
  calc ((foldBad dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁).card : ℚ)
      ≤ ((excSet dom g f d A).card : ℚ) +
          2 * jl (Fintype.card ι) (A - 1) d * (Fintype.card F : ℚ) := by exact_mod_cast h
    _ ≤ _ := by gcongr

end
end LeanVM.Protocol.Whir.AffineCombiner
