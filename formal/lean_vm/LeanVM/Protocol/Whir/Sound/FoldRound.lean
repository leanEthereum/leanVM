/-
  LeanVM.Protocol.Whir.Sound.FoldRound

  One affine fold round of the deployed WHIR verifier against the round-by-round invariant: the
  fold-round lemma as a counting bound at the boundary with the affine-combiner formalization, and
  its reading on the verifier's lanes, weights and claim.
-/

module

public import LeanVM.Protocol.Whir.Sound.Tuple

/-!
# A fold round

Annex B (`doc/leanvm/body/b-polynomial-commitment-scheme.tex`), `lem:fold-list`, and Protocol
`fig:protocol`, step 1: a round of a level with running claim `(Φ, σ)` on a word of `m + 1` lane
variables reads `u₀, w, c₀, c₁`, draws `(α, β)` (after a grind), and continues with the claim
`(Φ(α, ·), u₀ + α (u₀ + σ) + α² w + β c₀ + α β (c₀ + c₁))`
(`foldClaim`) on the affine fold `foldQ dom α β Q` (`foldRound`, `Statement/LeanVmVerifier.lean`):
the weight is folded at the combiner's own `α`.
Every round of a level is analysed at the level's one degree `d`.

* `FoldRoundBound dom d A N`: **the fold-round lemma in counting form**, for every word of any
  lane set with halves `f`, `g`, linear functionals `Λ₀`, `Λ₁` and value `c`: if every pair of
  `lst(f, g; A − 1, d)` violates `Λ₀ F + Λ₁ G = c`, every table leaves at most `N` challenges
  `(α, β)` after which a tuple of `lst(fold; A, d)` satisfies the new claim. It is the
  conclusion of [CYWZ26, preprint]'s Theorem 1.1 as the Annex applies it, with
  `N = N_aff + 2 jl n (A − 1) d |E|`, `N_aff` a bound on the combiner's exceptional pairs
  (`thm:mca-affine`, `ε_aff = N_aff / |E|²`). `LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFold`
  proves it, the count of exceptional pairs from `AffineCombinerMca`; this module takes the lemma
  as a hypothesis, which the parameters' certificate discharges.
* `card_foldEsc_le`: on the verifier's word, weight and claim, from the invariant
  `TViol κ dom Q Φ σ (A − 1) d`, every table leaves at most `N` escaping pairs (`foldEsc`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial Finset

@[expose] public section

open Classical in
/-- **The fold-round lemma, counting form** (Annex B, `lem:fold-list`): see the module docstring. -/
def FoldRoundBound {n : ℕ} (dom : Fin n ↪ E) (d A N : ℕ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] (f g : ρ → Fin n → E) (Λ₀ Λ₁ : (ρ → E[X]) →ₗ[E] E) (c : E),
    (∀ F G : ρ → E[X], DegLE d F → DegLE d G →
      A - 1 ≤ (agreeT dom F f ∩ agreeT dom G g).card → Λ₀ F + Λ₁ G ≠ c) →
    ∀ u₀ v c₀ c₁ : E, (univ.filter fun t : E × E ↦
      ∃ P : ρ → E[X], DegLE d P ∧
        A ≤ (agreeT dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x).card ∧
        (1 - t.1) * Λ₀ P + t.1 * Λ₁ P =
          u₀ + t.1 * (c - u₀) + t.1 ^ 2 * v + t.2 * c₀ + t.1 * t.2 * (c₁ - c₀)).card ≤ N

/-- The verifier's claim after a fold round (`foldRound`):
`u₀ + α (u₀ + σ) + α² w + β c₀ + α β (c₀ + c₁)`. -/
def foldClaim (σ α β u₀ w c₀ c₁ : E) : E :=
  u₀ + α * (u₀ + σ) + α * α * w + β * c₀ + α * β * (c₀ + c₁)

variable {n : ℕ} (κ : ℕ) (dom : Fin n ↪ E) {m : ℕ} (Q : (Fin (m + 1) → Bool) → Fin n → E)
  (Φ : List E → E) (σ : E) (A d : ℕ)

open Classical in
/-- The pairs `(α, β)` after which the fold escapes the invariant at `(A, d)`, for the table
`u₀ w c₀ c₁`. -/
noncomputable def foldEsc (u₀ w c₀ c₁ : E) : Finset (E × E) :=
  univ.filter fun t ↦ ¬ TViol κ dom (foldQ dom t.1 t.2 Q) (fun r ↦ Φ (t.1 :: r))
    (foldClaim σ t.1 t.2 u₀ w c₀ c₁) A d

/-! ## The weight against one half -/

/-- `F ↦ claimSum Ψ (lowMsg κ ∘ F)`, `E`-linear. -/
noncomputable def wlin (Ψ : List E → E) : ((Fin m → Bool) → E[X]) →ₗ[E] E where
  toFun F := claimSum Ψ fun u ↦ lowMsg κ (F u)
  map_add' F G := by
    simp only [claimSum, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c F := by
    simp only [claimSum, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

theorem wlin_apply (Ψ : List E → E) (F : (Fin m → Bool) → E[X]) :
    wlin κ Ψ F = claimSum Ψ fun u ↦ lowMsg κ (F u) := rfl

/-- The tuple with halves `F` and `G`. -/
noncomputable def joinT (F G : (Fin m → Bool) → E[X]) : (Fin (m + 1) → Bool) → E[X] :=
  fun v ↦ if v 0 then G (Fin.tail v) else F (Fin.tail v)

@[simp] theorem joinT_false (F G : (Fin m → Bool) → E[X]) (u : Fin m → Bool) :
    joinT F G (Fin.cons false u) = F u := by simp [joinT]

@[simp] theorem joinT_true (F G : (Fin m → Bool) → E[X]) (u : Fin m → Bool) :
    joinT F G (Fin.cons true u) = G u := by simp [joinT]

theorem forall_cube_succ {P : (Fin (m + 1) → Bool) → Prop} :
    (∀ v, P v) ↔ (∀ u, P (Fin.cons false u)) ∧ ∀ u, P (Fin.cons true u) := by
  refine ⟨fun h ↦ ⟨fun u ↦ h _, fun u ↦ h _⟩, fun h v ↦ ?_⟩
  rw [← Fin.cons_self_tail v]
  cases v 0
  · exact h.1 _
  · exact h.2 _

theorem agreeT_joinT (F G : (Fin m → Bool) → E[X]) :
    agreeT dom (joinT F G) Q =
      agreeT dom F (fun u ↦ Q (Fin.cons false u)) ∩ agreeT dom G (fun u ↦ Q (Fin.cons true u)) := by
  ext x
  simp only [mem_agreeT, Finset.mem_inter]
  rw [forall_cube_succ]
  simp

theorem degLE_joinT {F G : (Fin m → Bool) → E[X]} {d : ℕ} (hF : DegLE d F) (hG : DegLE d G) :
    DegLE d (joinT F G) := fun v ↦ by
  unfold joinT
  split
  · exact hG _
  · exact hF _

theorem tclaim_joinT (F G : (Fin m → Bool) → E[X]) :
    tclaim κ Φ (joinT F G) = wlin κ (fun r ↦ Φ (0 :: r)) F + wlin κ (fun r ↦ Φ (1 :: r)) G := by
  simp only [tclaim, wlin_apply, claimSum, sum_cube_succ, joinT_false, joinT_true, bitsL_cons,
    bitE_false, bitE_true, List.cons_append, Finset.sum_add_distrib]

/-- The folded weight against a tuple: `tclaim Φ(γ, ·) P = (1 − γ) Λ₀ P + γ Λ₁ P`. -/
theorem tclaim_head (hΦ : IsMultiaffine (m + 1 + κ) Φ) (γ : E) (P : (Fin m → Bool) → E[X]) :
    tclaim κ (fun r ↦ Φ (γ :: r)) P =
      (1 - γ) * wlin κ (fun r ↦ Φ (0 :: r)) P + γ * wlin κ (fun r ↦ Φ (1 :: r)) P := by
  have hΦ' : IsMultiaffine (m + κ + 1) Φ := by rwa [show m + κ + 1 = m + 1 + κ by omega]
  simp only [tclaim, wlin_apply, claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ ?_
  rw [hΦ'.head (bitsL u ++ bitsL x) (by simp) γ]
  ring

/-- In characteristic two the verifier's claim is the Annex's. -/
theorem foldClaim_eq (α β u₀ w c₀ c₁ : E) :
    foldClaim σ α β u₀ w c₀ c₁ =
      u₀ + α * (σ - u₀) + α ^ 2 * w + β * c₀ + α * β * (c₁ - c₀) := by
  rw [foldClaim, CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  ring

/-! ## The round -/

/-- **A fold round**: from the invariant at `(A − 1, d)`, every table leaves at most `N`
escaping pairs. -/
theorem card_foldEsc_le {N : ℕ} (hB : FoldRoundBound dom d A N)
    (hΦ : IsMultiaffine (m + 1 + κ) Φ) (hv : TViol κ dom Q Φ σ (A - 1) d)
    (u₀ w c₀ c₁ : E) : (foldEsc κ dom Q Φ σ A d u₀ w c₀ c₁).card ≤ N := by
  classical
  have h := hB (Fin m → Bool) (fun u ↦ Q (Fin.cons false u)) (fun u ↦ Q (Fin.cons true u))
    (wlin κ fun r ↦ Φ (0 :: r)) (wlin κ fun r ↦ Φ (1 :: r)) σ (fun F G hF hG hag ↦ by
      rw [← tclaim_joinT]
      exact hv _ (degLE_joinT hF hG) (by rwa [agreeT_joinT])) u₀ w c₀ c₁
  refine (Finset.card_le_card fun t ht ↦ ?_).trans h
  rw [foldEsc, Finset.mem_filter] at ht
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [TViol, not_forall, not_not] at ht
  obtain ⟨P, hP, hag, hc⟩ := ht.2
  refine ⟨P, hP, hag, ?_⟩
  rw [← tclaim_head κ Φ hΦ, hc, foldClaim_eq]

end
end LeanVM.Protocol.Whir.Sound
