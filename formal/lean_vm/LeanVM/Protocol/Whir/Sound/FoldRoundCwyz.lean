/-
  LeanVM.Protocol.Whir.Sound.FoldRoundCwyz

  The fold-round lemma the WHIR soundness takes, from the affine-combiner formalization.
-/

module

public import LeanVM.Protocol.Whir.Sound.FoldRound
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerLemma43
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployed
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerFoldRel

/-!
# The fold-round lemma from [CWYZ26]

`FoldRoundBound dom d A N` (`LeanVM.Protocol.Whir.Sound.FoldRound`) is Annex B's `lem:fold-list` in
counting form, relativised to a predicate on pairs. `foldRoundBound_of_admissible` proves it from
the affine-combiner formalization (`LeanVM.Protocol.ToArkLib.Whir.AffineCombiner*`):
`card_foldBadR_le_nAff'` at admissible
interpolation parameters `(m, D, B)`, under `(A − 1)² > n d`, `N` any integer above
`nAff + 2 jl n (A − 1) d |E|` (`ε_aff + 2L/|E|`, times `|E|²`). `foldRoundBound_of_ok`: a round
that passes the deployed check `foldRoundOK` (the Rust's `check_fold_round`) satisfies it at the
level's degree with `N = budget · |E|`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.AffineCombiner Polynomial
  Finset

@[expose] public section

/-- **The fold-round lemma at admissible parameters.** -/
theorem foldRoundBound_of_admissible {n : ℕ} (dom : Fin n ↪ E) {d A m D B N : ℕ}
    (hgap : n * d < (A - 1) * (A - 1)) (hadm : Admissible n d A m D B)
    (hN : nAff (Fintype.card E) n d A m D B +
      2 * AffineCombiner.jl n (A - 1) d * (Fintype.card E : ℚ) ≤ N) :
    FoldRoundBound dom d A N := by
  classical
  intro ρ _ f g Λ₀ Λ₁ c Bp hviol u₀ v c₀ c₁
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hagree : ∀ (P : ρ → E[X]) (w : ρ → Fin n → E), agreeT dom P w = agree dom P w :=
    fun P w ↦ by ext x; simp [agreeT, agree]
  have hb := card_foldBadR_le_nAff' dom f g 2 (by rwa [hn]) (by rwa [hn])
    Λ₀ Λ₁ c (fun p ↦ Bp p.1 p.2) (fun q hq hbq ↦ by
      rw [mem_pairList] at hq
      exact hviol q.1 q.2 hq.1 hq.2.1 (by rw [hagree, hagree]; exact hq.2.2) hbq) u₀ v c₀ c₁
  rw [hn] at hb
  have heq : (univ.filter fun t : E × E ↦ ∃ P : ρ → E[X], Sound.DegLE d P ∧
      A ≤ (agreeT dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x).card ∧
      (∀ F G, NearPairT dom d f g
        (agreeT dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x) F G → Bp F G) ∧
      (1 - t.1) * Λ₀ P + t.1 * Λ₁ P =
        u₀ + t.1 * (c - u₀) + t.1 ^ 2 * v + t.2 * c₀ + t.1 * t.2 * (c₁ - c₀)) =
      foldBadR dom f g A d Λ₀ Λ₁ c u₀ v c₀ c₁ (fun p ↦ Bp p.1 p.2) := by
    have hconv : ∀ (P : ρ → E[X]) (t : E × E) (F G : ρ → E[X]),
        NearPair dom f g d (agree dom P (foldW dom f g t.1 t.2)) (F, G) ↔
          NearPairT dom d f g (agree dom P fun r x ↦ g r x + (t.1 + t.2 * dom x) * f r x) F G := by
      intro P t F G
      unfold NearPair NearPairT
      constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, le_trans (le_of_eq ?_) h3⟩ <;>
        exact congrArg Finset.card (by ext x; simp only [Finset.mem_filter]; exact Iff.rfl)
    refine Finset.filter_congr fun t _ ↦ ?_
    refine exists_congr fun P ↦ ?_
    rw [mem_tupleList, hagree]
    exact ⟨fun ⟨a, b, hn, c⟩ ↦ ⟨⟨a, b⟩, fun p hp ↦ hn p.1 p.2 ((hconv P t p.1 p.2).mp hp), c⟩,
      fun ⟨⟨a, b⟩, hn, c⟩ ↦ ⟨a, b, fun F G hp ↦ hn (F, G) ((hconv P t F G).mpr hp), c⟩⟩
  rw [heq]
  exact Nat.cast_le.mp (hb.trans hN)

/-- **A deployed fold round**: passing `foldRoundOK` gives the fold-round lemma at the level's
degree with `N = budget · |E|`. -/
theorem foldRoundBound_of_ok {κ R k Aend j m D B budget : ℕ} (h64 : κ + R ≤ 64)
    (h : foldRoundOK κ R k Aend j m D B budget = true) :
    FoldRoundBound (domain κ R h64) (roundD κ k) (roundA k Aend j) (budget * Fintype.card E) := by
  obtain ⟨hadm, hgap, hrow⟩ := foldRoundOK_sound h
  refine foldRoundBound_of_admissible (domain κ R h64) hgap hadm ?_
  rw [show Fintype.card E = qE from LeanVM.Protocol.card_E, Nat.cast_mul]
  have hq : (0 : ℚ) < (qE : ℚ) := by positivity
  refine le_of_mul_le_mul_left ?_ hq
  calc (qE : ℚ) * (nAff qE (roundN κ R) (roundD κ k) (roundA k Aend j) m D B +
        2 * AffineCombiner.jl (roundN κ R) (roundA k Aend j - 1) (roundD κ k) * (qE : ℚ))
      = (qE : ℚ) * nAff qE (roundN κ R) (roundD κ k) (roundA k Aend j) m D B +
        2 * AffineCombiner.jl (roundN κ R) (roundA k Aend j - 1) (roundD κ k) * (qE : ℚ) ^ 2 := by
        ring
    _ ≤ budget * (qE : ℚ) ^ 2 := hrow
    _ = (qE : ℚ) * (budget * (qE : ℚ)) := by ring

end
end LeanVM.Protocol.Whir.Sound
