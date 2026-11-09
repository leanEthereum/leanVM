/-
  LeanVM.Protocol.Whir.Sound.FoldRoundCywz

  The fold-round lemma the WHIR soundness takes, from the affine-combiner formalization.
-/

module

public import LeanVM.Protocol.Whir.Sound.FoldRound
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerReduction

/-!
# The fold-round lemma from [CYWZ26, preprint]

`FoldRoundBound dom d A Lθ N` (`LeanVM.Protocol.Whir.Sound.FoldRound`) is Annex B's
`lem:fold-list` in counting form. `foldRoundBound_of_lemma43` proves it from the affine-combiner
formalization (`LeanVM.Protocol.ToArkLib.Whir.AffineCombiner*`): part (i) is `card_badPremix_le`
(`Lθ = jl n (A − 1) d`, under `(A − 1)² > n d`), part (ii) `card_foldBad_le_nAff_of_lemma43` at
admissible interpolation parameters `(m, D, B)`, `N` any integer above
`|E| · nAff + 2 jl n (A − 1) d |E|²` (`ε_aff + 2L/|E|`, times `|E|³`). It carries that
formalization's one open input, `Lemma43` ([CYWZ26, Lemma 4.3]) over `E`, as a hypothesis.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.AffineCombiner Polynomial
  Finset

@[expose] public section

/-- **The fold-round lemma at admissible parameters**, from Lemma 4.3. -/
theorem foldRoundBound_of_lemma43 {n : ℕ} (dom : Fin n ↪ E) {d A m D B N : ℕ}
    (hgap : n * d < (A - 1) * (A - 1)) (hadm : Admissible n d A m D B)
    (h43 : Lemma43 E 2 D (bigM d A m D))
    (hN : (Fintype.card E : ℚ) * nAff (Fintype.card E) n d A m D B +
      2 * AffineCombiner.jl n (A - 1) d * (Fintype.card E : ℚ) ^ 2 ≤ N) :
    FoldRoundBound dom d A (AffineCombiner.jl n (A - 1) d) N := by
  classical
  intro ρ _ f g Λ₀ Λ₁ c hviol
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hagree : ∀ (P : ρ → E[X]) (w : ρ → Fin n → E), agreeT dom P w = agree dom P w :=
    fun P w ↦ by ext x; simp [agreeT, agree]
  refine le_trans (card_le_card fun θ hθ ↦ ?_) (hn ▸ card_badPremix_le dom f g (by rwa [hn]))
  rw [mem_filter] at hθ
  simp only [badPremix, mem_filter, mem_univ, true_and]
  intro hgood
  obtain ⟨u₀, v₀, c₀, v₁, c₁, hlt⟩ := hθ.2
  have hb := card_foldBad_le_nAff_of_lemma43 (p := 2) dom f g (by rwa [hn]) (by rwa [hn]) h43
    Λ₀ Λ₁ c (fun q hq ↦ by
      rw [mem_pairList] at hq
      exact hviol q.1 q.2 hq.1 hq.2.1 (by rw [hagree, hagree]; exact hq.2.2)) θ hgood u₀ v₀ c₀ v₁ c₁
  rw [hn] at hb
  have heq : (univ.filter fun t : E × E × E ↦ ∃ P : ρ → E[X], Sound.DegLE d P ∧
      A ≤ (agreeT dom P fun r x ↦ g r x + (t.2.1 + t.2.2 * dom x) * (f r x + θ * g r x)).card ∧
      (1 - t.1) * Λ₀ P + t.1 * Λ₁ P = (1 - t.1) * (u₀ + t.2.1 * v₀ + t.2.2 * c₀) +
        t.1 * ((c - v₀ + θ * u₀) + t.2.1 * v₁ + t.2.2 * c₁)) =
      foldBad dom f g A d Λ₀ Λ₁ c θ u₀ v₀ c₀ v₁ c₁ := by
    refine Finset.filter_congr fun t _ ↦ ?_
    refine exists_congr fun P ↦ ?_
    rw [mem_tupleList, hagree]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  rw [heq] at hlt
  have : ((foldBad dom f g A d Λ₀ Λ₁ c θ u₀ v₀ c₀ v₁ c₁).card : ℚ) ≤ N := hb.trans hN
  exact absurd (Nat.cast_le.mp this) (not_le.mpr hlt)

end
end LeanVM.Protocol.Whir.Sound
