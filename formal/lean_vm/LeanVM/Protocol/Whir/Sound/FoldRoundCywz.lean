/-
  LeanVM.Protocol.Whir.Sound.FoldRoundCywz

  The fold-round lemma the WHIR soundness takes, from the affine-combiner formalization.
-/

module

public import LeanVM.Protocol.Whir.Sound.FoldRound
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerLemma43
public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployed

/-!
# The fold-round lemma from [CYWZ26, preprint]

`FoldRoundBound dom d A N` (`LeanVM.Protocol.Whir.Sound.FoldRound`) is Annex B's `lem:fold-list` in
counting form. `foldRoundBound_of_admissible` proves it from the affine-combiner formalization
(`LeanVM.Protocol.ToArkLib.Whir.AffineCombiner*`): `card_foldBad_le_nAff'` at admissible
interpolation parameters `(m, D, B)`, under `(A − 1)² > n d`, `N` any integer above
`|E| · nAff + 2 jl n (A − 1) d |E|²` (`ε_aff + 2L/|E|`, times `|E|³`). `foldRoundBound_of_ok`: a
round that passes the deployed check `foldRoundOK` (the Rust's `check_fold_round`) satisfies it
at the level's degree with `N = budget · |E|²`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Whir LeanVM.Protocol.Whir.AffineCombiner Polynomial
  Finset

@[expose] public section

/-- **The fold-round lemma at admissible parameters.** -/
theorem foldRoundBound_of_admissible {n : ℕ} (dom : Fin n ↪ E) {d A m D B N : ℕ}
    (hgap : n * d < (A - 1) * (A - 1)) (hadm : Admissible n d A m D B)
    (hN : (Fintype.card E : ℚ) * nAff (Fintype.card E) n d A m D B +
      2 * AffineCombiner.jl n (A - 1) d * (Fintype.card E : ℚ) ^ 2 ≤ N) :
    FoldRoundBound dom d A N := by
  classical
  intro ρ _ f g Λ₀ Λ₁ c hviol u₀ v₀ c₀ v₁ c₁
  have hn : Fintype.card (Fin n) = n := Fintype.card_fin n
  have hagree : ∀ (P : ρ → E[X]) (w : ρ → Fin n → E), agreeT dom P w = agree dom P w :=
    fun P w ↦ by ext x; simp [agreeT, agree]
  have hb := card_foldBad_le_nAff' 2 dom f g (by rwa [hn]) (by rwa [hn])
    Λ₀ Λ₁ c (fun q hq ↦ by
      rw [mem_pairList] at hq
      exact hviol q.1 q.2 hq.1 hq.2.1 (by rw [hagree, hagree]; exact hq.2.2)) u₀ v₀ c₀ v₁ c₁
  rw [hn] at hb
  have heq : (univ.filter fun t : E × E × E ↦ ∃ P : ρ → E[X], Sound.DegLE d P ∧
      A ≤ (agreeT dom P fun r x ↦ g r x + (t.2.1 + t.2.2 * dom x) * f r x).card ∧
      (1 - t.1) * Λ₀ P + t.1 * Λ₁ P = (1 - t.1) * (u₀ + t.2.1 * v₀ + t.2.2 * c₀) +
        t.1 * ((c - v₀) + t.2.1 * v₁ + t.2.2 * c₁)) =
      foldBad dom f g A d Λ₀ Λ₁ c u₀ v₀ c₀ v₁ c₁ := by
    refine Finset.filter_congr fun t _ ↦ ?_
    refine exists_congr fun P ↦ ?_
    rw [mem_tupleList, hagree]
    exact ⟨fun ⟨a, b, c⟩ ↦ ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ ↦ ⟨a, b, c⟩⟩
  rw [heq]
  exact Nat.cast_le.mp (hb.trans hN)

/-- **A deployed fold round**: passing `foldRoundOK` gives the fold-round lemma at the level's
degree with `N = budget · |E|²`. -/
theorem foldRoundBound_of_ok {κ R k Aend j m D B budget : ℕ} (h64 : κ + R ≤ 64)
    (h : foldRoundOK κ R k Aend j m D B budget = true) :
    FoldRoundBound (domain κ R h64) (roundD κ k) (roundA k Aend j)
      (budget * Fintype.card E ^ 2) := by
  obtain ⟨hadm, hgap, hrow⟩ := foldRoundOK_sound h
  refine foldRoundBound_of_admissible (domain κ R h64) hgap hadm ?_
  rw [LeanVM.Protocol.card_E]
  push_cast
  exact hrow

end
end LeanVM.Protocol.Whir.Sound
