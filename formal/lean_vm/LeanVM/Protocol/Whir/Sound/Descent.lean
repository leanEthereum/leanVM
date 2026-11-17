/-
  LeanVM.Protocol.Whir.Sound.Descent

  A good trace descends to a level-0 list member whose stack is not bad.
-/

module

public import LeanVM.Protocol.Whir.Sound.Spec

/-!
# The descent of a good trace

`traceGood codes 0 (lvl0Pred μ Bad) tr cs` (`Spec`) says that the final polynomial of the trace
does not satisfy level 0's predicate pulled back through every round and level. Unfolding the
pull-backs gives the descent the agreement-set extractor computes:

* `exists_of_not_predFrom`: within a level, a tuple failing the predicate after its rounds has a
  near tuple at each round going back, failing the predicate before it, down to a tuple of the
  level's lanes of degree at most `d`, agreeing with the level's oracle on at least the first
  round's threshold less one: `thr 1 − 1 = thr 0`.
* `exists_of_traceGood`: across levels, through each level's high part (`nextPred`), down to level
  `i`'s lanes.
* `exists_good_candidate`: at level 0, a list member at level 0's threshold, so its stack is a
  candidate of the committed word, and not bad.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd Polynomial Finset

@[expose] public section

/-- A near tuple keeps all but one column of the set it is near on. -/
theorem card_agreeT_of_near {n m : ℕ} {dom : Fin n ↪ E} {Q : (Fin (m + 1) → Bool) → Fin n → E}
    {d : ℕ} {S : Finset (Fin n)} {T : (Fin (m + 1) → Bool) → E[X]} (h : NearT dom Q d S T) :
    S.card - 1 ≤ (agreeT dom T Q).card := by
  classical
  obtain ⟨-, hloss⟩ := h
  have hsub : S.filter (fun x ↦ ¬ ∃ v, (T v).eval (dom x) ≠ Q v x) ⊆ agreeT dom T Q := by
    intro x hx
    obtain ⟨-, hx⟩ := mem_filter.mp hx
    simp only [not_exists, not_not] at hx
    exact (mem_agreeT _ _ _ _).mpr hx
  have := card_filter_add_card_filter_not (s := S) fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x
  have := card_le_card hsub
  omega

/-- **The descent within a level**: a tuple failing the predicate after the rounds `rs` (from
round `0`) has a tuple of `m + |rs|` lanes failing the level's predicate, of degree at most `d`
and agreeing with the oracle on at least `thr 1 − 1` columns when `rs` is not empty. -/
theorem exists_of_not_predFrom {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ)
    (O : ℕ → Fin n → E) (B : TPred) :
    ∀ (rs : List FoldRound) (m : ℕ) (U : (Fin m → Bool) → E[X]),
      ¬ predFrom dom d thr 0 O rs B m U →
      ∃ k, ∃ T : (Fin k → Bool) → E[X], k = m + rs.length ∧ ¬ B k T ∧
        (rs ≠ [] → DegLE d T ∧ thr 1 - 1 ≤ (agreeT dom T (rowsOf k O)).card) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => intro m U h; exact ⟨m, U, rfl, h, fun h' ↦ absurd rfl h'⟩
  | append_singleton rs r ih =>
    intro m U h
    rw [predFrom_concat] at h
    simp only [pullT, not_imp, not_forall] at h
    obtain ⟨hA, T₁, hnear, hT₁⟩ := h
    by_cases hne : rs = []
    · subst hne
      refine ⟨m + 1, T₁, by simp, hT₁, fun _ ↦ ⟨hnear.1, ?_⟩⟩
      have := card_agreeT_of_near hnear
      simp only [List.length_nil, zero_add, foldsA_nil] at hA this
      omega
    · obtain ⟨k, T, hk, hT, hrest⟩ := ih (m + 1) T₁ hT₁
      exact ⟨k, T, by rw [hk]; simp; omega, hT, fun _ ↦ hrest hne⟩

/-- **The descent across levels**: a good trace from level `i` has a tuple of level `i`'s lanes
failing its predicate, of the level's degree and agreeing with its oracle on at least its
starting threshold when the level folds at least once and its threshold exceeds its folds. -/
theorem exists_of_traceGood (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) :
    ∀ (tr : WhirTrace) (i : ℕ) (B : List (ℕ × ℕ × Word) → TPred), traceGood codes i B tr cs →
      ∃ T : (Fin (codes i).ℓ → Bool) → E[X], ¬ B cs (codes i).ℓ T ∧
        (1 ≤ (codes i).ℓ → (codes i).ℓ < (codes i).A → DegLE (codes i).deg T ∧
          (codes i).thr 0 ≤
            (agreeT (codes i).dom T (rowsOf (codes i).ℓ (laneO i cs (codes i).n))).card) := by
  intro tr
  induction tr with
  | final rounds folded =>
    intro i B h
    obtain ⟨-, hlen, hbad⟩ := h
    obtain ⟨k, T, hk, hT, hrest⟩ := exists_of_not_predFrom (codes i).dom (codes i).deg
      (codes i).thr (laneO i cs (codes i).n) (B cs) rounds 0 _ hbad
    rw [hlen, zero_add] at hk
    subst hk
    refine ⟨T, hT, fun h1 hA ↦ ?_⟩
    have hne : rounds ≠ [] := by
      intro h0; rw [h0] at hlen; simp at hlen; omega
    obtain ⟨hd, hag⟩ := hrest hne
    refine ⟨hd, le_trans (le_of_eq ?_) hag⟩
    simp only [LevelCode.thr]
    omega
  | mid rounds high rest ih =>
    intro i B h
    obtain ⟨hκ, hlen, h⟩ := h
    obtain ⟨T', hT', -⟩ := ih (i + 1) _ h
    have hbad : ¬ roundPred i (codes i) B rounds cs 0 fun _ ↦
        msgPoly (codes i).κ (joinMsg hκ (msgT (codes (i + 1)).κ T')) +
          hatE (codes i).κ * polyOf high := fun hb ↦ hT' fun h' ↦ by
      cases h'
      exact hb
    obtain ⟨k, T, hk, hT, hrest⟩ := exists_of_not_predFrom (codes i).dom (codes i).deg
      (codes i).thr (laneO i cs (codes i).n) (B cs) rounds 0 _ hbad
    rw [hlen, zero_add] at hk
    subst hk
    refine ⟨T, hT, fun h1 hA ↦ ?_⟩
    have hne : rounds ≠ [] := by
      intro h0; rw [h0] at hlen; simp at hlen; omega
    obtain ⟨hd, hag⟩ := hrest hne
    refine ⟨hd, le_trans (le_of_eq ?_) hag⟩
    simp only [LevelCode.thr]
    omega

/-- A good trace has commitments. -/
theorem traceGood_ne_nil (codes : ℕ → LevelCode) (cs : List (ℕ × ℕ × Word)) :
    ∀ (tr : WhirTrace) (i : ℕ) (B : List (ℕ × ℕ × Word) → TPred), traceGood codes i B tr cs →
      cs ≠ []
  | .final _ _, _, _, h => List.ne_nil_of_length_pos (by have := h.1; omega)
  | .mid _ _ rest, i, _, h => traceGood_ne_nil codes cs rest (i + 1) _ h.2.2

/-- A level-0 tuple at level 0's threshold whose stacks are not all bad has a candidate of the
committed word that is not bad. -/
theorem good_candidate_of_tuple {μ R : ℕ} (P₀ : LevelCode) (hμ : laneBits ≤ μ)
    (hκ : P₀.κ = μ - laneBits) (hR : P₀.R = R) (hℓ : P₀.ℓ = laneBits) (hthr : P₀.deg < P₀.thr 0)
    (Bad : Column μ → Prop) (cs : List (ℕ × ℕ × Word)) (T : (Fin P₀.ℓ → Bool) → E[X])
    (hT : ¬ lvl0Pred μ Bad cs P₀.ℓ T) (hd : DegLE P₀.deg T)
    (hag : P₀.thr 0 ≤ (agreeT P₀.dom T (rowsOf P₀.ℓ (laneO 0 cs P₀.n))).card) :
    ∃ q ∈ Candidates μ R (P₀.thr 0) (wordOf cs 0), ¬ Bad q := by
  obtain ⟨κ, R', ℓ, A, h64, hR1⟩ := P₀
  dsimp only at hκ hR hℓ hthr hT hd hag ⊢
  subst hκ hR hℓ
  obtain ⟨q, hq, hUq⟩ := exists_candidate_of_tuple hμ h64 hthr cs T hd hag
  refine ⟨q, hq, fun hb ↦ hT fun _ q' hq' ↦ ?_⟩
  have : q' = q := eq_of_blockOf_eq hμ fun u ↦ by
    have h1 := hq' ((bitsEquiv laneBits).symm u)
    have h2 := hUq ((bitsEquiv laneBits).symm u)
    rw [Equiv.apply_symm_apply] at h1 h2
    exact h1.symm.trans h2
  rw [this]
  exact hb

/-- **A good trace ends on a good candidate**: at level 0, with level 0's code on the stack's
`μ` variables and `2^6` lanes, its threshold above its degree and its folds, some candidate of
the committed word at level 0's threshold is not bad. -/
theorem exists_good_candidate (codes : ℕ → LevelCode) {μ R : ℕ} (hμ : laneBits ≤ μ)
    (hκ₀ : (codes 0).κ = μ - laneBits) (hR₀ : (codes 0).R = R) (hℓ₀ : (codes 0).ℓ = laneBits)
    (hthr : (codes 0).deg < (codes 0).thr 0) (hA₀ : (codes 0).ℓ < (codes 0).A)
    (Bad : Column μ → Prop) (tr : WhirTrace) (cs : List (ℕ × ℕ × Word))
    (h : traceGood codes 0 (lvl0Pred μ Bad) tr cs) :
    ∃ q ∈ Candidates μ R ((codes 0).thr 0) (wordOf cs 0), ¬ Bad q := by
  obtain ⟨T, hT, hrest⟩ := exists_of_traceGood codes cs tr 0 (lvl0Pred μ Bad) h
  obtain ⟨hd, hag⟩ := hrest (by rw [hℓ₀]; decide) hA₀
  exact good_candidate_of_tuple (codes 0) hμ hκ₀ hR₀ hℓ₀ hthr Bad cs T hT hd hag

end
end LeanVM.Protocol.Whir.Sound
