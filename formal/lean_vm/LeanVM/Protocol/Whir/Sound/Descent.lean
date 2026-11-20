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

/-! ## The descent as an algorithm -/

/-- **Near tuples are unique** on a set of at least `d + 3` columns: two of them agree on all but
two columns of it, more than `d`. -/
theorem nearT_unique {n m : ℕ} {dom : Fin n ↪ E} {Q : (Fin (m + 1) → Bool) → Fin n → E} {d : ℕ}
    {S : Finset (Fin n)} (hS : d + 3 ≤ S.card) {T T' : (Fin (m + 1) → Bool) → E[X]}
    (hT : NearT dom Q d S T) (hT' : NearT dom Q d S T') : T = T' := by
  classical
  by_contra hne
  have hsub : (S.filter fun x ↦ ¬ ∃ v, (T v).eval (dom x) ≠ Q v x) ∩
      (S.filter fun x ↦ ¬ ∃ v, (T' v).eval (dom x) ≠ Q v x) ⊆
      agreeT dom T Q ∩ agreeT dom T' Q := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inter.mp hx
    simp only [mem_filter, not_exists, not_not] at hx1 hx2
    exact mem_inter.mpr ⟨(mem_agreeT _ _ _ _).mpr hx1.2, (mem_agreeT _ _ _ _).mpr hx2.2⟩
  have h1 := card_filter_add_card_filter_not (s := S) fun x ↦ ∃ v, (T v).eval (dom x) ≠ Q v x
  have h2 := card_filter_add_card_filter_not (s := S) fun x ↦ ∃ v, (T' v).eval (dom x) ≠ Q v x
  have h3 := card_union_add_card_inter (S.filter fun x ↦ ¬ ∃ v, (T v).eval (dom x) ≠ Q v x)
    (S.filter fun x ↦ ¬ ∃ v, (T' v).eval (dom x) ≠ Q v x)
  have h4 : ((S.filter fun x ↦ ¬ ∃ v, (T v).eval (dom x) ≠ Q v x) ∪
      (S.filter fun x ↦ ¬ ∃ v, (T' v).eval (dom x) ≠ Q v x)).card ≤ S.card :=
    card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have h5 := card_le_card hsub
  have h6 := card_agreeT_inter_le dom hT.1 hT'.1 hne Q
  have h7 := hT.2
  have h8 := hT'.2
  omega

/-- **A near-tuple decoder**: on a word and a set of columns, only near tuples, and one whenever
one exists on at least `d + 3` columns. -/
structure NearDecoder where
  /-- The decoder. -/
  dec : ∀ {n m : ℕ}, (Fin n ↪ E) → ℕ → ((Fin (m + 1) → Bool) → Fin n → E) → Finset (Fin n) →
    Option ((Fin (m + 1) → Bool) → E[X])
  /-- It returns only near tuples. -/
  sound : ∀ {n m : ℕ} (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E) S T,
    dec dom d Q S = some T → NearT dom Q d S T
  /-- It returns one whenever one exists on at least `d + 3` columns. -/
  complete : ∀ {n m : ℕ} (dom : Fin n ↪ E) (d : ℕ) (Q : (Fin (m + 1) → Bool) → Fin n → E) S T,
    d + 3 ≤ S.card → NearT dom Q d S T → (dec dom d Q S).isSome

open Classical in
/-- **The descent within a level**: from a tuple after the rounds `rs`, at each round going back
the near tuple of the unfolded word on its agreement set with the fold, if that set reaches the
round's threshold. -/
noncomputable def descendRounds (D : NearDecoder) {n : ℕ} (dom : Fin n ↪ E) (d : ℕ)
    (thr : ℕ → ℕ) (O : ℕ → Fin n → E) (rs : List FoldRound) (m : ℕ)
    (U : (Fin m → Bool) → E[X]) : Option (Σ k, (Fin k → Bool) → E[X]) :=
  match _h : rs.getLast? with
  | none => some ⟨m, U⟩
  | some r =>
    let Q := rowsOf (m + 1) (foldsA dom rs.dropLast O)
    let S := agreeT dom U (foldQ dom r.alpha r.beta Q)
    if thr (rs.dropLast.length + 1) ≤ S.card then
      (D.dec dom d Q S).bind fun T ↦ descendRounds D dom d thr O rs.dropLast (m + 1) T
    else none
termination_by rs.length
decreasing_by
  have : rs ≠ [] := fun h0 ↦ by simp [h0] at _h
  simp only [List.length_dropLast]
  have := List.length_pos_of_ne_nil this
  omega

theorem descendRounds_nil (D : NearDecoder) {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ)
    (O : ℕ → Fin n → E) (m : ℕ) (U : (Fin m → Bool) → E[X]) :
    descendRounds D dom d thr O [] m U = some ⟨m, U⟩ := by
  rw [descendRounds]; rfl

theorem descendRounds_concat (D : NearDecoder) {n : ℕ} (dom : Fin n ↪ E) (d : ℕ) (thr : ℕ → ℕ)
    (O : ℕ → Fin n → E) (rs : List FoldRound) (r : FoldRound) (m : ℕ) (U : (Fin m → Bool) → E[X]) :
    descendRounds D dom d thr O (rs ++ [r]) m U =
      if thr (rs.length + 1) ≤ (agreeT dom U (foldQ dom r.alpha r.beta
          (rowsOf (m + 1) (foldsA dom rs O)))).card then
        (D.dec dom d (rowsOf (m + 1) (foldsA dom rs O))
          (agreeT dom U (foldQ dom r.alpha r.beta (rowsOf (m + 1) (foldsA dom rs O))))).bind
          fun T ↦ descendRounds D dom d thr O rs (m + 1) T
      else none := by
  rw [descendRounds]
  split
  · rename_i h; simp at h
  · rename_i r' h
    simp only [List.getLast?_concat, Option.some.injEq] at h
    subst h
    simp only [List.dropLast_concat]

/-- **The algorithm finds the descent**: a tuple failing the predicate after the rounds `rs`, whose
rounds' thresholds are at least `d + 3`, descends to a tuple of `m + |rs|` lanes failing the
level's predicate, of degree at most `d` and agreeing with the oracle on at least `thr 1 − 1`
columns when `rs` is not empty. -/
theorem descendRounds_of_not_predFrom (D : NearDecoder) {n : ℕ} (dom : Fin n ↪ E) (d : ℕ)
    (thr : ℕ → ℕ) (O : ℕ → Fin n → E) (B : TPred) :
    ∀ (rs : List FoldRound), (∀ j, 1 ≤ j → j ≤ rs.length → d + 3 ≤ thr j) →
      ∀ (m : ℕ) (U : (Fin m → Bool) → E[X]), ¬ predFrom dom d thr 0 O rs B m U →
      ∃ k, ∃ T : (Fin k → Bool) → E[X], descendRounds D dom d thr O rs m U = some ⟨k, T⟩ ∧
        k = m + rs.length ∧ ¬ B k T ∧
        (rs ≠ [] → DegLE d T ∧ thr 1 - 1 ≤ (agreeT dom T (rowsOf k O)).card) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil =>
    intro _ m U h
    exact ⟨m, U, descendRounds_nil D dom d thr O m U, rfl, h, fun h' ↦ absurd rfl h'⟩
  | append_singleton rs r ih =>
    intro hthr m U h
    rw [predFrom_concat] at h
    simp only [pullT, not_imp, not_forall] at h
    obtain ⟨hA, T₁, hnear, hT₁⟩ := h
    simp only [Nat.zero_add] at hA
    have hd3 : d + 3 ≤ (agreeT dom U (foldQ dom r.alpha r.beta
        (rowsOf (m + 1) (foldsA dom rs O)))).card :=
      (hthr (rs.length + 1) (by omega) (by simp)).trans hA
    obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp (D.complete dom d _ _ T₁ hd3 hnear)
    have hT'eq : T' = T₁ := nearT_unique hd3 (D.sound dom d _ _ _ hT') hnear
    subst hT'eq
    have hthr' : ∀ j, 1 ≤ j → j ≤ rs.length → d + 3 ≤ thr j :=
      fun j h1 h2 ↦ hthr j h1 (by simp; omega)
    rw [descendRounds_concat]
    simp only [hA, ↓reduceIte, hT', Option.bind_some]
    by_cases hne : rs = []
    · subst hne
      rw [descendRounds_nil]
      refine ⟨m + 1, T', rfl, by simp, hT₁, fun _ ↦ ⟨hnear.1, ?_⟩⟩
      have := card_agreeT_of_near hnear
      simp only [List.length_nil, Nat.zero_add, foldsA_nil] at hA this ⊢
      omega
    · obtain ⟨k, T, hdesc, hk, hT, hrest⟩ := ih hthr' (m + 1) T' hT₁
      exact ⟨k, T, hdesc, by rw [hk]; simp; omega, hT, fun _ ↦ hrest hne⟩

open Classical in
/-- **The descent across levels**: the final polynomial descended through the last level, then at
each level going back the polynomial of the message reached and the high part, descended through
that level's rounds. -/
noncomputable def descendTrace (D : NearDecoder) (codes : ℕ → LevelCode)
    (cs : List (ℕ × ℕ × Word)) : WhirTrace → ℕ → Option (Σ k, (Fin k → Bool) → E[X])
  | .final rounds folded, i => descendRounds D (codes i).dom (codes i).deg (codes i).thr
      (laneO i cs (codes i).n) rounds 0 fun _ ↦ polyOf folded
  | .mid rounds high rest, i => (descendTrace D codes cs rest (i + 1)).bind fun T' ↦
      if h : T'.1 = (codes (i + 1)).ℓ ∧ (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ then
        descendRounds D (codes i).dom (codes i).deg (codes i).thr (laneO i cs (codes i).n) rounds 0
          fun _ ↦ msgPoly (codes i).κ (joinMsg h.2 (msgT (codes (i + 1)).κ (h.1 ▸ T'.2))) +
            hatE (codes i).κ * polyOf high
      else none

/-- **The algorithm descends a good trace**: with every round's threshold at least the level's
degree plus three, the descent returns a tuple of level `i`'s lanes failing its predicate, of the
level's degree and agreeing with its oracle on its starting threshold when it folds and its
threshold exceeds its folds. -/
theorem descendTrace_of_traceGood (D : NearDecoder) (codes : ℕ → LevelCode)
    (cs : List (ℕ × ℕ × Word))
    (hthr : ∀ i j, 1 ≤ j → j ≤ (codes i).ℓ → (codes i).deg + 3 ≤ (codes i).thr j) :
    ∀ (tr : WhirTrace) (i : ℕ) (B : List (ℕ × ℕ × Word) → TPred), traceGood codes i B tr cs →
      ∃ T : (Fin (codes i).ℓ → Bool) → E[X], descendTrace D codes cs tr i = some ⟨_, T⟩ ∧
        ¬ B cs (codes i).ℓ T ∧
        (1 ≤ (codes i).ℓ → (codes i).ℓ < (codes i).A → DegLE (codes i).deg T ∧
          (codes i).thr 0 ≤
            (agreeT (codes i).dom T (rowsOf (codes i).ℓ (laneO i cs (codes i).n))).card) := by
  intro tr
  induction tr with
  | final rounds folded =>
    intro i B h
    obtain ⟨-, hlen, hbad⟩ := h
    obtain ⟨k, T, hdesc, hk, hT, hrest⟩ := descendRounds_of_not_predFrom D (codes i).dom
      (codes i).deg (codes i).thr (laneO i cs (codes i).n) (B cs) rounds
      (fun j h1 h2 ↦ hthr i j h1 (by omega)) 0 _ hbad
    rw [hlen, zero_add] at hk
    subst hk
    refine ⟨T, hdesc, hT, fun h1 hA ↦ ?_⟩
    have hne : rounds ≠ [] := by
      intro h0; rw [h0] at hlen; simp at hlen; omega
    obtain ⟨hd, hag⟩ := hrest hne
    refine ⟨hd, le_trans (le_of_eq ?_) hag⟩
    simp only [LevelCode.thr]
    omega
  | mid rounds high rest ih =>
    intro i B h
    obtain ⟨hκ, hlen, h⟩ := h
    obtain ⟨T', hdesc', hT', -⟩ := ih (i + 1) _ h
    have hbad : ¬ roundPred i (codes i) B rounds cs 0 fun _ ↦
        msgPoly (codes i).κ (joinMsg hκ (msgT (codes (i + 1)).κ T')) +
          hatE (codes i).κ * polyOf high := fun hb ↦ hT' fun h' ↦ by
      cases h'
      exact hb
    obtain ⟨k, T, hdesc, hk, hT, hrest⟩ := descendRounds_of_not_predFrom D (codes i).dom
      (codes i).deg (codes i).thr (laneO i cs (codes i).n) (B cs) rounds
      (fun j h1 h2 ↦ hthr i j h1 (by omega)) 0 _ hbad
    rw [hlen, zero_add] at hk
    subst hk
    have hc : (codes (i + 1)).ℓ = (codes (i + 1)).ℓ ∧
        (codes i).κ = (codes (i + 1)).ℓ + (codes (i + 1)).κ := ⟨rfl, hκ⟩
    refine ⟨T, ?_, hT, fun h1 hA ↦ ?_⟩
    · rw [descendTrace, hdesc', Option.bind_some, dite_eq_left hc]
      exact hdesc
    · have hne : rounds ≠ [] := by
        intro h0; rw [h0] at hlen; simp at hlen; omega
      obtain ⟨hd, hag⟩ := hrest hne
      refine ⟨hd, le_trans (le_of_eq ?_) hag⟩
      simp only [LevelCode.thr]
      omega

end
end LeanVM.Protocol.Whir.Sound
