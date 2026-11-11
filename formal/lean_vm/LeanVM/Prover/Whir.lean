/-
  LeanVM.Prover.Whir

  The executable WHIR opening makes the specification's moves.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Prover.WhirBasis
public import LeanVM.Prover.Ring

/-!
# The opening

`corr_openingFast`: for a stack of at most `64` variables, the executable opening on claim
descriptions, `openingFast μ R q.values.toArray claims`, makes the moves of the specification's
`honestOpening μ R q (claims.map ClaimDesc.denote)`: the same scalars sent, the same words
committed (at every position), each challenge and each opening given to both.

Along the levels (`corr_levelsA`) the executable carries the verifier's state `s`, the weight
table `W` and the folded stack `g` as arrays, the specification the same state, `W` as a list
and recomputes `g = foldAll f₀ s.folds`; the invariant is `W.toList = W` and
`g.toList = foldAll f₀ s.folds`. Each round polynomial is the specification's
(`corr_roundA`), each fold in place is the specification's fold (`toList_foldPairsA_foldAll`),
the level words are the specification's (`levelWordFast_eq`), the out-of-domain and query
tables are (`eqKernel_eq_tableOf`, `toList_queryTableA`), and gluing is (`toList_glueTablesA`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Complete LeanVM.Protocol.EndToEnd
open LeanVM.Prover.Enc

@[expose] public section

/-! ## Moves -/

section Moves

variable {α β γ : Type} {S : α → β → Prop}

theorem corrW_sampleE {f : E → Script α} {g : E → Script β} (h : ∀ c, Corr S (f c) (g c)) :
    Corr S (Script.sampleE >>= f) (Script.sampleE >>= g) := h

theorem corrW_sendE {x y : E} {f : Unit → Script α} {g : Unit → Script β} (hxy : x = y)
    (h : Corr S (f ()) (g ())) : Corr S (Script.sendE x >>= f) (Script.sendE y >>= g) :=
  ⟨hxy, h⟩

theorem corrW_sendList {xs ys : List E} {f : Unit → Script α} {g : Unit → Script β}
    (hxy : xs = ys) (h : Corr S (f ()) (g ())) :
    Corr S (Script.sendList xs >>= f) (Script.sendList ys >>= g) := by
  subst hxy
  exact Corr.bind' (Corr.sendList xs) fun a b _ ↦ by cases a; cases b; exact h

theorem corrW_grindS {f : Unit → Script α} {g : Unit → Script β} (h : Corr S (f ()) (g ())) :
    Corr S (Script.grindS >>= f) (Script.grindS >>= g) := h

theorem corrW_commitS {w w' : Word} {f : Unit → Script α} {g : Unit → Script β} (hw : w = w')
    (h : Corr S (f ()) (g ())) : Corr S (Script.commitS w >>= f) (Script.commitS w' >>= g) :=
  ⟨hw, h⟩

theorem corrW_queryS {f : List (List K) → Script α} {g : List (List K) → Script β}
    (h : ∀ rows, Corr S (f rows) (g rows)) : Corr S (Script.queryS >>= f) (Script.queryS >>= g) :=
  h

theorem corrW_same (H : Script γ) {f : γ → Script α} {g : γ → Script β}
    (h : ∀ a, Corr S (f a) (g a)) : Corr S (H >>= f) (H >>= g) :=
  Corr.bind_same H h

end Moves

/-! ## Rounds -/

/-- **The round polynomial**: the executable sends the specification's coefficients and returns
the verifier's quadratic. -/
theorem corr_roundA (claim : E) (W g : Array E) :
    Corr (fun a _ ↦ a = roundQuad claim W.toList g.toList) (roundA claim W g)
      (hRound W.toList g.toList) := by
  refine ⟨roundC0A_eq W g, roundC2A_eq W g, ?_⟩
  show [roundC0A W g, claim + sumE [roundC2A W g], roundC2A W g] = roundQuad claim W.toList g.toList
  rw [roundC0A_eq, roundC2A_eq]
  rfl

/-- The round polynomial of specification tables given as arrays. -/
theorem corr_roundA' {claim : E} {W g : Array E} {W' g' : List E} (hW : W.toList = W')
    (hg : g.toList = g') :
    Corr (fun a _ ↦ a = roundQuad claim W' g') (roundA claim W g) (hRound W' g') := by
  subst hW hg
  exact corr_roundA claim W g

/-- **The fold rounds**, both tables folded in place. -/
theorem corr_foldRoundsA (f₀ : List E) :
    ∀ (n : ℕ) (s : WhirStateT) (lf : List E) (W g : Array E), g.toList = foldAll f₀ s.folds →
      Corr (fun a b ↦ a.1 = b.1.forget ∧ a.2.1 = b.2.1 ∧ a.2.2.1.toList = b.2.2 ∧
          a.2.2.2.toList = foldAll f₀ b.1.folds)
        (foldRoundsA n s.forget lf W g) (hFoldRounds f₀ n s lf W.toList)
  | 0, s, lf, W, g, hg => by
    simp only [foldRoundsA, hFoldRounds]
    exact ⟨rfl, rfl, rfl, hg⟩
  | n + 1, s, lf, W, g, hg => by
    simp only [foldRoundsA, hFoldRounds]
    refine corrW_sampleE fun c ↦ ?_
    refine Corr.bind' (corr_roundA' (toList_foldPairsA c W) (toList_foldPairsA_foldAll hg c))
      fun quad _ hq ↦ ?_
    subst hq
    have := corr_foldRoundsA f₀ n
      { s with target := polyEval s.quad c,
               quad := roundQuad (polyEval s.quad c) (foldPairs c W.toList)
                 (foldAll f₀ (s.folds ++ [c])),
               folds := s.folds ++ [c] } (lf ++ [c]) (foldPairsA c W) (foldPairsA c g)
      (toList_foldPairsA_foldAll hg c)
    rwa [toList_foldPairsA] at this

/-- **The tail rounds.** -/
theorem corr_tailRoundsA : ∀ (n : ℕ) (target : E) (quad : List E) (W g : Array E),
    Corr (fun _ _ ↦ True) (tailRoundsA n quad W g)
      (hTailRounds n target quad W.toList g.toList)
  | 0, _, _, _, _ => by simp only [tailRoundsA, hTailRounds]; trivial
  | n + 1, target, quad, W, g => by
    simp only [tailRoundsA, hTailRounds]
    refine corrW_sampleE fun c ↦ ?_
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte]; trivial
    · simp only [hn, ↓reduceIte]
      refine Corr.bind' (corr_roundA' (toList_foldPairsA c W) (toList_foldPairsA c g))
        fun quad' _ hq ↦ ?_
      subst hq
      have := corr_tailRoundsA n (polyEval quad c)
        (roundQuad (polyEval quad c) (foldPairs c W.toList) (foldPairs c g.toList))
        (foldPairsA c W) (foldPairsA c g)
      rw [toList_foldPairsA, toList_foldPairsA] at this
      rw [← Script.bind_ret (tailRoundsA n _ _ _)]
      exact Corr.bind (fun _ _ _ ↦ trivial) _ _ this

/-- The query positions are received as the specification receives them. -/
theorem sampleQueriesS_eq (depth : ℕ) : ∀ fuel remaining : ℕ,
    sampleQueriesS depth fuel remaining = hSampleQueriesAux depth fuel remaining
  | 0, _ => rfl
  | fuel + 1, remaining => by
    simp only [sampleQueriesS, hSampleQueriesAux, sampleQueriesS_eq depth fuel]

/-! ## The levels -/

theorem corrW_pure {α β γ δ : Type} {S : α → β → Prop} {a : γ} {b : δ} {f : γ → Script α}
    {g : δ → Script β} (h : Corr S (f a) (g b)) : Corr S (pure a >>= f) (pure b >>= g) := h

/-- The tail rounds, then nothing, from related tables. -/
theorem corr_tailRoundsA' {n : ℕ} {target : E} {quad quad' : List E} {W g : Array E}
    {W' g' : List E} (hq : quad = quad') (hW : W.toList = W') (hg : g.toList = g') :
    Corr (fun _ _ ↦ True) (tailRoundsA n quad W g)
      (hTailRounds n target quad' W' g' >>= fun _ ↦ pure ()) := by
  subst hq hW hg
  rw [← Script.bind_ret (tailRoundsA n quad W g)]
  exact Corr.bind (fun _ _ _ ↦ trivial) _ _ (corr_tailRoundsA _ _ _ _ _)

/-- **The WHIR levels**: from related tables, the executable levels make the specification's
moves. -/
theorem corr_levelsA {μ : ℕ} (hμ : μ ≤ 64) (f₀ : List E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirStateT) (W g : Array E),
      g.toList = foldAll f₀ s.folds →
      Corr (fun _ _ ↦ True) (levelsA μ index levels s.forget W g)
        (hLevels μ f₀ index levels s W.toList) := by
  intro levels
  induction levels with
  | nil => intro _ _ _ _ _; simp only [levelsA, hLevels]; trivial
  | cons level rest ih =>
    intro index s W g hg
    simp only [levelsA, hLevels]
    refine Corr.bind' (corr_foldRoundsA f₀ level.fold s [] W g hg) fun a b hab ↦ ?_
    obtain ⟨s₁, lf, W₁, g₁⟩ := a
    obtain ⟨sb, lfb, Wb⟩ := b
    obtain ⟨h1, h2, h3, hg₁⟩ := hab
    simp only at h1 h2 h3 hg₁
    subst h1 h2 h3
    dsimp only
    rw [show sb.forget.folds = sb.folds from rfl]
    have hm : μ - sb.folds.length ≤ 64 := by omega
    have hih : ∀ (sp : WhirState) (s' : WhirStateT) (Wa : Array E) (Wl : List E), sp = s'.forget →
        Wa.toList = Wl → g₁.toList = foldAll f₀ s'.folds →
        Corr (fun _ _ ↦ True) (levelsA μ (index + 1) rest sp Wa g₁)
          (hLevels μ f₀ (index + 1) rest s' Wl) := by
      intro sp s' Wa Wl hsp hW hg'
      subst hsp hW
      exact ih (index + 1) s' Wa g₁ hg'
    cases rest with
    | nil =>
      refine corrW_sendList hg₁ (corrW_pure ?_)
      dsimp only
      refine corrW_grindS ?_
      rw [sampleQueriesS_eq]
      refine corrW_same _ fun queries ↦ ?_
      refine corrW_sampleE fun lam ↦ ?_
      refine corrW_queryS fun words ↦ ?_
      refine Corr.bind' (corr_roundA'
        (W' := queryTable (μ - sb.folds.length) queries (powers lam queries.length))
        (toList_queryTableA hm _ _) hg₁) fun quad _ hq ↦ ?_
      subst hq
      refine corr_tailRoundsA' rfl ?_ hg₁
      rw [toList_glueTablesA]
      simp [toList_queryTableA hm]
    | cons next rest' =>
      refine corrW_commitS (by rw [levelWordFast_eq (by omega), hg₁]) ?_
      refine Corr.bind' (corr_sampleN _) fun z z' hz ↦ ?_
      obtain ⟨rfl, hz⟩ := hz
      refine corrW_sendE (by rw [mleA_eq, hg₁]) ?_
      rw [mleA_eq, hg₁]
      refine Corr.bind' (corr_roundA' (W' := tableOf (μ - sb.folds.length) (eqEval z))
        (by rw [toList_eqTable, eqKernel_eq_tableOf z hz]) hg₁) fun quad _ hq ↦ ?_
      subst hq
      refine corrW_pure ?_
      dsimp only
      refine corrW_grindS ?_
      rw [sampleQueriesS_eq]
      refine corrW_same _ fun queries ↦ ?_
      refine corrW_sampleE fun lam ↦ ?_
      refine corrW_queryS fun words ↦ ?_
      refine Corr.bind' (corr_roundA'
        (W' := queryTable (μ - sb.folds.length) queries (powers lam queries.length))
        (toList_queryTableA hm _ _) hg₁) fun quad _ hq ↦ ?_
      subst hq
      refine hih _ (glueT lam sb _) _ _ rfl ?_ (by rw [glue_folds]; exact hg₁)
      rw [toList_glueTablesA]
      simp [toList_queryTableA hm, toList_eqTable, eqKernel_eq_tableOf z hz]

/-! ## The opening -/

/-- **The executable opening makes the specification's moves**: on claim descriptions and the
stack array of `q`, `openingFast` and `honestOpening` on the claims the descriptions denote send
the same scalars and commit the same words, for every challenge and opening. -/
theorem corr_openingFast {μ : ℕ} (hμ : μ ≤ 64) (R : ℕ) (q : Column μ)
    (claims : List ClaimDesc) :
    Corr (fun _ _ ↦ True) (openingFast μ R q.values.toArray claims)
      (honestOpening μ R q (claims.map ClaimDesc.denote)) := by
  simp only [openingFast, honestOpening, List.length_map]
  refine corrW_sampleE fun c ↦ ?_
  cases Whir.ladder μ R with
  | none => trivial
  | some config =>
    dsimp only
    simp only [hWhirRun]
    have htarget : dot (powers c claims.length) (claims.map fun d ↦ d.denote.2) =
        dot (powers c claims.length) ((claims.map ClaimDesc.denote).map (·.2)) := by
      rw [List.map_map]; rfl
    rw [htarget]
    refine Corr.bind' (corr_roundA' (toList_basisTableA μ _ claims) (toList_stackTableA q))
      fun quad _ hq ↦ ?_
    subst hq
    have := corr_levelsA hμ (stackTable μ q) config 0
      ⟨dot (powers c claims.length) ((claims.map ClaimDesc.denote).map (·.2)),
        roundQuad (dot (powers c claims.length) ((claims.map ClaimDesc.denote).map (·.2)))
          (basisTable μ (powers c claims.length) (claims.map ClaimDesc.denote))
          (stackTable μ q), [], []⟩
      (basisTableA μ (powers c claims.length) claims) (stackTableA μ q.values.toArray)
      (by rw [toList_stackTableA]; rfl)
    rwa [toList_basisTableA] at this

end
end LeanVM.Prover
