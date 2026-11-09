module

public import Common.SeedKey
public import Common.Eager

@[expose] public section

/-!
# A signer swapped for one with the same values

Two hash-query schemes `S₁` and `S₂` (`Common.SufCma.SchemeWithHash`) whose honest algorithms,
evaluated on any answer function `f`, give the same public key and the same signatures
(`StaticSwap`) have the same success in the random-oracle game (`StaticSwap.success_eq`), so a
random-oracle bound at the adversary's own count for `S₁` is one for `S₂`
(`StaticSwap.romBoundAdv`, `Common.AdvBudget`).

The order of the hash calls is free: the success is compared with the honest algorithms' part of
the random oracle sampled in advance (`Common.Eager`), on which the honest algorithms are
functions of the table.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common.SufCma

/-! ## A hash-only computation in the game -/

theorem liftM_query_bind {α : Type} (t : List UInt8)
    (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    (liftM (liftM (SchemeHashSpec.query t) >>= k) : OracleComp World α) =
      liftM (World.query (.inr t)) >>= fun u ↦ liftM (k u) := by
  rw [liftM_bind]; rfl

/-! ## The adversary's phase -/

section Phase

variable {Seed PK SK₁ SK₂ Req Resp F : Type}

/-- A query of the adversary's own, in the phase. -/
theorem phase_inl {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) {β γ : Type}
    (t : World.Domain) (k : World.Range t → OracleComp (World + (Req →ₒ Resp)) β)
    (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) :
    (simulateQ (gameOracles S sk)
      (liftM ((World + (Req →ₒ Resp)).query (.inl t)) >>= k)).run >>= post =
      liftM (World.query t) >>= fun u ↦
        (simulateQ (gameOracles S sk) (k u)).run >>= fun p ↦ post (p.1, ∅ ++ p.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind', bind_assoc, gameOracles_inl,
    bind_map_left]
  rfl

/-- A signing query, in the phase. -/
theorem phase_inr {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) {β γ : Type}
    (r : Req) (k : Resp → OracleComp (World + (Req →ₒ Resp)) β)
    (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) :
    (simulateQ (gameOracles S sk)
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) >>= k)).run >>= post =
      liftM (S.sign sk r) >>= fun u ↦
        (simulateQ (gameOracles S sk) (k u)).run >>= fun p ↦ post (p.1, [⟨r, u⟩] ++ p.2) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, WriterT.run_bind', bind_assoc, gameOracles_inr,
    bind_map_left]
  rfl

/-- The game with its pairs taken apart. -/
theorem romGame_eq {SK : Type} (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    romGame S main = liftM S.sample >>= fun seed ↦ liftM (S.keygen seed) >>= fun keys ↦
      (simulateQ (gameOracles S keys.2) (main keys.1)).run >>= fun p ↦
        liftM (S.verify keys.1 p.1) >>= fun verified ↦ pure (S.win p.2 p.1 && verified) := rfl

end Phase

/-! ## Queries in a part of the domain -/

/-- Every query of `X`, on every path, lies in `P`. -/
def QueriesIn (P : List UInt8 → Prop) {α : Type} : OracleComp SchemeHashSpec α → Prop
  | .pure _ => True
  | .liftBind t k => P t ∧ ∀ u, QueriesIn P (k u)

section QueriesIn

variable {P : List UInt8 → Prop} {α β : Type}

theorem queriesIn_pure (a : α) : QueriesIn P (pure a : OracleComp SchemeHashSpec α) := trivial

theorem queriesIn_query_bind (t : List UInt8) (k : BitVec 256 → OracleComp SchemeHashSpec α) :
    QueriesIn P (liftM (SchemeHashSpec.query t) >>= k) ↔ P t ∧ ∀ u, QueriesIn P (k u) := Iff.rfl

theorem queriesIn_bind {X : OracleComp SchemeHashSpec α} {f : α → OracleComp SchemeHashSpec β}
    (hX : QueriesIn P X) (hf : ∀ a, QueriesIn P (f a)) : QueriesIn P (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc, queriesIn_query_bind]
    exact ⟨hX.1, fun u ↦ ih u (hX.2 u)⟩

theorem queriesIn_map {X : OracleComp SchemeHashSpec α} (f : α → β) (hX : QueriesIn P X) :
    QueriesIn P (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact queriesIn_bind hX fun _ ↦ trivial

theorem queriesIn_query {t : List UInt8} (ht : P t) :
    QueriesIn P (liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec (BitVec 256)) := by
  have := (queriesIn_query_bind (P := P) t pure).mpr ⟨ht, fun _ ↦ trivial⟩
  simpa using this

end QueriesIn

/-! ## The honest part of the random oracle sampled in advance -/

section Eager

variable (P : List UInt8 → Prop) [DecidablePred P] [Fintype {d // P d}]

/-- **The random oracle with its `P`-part a table `g`**: a `P`-point is answered from the cache
if cached, else by `g`, and never cached; every other query is the lazy random oracle. -/
noncomputable def eagerW (g : {d // P d} → BitVec 256) :
    QueryImpl World (StateT SchemeHashSpec.QueryCache ProbComp)
  | .inl n => unifFwdImpl _ n
  | .inr d =>
      if h : P d then StateT.mk fun c ↦ pure ((c d).getD (g ⟨d, h⟩), c)
      else SchemeHashSpec.randomOracle d

omit [DecidablePred P] [Fintype {d // P d}] in
theorem randomOracle_run_comm' (t d : List UInt8) (ht : t ≠ d) (c : SchemeHashSpec.QueryCache)
    (u : BitVec 256) :
    Prod.map id (fun c' ↦ c'.cacheQuery d u) <$> (SchemeHashSpec.randomOracle t).run c =
      (SchemeHashSpec.randomOracle t).run (c.cacheQuery d u) := by
  rw [randomOracle.run_eq, randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ ht]
  rcases h : c t with _ | v
  · simp only [map_bind, map_pure, Prod.map_apply, id_eq]
    refine bind_congr fun w ↦ ?_
    rw [QueryCache.cacheQuery_comm _ (Ne.symm ht)]
  · simp

omit [DecidablePred P] [Fintype {d // P d}] in
theorem mem_support_randomOracle_run' {t : List UInt8} {c : SchemeHashSpec.QueryCache} {z}
    (hz : z ∈ support ((SchemeHashSpec.randomOracle t).run c)) :
    z.2 = c ∨ ∃ v, z.2 = c.cacheQuery t v := by
  rw [randomOracle.run_eq] at hz
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inr ⟨w, rfl⟩
  · simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

theorem unifFwd_run' (n : ℕ) (c : SchemeHashSpec.QueryCache) :
    (unifFwdImpl SchemeHashSpec n).run c =
      (·, c) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simpa using unifFwdImpl.simulateQ_run (hashSpec := SchemeHashSpec)
    (unifSpec.query n : ProbComp (Fin (n + 1))) c

omit [Fintype {d // P d}] in
/-- Moving a cached `P`-answer into the table. -/
theorem run'_eagerW_cacheQuery (g : {d // P d} → BitVec 256) (d : List UInt8) (hd : P d)
    (u : BitVec 256) {α : Type} (Y : OracleComp World α) (c : SchemeHashSpec.QueryCache)
    (hc : c d = none) :
    (simulateQ (eagerW P g) Y).run' (c.cacheQuery d u) =ᵈ
      (simulateQ (eagerW P (Function.update g ⟨d, hd⟩ u)) Y).run' c := by
  refine (run'_simulateQ_evalDistEq_of_inv (eagerW P (Function.update g ⟨d, hd⟩ u))
    (eagerW P g) (fun c ↦ c d = none) (fun c ↦ c.cacheQuery d u) ?_ ?_ Y c hc).symm
  · intro t s hsd z hz
    rcases t with n | d'
    · change z ∈ support ((unifFwdImpl _ n).run s) at hz
      rw [unifFwd_run', support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hsd
    · simp only [eagerW] at hz
      split at hz
      · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsd
      · next hd' =>
        rcases mem_support_randomOracle_run' hz with h | ⟨v, h⟩
        · rw [h]; exact hsd
        · rw [h, QueryCache.cacheQuery_of_ne _ _ (by rintro rfl; exact hd' hd)]; exact hsd
  · intro t s hsd
    rcases t with n | d'
    · change _ <$> (unifFwdImpl _ n).run s =ᵈ (unifFwdImpl _ n).run _
      rw [unifFwd_run', unifFwd_run', Functor.map_map]
      exact EvalDistEq.rfl
    · simp only [eagerW]
      split
      · next hd' =>
        simp only [StateT.run_mk, map_pure, Prod.map_apply, id_eq]
        by_cases hdd : d' = d
        · subst hdd
          simp [hsd]
        · rw [QueryCache.cacheQuery_of_ne _ _ hdd]
          have : (⟨d', hd'⟩ : {d // P d}) ≠ ⟨d, hd⟩ := fun h ↦ hdd (congrArg Subtype.val h)
          simp [Function.update_of_ne this]
      · next hd' =>
        exact (randomOracle_run_comm' d' d (by rintro rfl; exact hd' hd) s u) ▸ EvalDistEq.rfl

/-- **Eager sampling of the `P`-part of the random oracle.** -/
theorem run'_romImpl_evalDistEq_eagerW {α : Type} (X : OracleComp World α)
    (c : SchemeHashSpec.QueryCache) :
    (simulateQ SchemeHashSpec.romImpl X).run' c =ᵈ
      (($ᵗ ({d // P d} → BitVec 256) : ProbComp _) >>= fun g ↦
        (simulateQ (eagerW P g) X).run' c) := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    simp only [← StateT.run'_eq]
    rcases t with n | d
    · exact common_step_evalDistEq P ((unifFwdImpl _ n).run c) _ _ fun a ↦ ih a.1 a.2
    · by_cases hd : P d
      · have h1 : ∀ g, (eagerW P g (.inr d)).run c = pure ((c d).getD (g ⟨d, hd⟩), c) :=
          fun g ↦ by simp [eagerW, hd]
        simp only [h1, pure_bind]
        change (((SchemeHashSpec.randomOracle d).run c) >>= _) =ᵈ _
        rw [randomOracle.run_eq]
        rcases hc : c d with _ | v
        · simp only [bind_assoc, pure_bind, Option.getD_none]
          let ψ : ({d // P d} → BitVec 256) → ProbComp α := fun g ↦
            (simulateQ (eagerW P g) (k (g ⟨d, hd⟩))).run' c
          refine (EvalDistEq.bind_right _ fun u ↦ (ih u _).trans (EvalDistEq.bind_right _
            fun g ↦ run'_eagerW_cacheQuery P g d hd u (k u) c hc)).trans ?_
          have h2 : ∀ (u : BitVec 256) (g : {d // P d} → BitVec 256),
              (simulateQ (eagerW P (Function.update g ⟨d, hd⟩ u)) (k u)).run' c =
                ψ (Function.update g ⟨d, hd⟩ u) := fun u g ↦ by simp [ψ]
          simp only [h2]
          exact uniform_update_evalDistEq P ⟨d, hd⟩ ψ
        · simp only [pure_bind, Option.getD_some]
          exact ih v c
      · have h1 : ∀ g, eagerW P g (.inr d) = SchemeHashSpec.randomOracle d :=
          fun g ↦ by simp [eagerW, hd]
        simp only [h1]
        exact common_step_evalDistEq P ((SchemeHashSpec.randomOracle d).run c) _ _
          fun a ↦ ih a.1 a.2

/-- A cache without `P`-points: those of every run under the table from the empty cache. -/
def PFree (c : SchemeHashSpec.QueryCache) : Prop := ∀ d, P d → c d = none

/-- The table as an answer function. -/
def tableAnswers (g : {d // P d} → BitVec 256) : QueryImpl SchemeHashSpec Id :=
  fun d ↦ if h : P d then g ⟨d, h⟩ else 0

omit [DecidablePred P] [Fintype {d // P d}] in
theorem pFree_empty : PFree P ∅ := fun _ _ ↦ rfl

omit [Fintype {d // P d}] in
theorem pFree_step (g : {d // P d} → BitVec 256) (t : World.Domain) (c : SchemeHashSpec.QueryCache)
    (hc : PFree P c) : ∀ z ∈ support ((eagerW P g t).run c), PFree P z.2 := by
  intro z hz
  rcases t with n | d
  · change z ∈ support ((unifFwdImpl _ n).run c) at hz
    rw [unifFwd_run', support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact hc
  · simp only [eagerW] at hz
    split at hz
    · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
      subst hz; exact hc
    · next hd =>
      rcases mem_support_randomOracle_run' hz with h | ⟨v, h⟩
      · rw [h]; exact hc
      · intro d' hd'
        rw [h, QueryCache.cacheQuery_of_ne _ _ (by rintro rfl; exact hd hd')]
        exact hc d' hd'

omit [Fintype {d // P d}] in
/-- Runs under the table keep caches without `P`-points. -/
theorem pFree_run (g : {d // P d} → BitVec 256) {α : Type} (X : OracleComp World α) :
    ∀ c, PFree P c → ∀ z ∈ support ((simulateQ (eagerW P g) X).run c), PFree P z.2 := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c hc z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact hc
  | query_bind t k ih =>
    intro c hc z hz
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    exact ih w.1 w.2 (pFree_step P g t c hc w hw) z hz

omit [Fintype {d // P d}] in
/-- **An honest computation under the table** is its value on the table, from a cache without
`P`-points, which it leaves unchanged. -/
theorem eagerW_liftM (g : {d // P d} → BitVec 256) {α : Type} (X : OracleComp SchemeHashSpec α)
    (hX : QueriesIn P X) :
    ∀ c, PFree P c → (simulateQ (eagerW P g) (liftM X : OracleComp World α)).run c =
      pure (evalWithAnswerFn (tableAnswers P g) X, c) := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro c _
    simp
  | query_bind t k ih =>
    intro c hc
    rw [queriesIn_query_bind] at hX
    rw [liftM_query_bind]
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    have hstep : (eagerW P g (.inr t)).run c = pure (g ⟨t, hX.1⟩, c) := by
      simp [eagerW, hX.1, hc t hX.1]
    rw [hstep, pure_bind, ih _ (hX.2 _) c hc, evalWithAnswerFn_bind,
      show evalWithAnswerFn (tableAnswers P g) (liftM (SchemeHashSpec.query t)) =
        tableAnswers P g t from simulateQ_spec_query _ t]
    simp [tableAnswers, hX.1]

end Eager

/-! ## The adversary's phase under the table -/

section PhaseEager

variable (P : List UInt8 → Prop) [DecidablePred P] [Fintype {d // P d}]
  {Seed PK SK₁ SK₂ Req Resp F : Type}

omit [Fintype {d // P d}] in
theorem run'_bind_congr (g : {d // P d} → BitVec 256) {α β : Type} (x : OracleComp World α)
    (f₁ f₂ : α → OracleComp World β) (c : SchemeHashSpec.QueryCache)
    (h : ∀ z ∈ support ((simulateQ (eagerW P g) x).run c),
      (simulateQ (eagerW P g) (f₂ z.1)).run' z.2 =ᵈ (simulateQ (eagerW P g) (f₁ z.1)).run' z.2) :
    (simulateQ (eagerW P g) (x >>= f₂)).run' c =ᵈ (simulateQ (eagerW P g) (x >>= f₁)).run' c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact evalDistEq_bind_of_support EvalDistEq.rfl fun z hz ↦ by
    simpa only [StateT.run'_eq] using h z hz

omit [Fintype {d // P d}] in
theorem run'_liftM_bind (g : {d // P d} → BitVec 256) {α β : Type}
    (X : OracleComp SchemeHashSpec α) (hX : QueriesIn P X) (f : α → OracleComp World β)
    (c : SchemeHashSpec.QueryCache) (hc : PFree P c) :
    (simulateQ (eagerW P g) ((liftM X : OracleComp World α) >>= f)).run' c =
      (simulateQ (eagerW P g) (f (evalWithAnswerFn (tableAnswers P g) X))).run' c := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, eagerW_liftM P g X hX c hc,
    pure_bind]

omit [Fintype {d // P d}] in
/-- **The phase under the table**: when the two signers are honest computations with the same
values on the table, the phase against either, followed by a common continuation, is the same in
distribution from a cache without `P`-points. -/
theorem phase_eager (g : {d // P d} → BitVec 256) (S₁ : SchemeWithHash Seed PK SK₁ Req Resp F)
    (S₂ : SchemeWithHash Seed PK SK₂ Req Resp F) (sk₁ : SK₁) (sk₂ : SK₂)
    (h₁ : ∀ r, QueriesIn P (S₁.sign sk₁ r)) (h₂ : ∀ r, QueriesIn P (S₂.sign sk₂ r))
    (heq : ∀ r, evalWithAnswerFn (tableAnswers P g) (S₂.sign sk₂ r) =
      evalWithAnswerFn (tableAnswers P g) (S₁.sign sk₁ r))
    {β γ : Type} (M : OracleComp (World + (Req →ₒ Resp)) β) :
    ∀ (post : β × QueryLog (Req →ₒ Resp) → OracleComp World γ) (c : SchemeHashSpec.QueryCache),
      PFree P c →
      (simulateQ (eagerW P g) ((simulateQ (gameOracles S₂ sk₂) M).run >>= post)).run' c =ᵈ
        (simulateQ (eagerW P g) ((simulateQ (gameOracles S₁ sk₁) M).run >>= post)).run' c := by
  induction M using OracleComp.inductionOn with
  | pure a =>
    intro post c _
    exact EvalDistEq.rfl
  | query_bind t k ih =>
    intro post c hc
    rcases t with t | r
    · rw [phase_inl, phase_inl]
      exact run'_bind_congr P g _ _ _ c fun z hz ↦
        ih z.1 _ z.2 (pFree_run P g _ c hc z hz)
    · rw [phase_inr, phase_inr]
      rw [run'_liftM_bind P g _ (h₂ r) _ c hc, run'_liftM_bind P g _ (h₁ r) _ c hc, heq r]
      exact ih _ _ c hc

end PhaseEager

/-! ## The swap -/

/-- **A signer swapped for one with the same values.** `S₂`'s secret key is a function `keep` of
the seed; on every answer function `f`, `S₂`'s key generation gives `S₁`'s public key, and `S₂`'s
signer with the kept key gives the signatures of `S₁`'s signer with `S₁`'s key on `f`. The honest
algorithms query a finite part `P` of the hash's domain. -/
structure StaticSwap {Seed PK SK₁ SK₂ Req Resp F : Type}
    (S₁ : SchemeWithHash Seed PK SK₁ Req Resp F) (S₂ : SchemeWithHash Seed PK SK₂ Req Resp F) where
  keep : Seed → SK₂
  sample_eq : S₂.sample = S₁.sample
  verify_eq : S₂.verify = S₁.verify
  win_eq : S₂.win = S₁.win
  keygen_eval : ∀ f seed, evalWithAnswerFn f (S₂.keygen seed) =
    ((evalWithAnswerFn f (S₁.keygen seed)).1, keep seed)
  sign_eval : ∀ f seed r, evalWithAnswerFn f (S₂.sign (keep seed) r) =
    evalWithAnswerFn f (S₁.sign (evalWithAnswerFn f (S₁.keygen seed)).2 r)

namespace StaticSwap

variable {Seed PK SK₁ SK₂ Req Resp F : Type} {S₁ : SchemeWithHash Seed PK SK₁ Req Resp F}
  {S₂ : SchemeWithHash Seed PK SK₂ Req Resp F}

/-- **The same success**: in the random-oracle model, the game against `S₂` is won as often as
the game against `S₁`. -/
theorem success_eq (K : StaticSwap S₁ S₂) (P : List UInt8 → Prop) [DecidablePred P]
    [Fintype {d // P d}] (hk₁ : ∀ seed, QueriesIn P (S₁.keygen seed))
    (hk₂ : ∀ seed, QueriesIn P (S₂.keygen seed)) (hs₁ : ∀ sk r, QueriesIn P (S₁.sign sk r))
    (hs₂ : ∀ seed r, QueriesIn P (S₂.sign (K.keep seed) r))
    (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    Pr{let r ← romExperiment S₂ main}[r.1 = true] =
      Pr{let r ← romExperiment S₁ main}[r.1 = true] := by
  rw [prob_romExperiment, prob_romExperiment,
    (run'_romImpl_evalDistEq_eagerW P (romGame S₂ main) ∅).prEvent_eq,
    (run'_romImpl_evalDistEq_eagerW P (romGame S₁ main) ∅).prEvent_eq]
  refine (EvalDistEq.bind_right _ fun g ↦ ?_).prEvent_eq _
  rw [romGame_eq, romGame_eq, K.sample_eq]
  refine run'_bind_congr P g _ _ _ ∅ fun z hz ↦ ?_
  have hc := pFree_run P g _ ∅ (pFree_empty P) z hz
  rw [run'_liftM_bind P g _ (hk₂ z.1) _ z.2 hc, run'_liftM_bind P g _ (hk₁ z.1) _ z.2 hc,
    K.keygen_eval]
  simp only [K.verify_eq, K.win_eq]
  exact phase_eager P g S₁ S₂ _ _ (fun r ↦ hs₁ _ r) (hs₂ z.1) (fun r ↦ K.sign_eval _ z.1 r) _ _ z.2
    hc

end StaticSwap

end Common.SufCma
