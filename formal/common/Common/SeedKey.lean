module

public import Common.Signature
public import Common.Rerun

@[expose] public section

/-!
# A secret key that is the key's seed, or the seed and part of what it derives

The crates' secret key is the key's seed `S_0` (leanSPHINCS), or the seed and the public parameter
(leanXMSS): the signer derives the rest of what it signs with from it at each signature (the scheme
seed `S = H(tag ‖ S_0)`, and for leanSPHINCS the public parameter of `S`), as key generation
derived it. In the random-oracle game these derivations are cache hits: key generation made the
same queries before, so they return the same values. A scheme `S` whose secret key is what the
derivation gives, and the scheme `K.scheme` whose secret key is the kept part and whose signer
derives the rest first (`KeptKey`), have the same game in distribution, so the same success
(`KeptKey.prob_romExperiment_eq`); `KeptKey.romBoundAdv` (`Common.AdvBudget`) passes a bound at the
adversary's own count from one to the other.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common.SufCma

variable {Seed PK SK Req Resp F D : Type}

/-! ## Runs in the random-oracle model -/

/-- A run of a game in the random-oracle model from the cache `c`. -/
noncomputable abbrev romRun {α : Type} (x : OracleComp World α) (c : SchemeHashSpec.QueryCache) :
    ProbComp (α × SchemeHashSpec.QueryCache) :=
  (simulateQ SchemeHashSpec.romImpl x).run c

/-- Equal in distribution after a draw equal in distribution, the continuations equal in
distribution on its support. -/
theorem evalDistEq_bind_of_support {α β : Type} {mx my : ProbComp α} (h : mx =ᵈ my)
    {f g : α → ProbComp β} (hfg : ∀ a ∈ support my, f a =ᵈ g a) : mx >>= f =ᵈ my >>= g := by
  refine (h.bind_left f).trans ?_
  let : MeasurableSpace β := ⊤
  exact EvalDistEq.of_evalDist_eq
    (evalDist_bind_congr_of_support my f g fun a ha ↦ (hfg a ha).evalDist_eq)

theorem romRun_bind {α β : Type} (x : OracleComp World α) (f : α → OracleComp World β)
    (c : SchemeHashSpec.QueryCache) :
    romRun (x >>= f) c = romRun x c >>= fun z ↦ romRun (f z.1) z.2 := by
  simp only [romRun, simulateQ_bind, StateT.run_bind]

theorem romRun_bind_evalDistEq {α β : Type} {x y : OracleComp World α} {f g : α → OracleComp World β}
    {c : SchemeHashSpec.QueryCache} (hxy : romRun x c =ᵈ romRun y c)
    (hfg : ∀ z ∈ support (romRun y c), romRun (f z.1) z.2 =ᵈ romRun (g z.1) z.2) :
    romRun (x >>= f) c =ᵈ romRun (y >>= g) c := by
  rw [romRun_bind, romRun_bind]
  exact evalDistEq_bind_of_support hxy hfg

/-- A hash-only computation lifted into the world flips no coins. -/
theorem noCoins_liftM {α : Type} (X : OracleComp SchemeHashSpec α) :
    NoCoins (liftM X : OracleComp World α) := by
  induction X using OracleComp.inductionOn with
  | pure a => exact noCoins_pure (hs := SchemeHashSpec) a
  | query_bind t k ih =>
    rw [liftM_bind]
    exact (noCoins_hq_bind (hs := SchemeHashSpec) t _).mpr ih

/-- A hash-only computation lifted into the world has its outputs. -/
theorem mem_support_liftM_world {α : Type} (X : OracleComp SchemeHashSpec α) (a : α) :
    a ∈ support (liftM X : OracleComp World α) ↔ a ∈ support X := by
  induction X using OracleComp.inductionOn with
  | pure b => simp
  | query_bind t k ih =>
    rw [liftM_bind, mem_support_bind_iff, mem_support_bind_iff]
    constructor
    · rintro ⟨u, -, hu⟩
      exact ⟨u, by simp, (ih u).mp hu⟩
    · rintro ⟨u, -, hu⟩
      exact ⟨u, mem_support_query (spec := World) (.inr t) u, (ih u).mpr hu⟩

/-! ## The game's oracles -/

/-- The game's oracles: the world forwarded, the signing oracle logging. -/
abbrev gameOracles {SK' : Type} (X : SchemeWithHash Seed PK SK' Req Resp F) (sk : SK') :=
  QueryImpl.ofLift World (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp World)) + signingOracle X sk

theorem gameOracles_inl {SK' : Type} (X : SchemeWithHash Seed PK SK' Req Resp F) (sk : SK')
    (t : World.Domain) :
    (gameOracles X sk (.inl t)).run =
      (·, ∅) <$> (liftM (World.query t) : OracleComp World _) := rfl

theorem gameOracles_inr {SK' : Type} (X : SchemeWithHash Seed PK SK' Req Resp F) (sk : SK')
    (r : Req) :
    (gameOracles X sk (.inr r)).run =
      (fun u ↦ (u, [⟨r, u⟩])) <$> (liftM (X.sign sk r) : OracleComp World Resp) := by
  simp [gameOracles, signingOracle]

namespace KeptKey

variable {SK' : Type} {S : SchemeWithHash Seed PK SK Req Resp F} (K : KeptKey S D SK')

/-- The signer's derivation reruns key generation's: in the random-oracle model, from a cache that
holds what `derive seed` queried, `rederive` of the kept key returns the derived value, querying
nothing new. -/
def Reruns : Prop :=
  ∀ (seed : Seed) (c : SchemeHashSpec.QueryCache),
    ∀ z ∈ support (romRun (liftM (K.derive seed) : OracleComp World D) c), ∀ c', z.2 ≤ c' →
      romRun (liftM (K.rederive (K.keep seed z.1)) : OracleComp World D) c' = pure (z.1, c')

/-! ## Success: the same in distribution -/

theorem _root_.Common.SufCma.romRun_map {α β : Type} (f : α → β) (x : OracleComp World α)
    (c : SchemeHashSpec.QueryCache) :
    romRun (f <$> x) c = (fun p ↦ (f p.1, p.2)) <$> romRun x c := by
  simp only [romRun, simulateQ_map, StateT.run_map]

/-- **The adversary's phase, in the random-oracle model**: from a cache on which the kept key's
derivation returns `d` querying nothing new, the phase against `K.scheme` with the kept key is the
phase against `S` with a key of derivation `d`, in distribution. -/
theorem phase_evalDistEq (key : SK') (d : D) (c₁ : SchemeHashSpec.QueryCache)
    (hd : ∀ c, c₁ ≤ c → romRun (liftM (K.rederive key) : OracleComp World D) c = pure (d, c))
    (sk : SK) (hsk : S.sign sk = K.signWith d) {β : Type}
    (M : OracleComp (World + (Req →ₒ Resp)) β) :
    ∀ c, c₁ ≤ c → romRun (simulateQ (gameOracles K.scheme key) M).run c =ᵈ
      romRun (simulateQ (gameOracles S sk) M).run c := by
  induction M using OracleComp.inductionOn with
  | pure a => intro c _; exact EvalDistEq.rfl
  | query_bind t k ih =>
    intro c hc
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, WriterT.run_bind']
    rcases t with t | r
    · rw [gameOracles_inl, gameOracles_inl]
      refine romRun_bind_evalDistEq EvalDistEq.rfl fun z hz ↦ ?_
      rw [romRun_map, romRun_map]
      exact (ih z.1.1 z.2 (le_trans hc (le_of_mem_support_run _ _ hz))).map _
    · rw [gameOracles_inr, gameOracles_inr, hsk]
      have hfirst : ∀ {γ : Type} (g : Resp → γ),
          romRun (g <$> (liftM (K.scheme.sign key r) : OracleComp World Resp)) c =
            romRun (g <$> (liftM (K.signWith d r) : OracleComp World Resp)) c := by
        intro γ g
        simp only [KeptKey.scheme, romRun_map, liftM_bind, romRun_bind, hd c hc, pure_bind]
      refine romRun_bind_evalDistEq (by rw [hfirst]) fun z hz ↦ ?_
      rw [romRun_map, romRun_map]
      exact (ih z.1.1 z.2 (le_trans hc (le_of_mem_support_run _ _ hz))).map _

theorem fst_mem_support_romRun' {α : Type} {x : OracleComp World α} {c : SchemeHashSpec.QueryCache}
    {z : α × SchemeHashSpec.QueryCache} (h : z ∈ support (romRun x c)) :
    z.1 ∈ support x :=
  support_simulateQ_run'_subset SchemeHashSpec.romImpl x c (by
    rw [StateT.run'_eq]; erw [support_map]; exact ⟨z, h, rfl⟩)

/-- **The game against `K.scheme` is the game against `S`, in distribution**, in the random-oracle
model from any cache, when the signer's derivation reruns key generation's. -/
theorem romGame_evalDistEq (hK : K.Reruns) (main : PK → OracleComp (World + (Req →ₒ Resp)) F)
    (c : SchemeHashSpec.QueryCache) :
    romRun (romGame K.scheme main) c =ᵈ romRun (romGame S main) c := by
  unfold romGame
  refine romRun_bind_evalDistEq EvalDistEq.rfl fun zs _ ↦ ?_
  simp only [KeptKey.scheme, K.keygen_eq, liftM_map, bind_map_left, liftM_bind, bind_assoc]
  refine romRun_bind_evalDistEq EvalDistEq.rfl fun zd hzd ↦ ?_
  refine romRun_bind_evalDistEq EvalDistEq.rfl fun zk hzk ↦ ?_
  have hkeys : zk.1 ∈ support (K.rest zs.1 zd.1) :=
    (mem_support_liftM_world _ _).mp (fst_mem_support_romRun' hzk)
  have hsk := K.sign_eq zs.1 zd.1 zk.1 hkeys
  have hrerun : ∀ c', zd.2 ≤ c' →
      romRun (liftM (K.rederive (K.keep zs.1 zd.1)) : OracleComp World D) c' = pure (zd.1, c') :=
    hK zs.1 zs.2 zd hzd
  rcases zk with ⟨⟨pk, sk⟩, ck⟩
  refine romRun_bind_evalDistEq
    (K.phase_evalDistEq _ zd.1 zd.2 hrerun sk hsk (main pk) ck
      (le_of_mem_support_run _ _ hzk)) fun _ _ ↦ EvalDistEq.rfl

/-- The success of the game against `K.scheme` is that against `S`. -/
theorem prob_romExperiment_eq (hK : K.Reruns) (main : PK → OracleComp (World + (Req →ₒ Resp)) F) :
    Pr{let r ← romExperiment K.scheme main}[r.1 = true] =
      Pr{let r ← romExperiment S main}[r.1 = true] := by
  rw [prob_romExperiment, prob_romExperiment, StateT.run'_eq, StateT.run'_eq, prEvent_map,
    prEvent_map]
  exact (K.romGame_evalDistEq hK main ∅).prEvent_eq _

end KeptKey

end Common.SufCma
