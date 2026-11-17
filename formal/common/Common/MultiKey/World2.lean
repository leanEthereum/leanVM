module

public import Common.MultiKey.Reduction

@[expose] public section

/-!
# The tagged game with two oracles is the single-key game against the reduction

`prob_taggedGame_eq`: the tagged game's win, its tagged queries answered by two independent random
oracles, has the probability of the single-key ROM game against `reduction` (whose private oracle
the reduction samples itself with coins). The private oracle sampled inside is the second oracle
(`Common.SufCma.MultiKey.flatten`); the rest is the same computation: the state layer of the
private oracle commutes with the writer layer of the signing oracle
(`Common.SufCma.simulateQ_state_writer_comm`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

section Lifts

variable {ι ι' σ α : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- A stateful simulation whose every step leaves the state alone runs as the plain one. -/
theorem run_simulateQ_stateless (impl : QueryImpl spec (StateT σ (OracleComp spec')))
    (g : QueryImpl spec (OracleComp spec')) (h : ∀ t, impl t = StateT.lift (g t))
    (X : OracleComp spec α) (c : σ) :
    (simulateQ impl X).run c = (·, c) <$> simulateQ g X := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, h, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, ih, map_bind]

end Lifts

/-- Logging the queries changes nothing else. -/
theorem fst_map_run_logImpl {α : Type} (X : OracleComp SchemeHashSpec α) :
    Prod.fst <$> (simulateQ logImpl X).run = X := by
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    have h0 : Prod.fst <$> (logImpl t).run =
        (liftM (SchemeHashSpec.query t) : OracleComp SchemeHashSpec _) := by
      simp [logImpl, run_liftM_query_writer]
    calc Prod.fst <$> (simulateQ logImpl (liftM (SchemeHashSpec.query t) >>= k)).run
        = (logImpl t).run >>= fun p ↦ Prod.fst <$> (simulateQ logImpl (k p.1)).run := by
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
            OracleQuery.cont_query, id_map, WriterT.run_bind', map_bind, Functor.map_map]
          rfl
      _ = (logImpl t).run >>= fun p ↦ k p.1 := by simp only [ih]
      _ = liftM (SchemeHashSpec.query t) >>= k := by rw [← h0, bind_map_left]

theorem fst_map_loggedKeygen (S : SchemeWithHash Seed PK SK Req Resp F) (seed : Seed) :
    Prod.fst <$> loggedKeygen S seed = S.keygen seed :=
  fst_map_run_logImpl _

/-- Coins through the private oracle sampled inside: the coins, the cache untouched. -/
theorem run_inner_coinsT {α : Type} (p : ProbComp α) (c : SchemeHashSpec.QueryCache) :
    (simulateQ inner (simulateQ coinsT p)).run c = (·, c) <$> (liftM p : OracleComp World α) := by
  rw [← QueryImpl.simulateQ_compose,
    run_simulateQ_stateless _ (fun n ↦ liftM (World.query (.inl n))) (fun n ↦ by
      simp only [QueryImpl.apply_compose, coinsT, simulateQ_spec_query]; rfl)]
  rfl

/-- The real oracle through the private oracle sampled inside: the hash, the cache untouched. -/
theorem run_inner_tagF {α : Type} (X : OracleComp SchemeHashSpec α)
    (c : SchemeHashSpec.QueryCache) :
    (simulateQ inner (simulateQ tagF X)).run c = (·, c) <$> (liftM X : OracleComp World α) := by
  rw [← QueryImpl.simulateQ_compose,
    run_simulateQ_stateless _ (fun x ↦ liftM (World.query (.inr x))) (fun x ↦ by
      simp only [QueryImpl.apply_compose, tagF, simulateQ_spec_query]; rfl)]
  rfl

/-! ## The middle phase: the private oracle's state and the signing oracle's log commute -/

variable (S : SchemeWithHash Seed PK SK Req Resp F)

/-- **The private oracle sampled inside, then the signing oracle, is the signing oracle, then the
private oracle sampled inside.** -/
theorem gameOracles_innerR (sk : SK) {α : Type} (Y : OracleComp (TSpec + (Req →ₒ Resp)) α)
    (c : SchemeHashSpec.QueryCache) :
    (simulateQ (gameOracles S sk) ((simulateQ innerR Y).run c)).run =
      (fun z ↦ ((z.1.1, z.2), z.1.2)) <$>
        (simulateQ inner ((simulateQ (gameOraclesT S sk) Y).run)).run c := by
  have h := simulateQ_state_writer_comm innerR (gameOracles S sk)
    (QueryImpl.ofLift World (OracleComp World)) (gameOraclesT S sk) inner (fun t s ↦ ?_) Y c
  · rwa [simulateQ_ofLift_eq_self] at h
  rw [simulateQ_ofLift_eq_self]
  rcases t with t | r
  · have h1 : (innerR (Req := Req) (Resp := Resp) (.inl t)).run s =
        simulateQ toWR ((inner t).run s) := rfl
    have h2 : ∀ u, ((gameOracles S sk ∘ₛ toWR (Req := Req) (Resp := Resp)) u).run =
        (·, ∅) <$> (liftM (World.query u) : OracleComp World _) := by
      intro u
      simp only [QueryImpl.apply_compose, toWR, simulateQ_spec_query]
      rfl
    have h3 : ((gameOraclesT S sk) (.inl t)).run =
        (·, ∅) <$> (liftM (TSpec.query t) : OracleComp TSpec _) := rfl
    rw [h1, ← QueryImpl.simulateQ_compose, run_simulateQ_writer_of_run _ _ h2, h3, simulateQ_map,
      simulateQ_spec_query, StateT.run_map, Functor.map_map]
    have h4 : simulateQ (fun u ↦ (liftM (World.query u) : OracleComp World _)) ((inner t).run s) =
        (inner t).run s :=
      simulateQ_ofLift_eq_self ((inner t).run s)
    rw [h4]
    rfl
  · have h1 : (innerR (Req := Req) (Resp := Resp) (.inr r)).run s =
        (fun u ↦ (u, s)) <$>
          (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ Resp) := rfl
    have h2 : ((gameOraclesT S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
        simulateQ tagF (S.sign sk r) := by
      simp [gameOraclesT, signT]
    rw [h1, simulateQ_map, simulateQ_spec_query, WriterT.run_map', gameOracles_inr, h2,
      simulateQ_map, StateT.run_map, run_inner_tagF, Functor.map_map, Functor.map_map,
      Functor.map_map]
    rfl


variable (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)] {k : ℕ}

/-- **The tagged game, its private oracle sampled inside, is the single-key game against the
reduction.** -/
theorem inner_taggedGame (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    (fun z ↦ z.1.2) <$> (simulateQ inner (taggedGame S ownedPub i A)).run' ∅ =
      romGame S (reduction S ownedPub i A) := by
  rw [StateT.run'_eq, Functor.map_map, romGame_eq]
  simp only [taggedGame, simulateQ_bind, StateT.run_bind, run_inner_coinsT, run_inner_tagF,
    bind_map_left, map_bind]
  refine bind_congr fun s ↦ ?_
  rw [← fst_map_loggedKeygen S s, liftM_map, bind_map_left]
  refine bind_congr fun zi ↦ ?_
  simp only [reduction, simulateQ_map, WriterT.run_map', StateT.run'_eq, gameOracles_innerR,
    bind_map_left]
  refine bind_congr fun z ↦ ?_
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

theorem join_empty : join ∅ ∅ = (∅ : TagSpec.QueryCache) :=
  QueryCache.ext fun t ↦ by rw [join_apply]; split <;> rfl

/-- **The tagged game with two oracles wins as often as the single-key game against the
reduction.** -/
theorem prob_taggedGame_eq (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) :
    Pr{let z ← (simulateQ TagSpec.romImpl (taggedGame S ownedPub i A)).run ∅}[z.1.1.2 = true] =
      Pr{let r ← romExperiment S (reduction S ownedPub i A)}[r.1 = true] := by
  rw [prob_romExperiment, ← inner_taggedGame, ← join_empty, ← flatten]
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end Common.SufCma.MultiKey
