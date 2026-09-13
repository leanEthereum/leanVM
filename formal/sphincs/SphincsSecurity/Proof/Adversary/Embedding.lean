import SphincsSecurity.Proof.Seeded.QueryBoundExtras

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security
set_option backward.isDefEq.respectTransparency false

def embedQueries : QueryImpl (HashSpec + SigningSpec) (OracleComp (OracleWorld + SigningSpec)) :=
  fun | .inl input => liftM ((OracleWorld + SigningSpec).query (.inl (.inr input)))
      | .inr input => liftM ((OracleWorld + SigningSpec).query (.inr input))

def embed (adversary : Adversary) : SphincsSecurity.Adversary :=
  ⟨fun pk => simulateQ embedQueries (adversary.main pk)⟩

theorem logged_embed {α : Type} (sk : Seeded.SecretKey)
    (computation : OracleComp (HashSpec + SigningSpec) α) :
    (simulateQ (forwardOracles + SphincsSecurity.signingOracle Seeded.scheme sk)
      (simulateQ embedQueries computation)).run =
    (liftM (simulateQ (QueryImpl.ofLift HashSpec (WriterT (QueryLog SigningSpec) (OracleComp HashSpec)) + signingOracle sk)
      computation).run : OracleComp OracleWorld _) := by
  rw [← QueryImpl.simulateQ_compose]
  change _ = simulateQ (QueryImpl.ofLift HashSpec (OracleComp OracleWorld))
    (simulateQ (QueryImpl.ofLift HashSpec (WriterT (QueryLog SigningSpec) (OracleComp HashSpec)) + signingOracle sk) computation).run
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  congr 2
  funext input
  cases input <;> apply WriterT.ext <;>
    simp [QueryImpl.writerTMapBase, QueryImpl.compose, embedQueries, forwardOracles,
      SphincsSecurity.signingOracle, signingOracle, Seeded.scheme, WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell,
      map_eq_bind_pure_comp, bind_assoc]
  all_goals rfl

theorem game_embed (adversary : Adversary) :
    SphincsSecurity.gameCore Seeded.scheme (embed adversary) = (do
      let seed ← liftM sampleMasterSeed
      liftM (gameCore seed adversary)) := by
  unfold SphincsSecurity.gameCore Seeded.gameRest
  change (Seeded.keygen >>= _) = _
  unfold Seeded.keygen
  simp only [bind_assoc, gameCore, liftM_bind, liftM_pure]
  apply bind_congr
  intro seed
  apply bind_congr
  rintro ⟨pk, sk⟩
  simp only [embed, logged_embed]
  rfl

noncomputable def countAll {α : Type} (computation : OracleComp HashSpec α) :=
  QueryCap.counted (fun _ => True) computation

theorem count_lift {α : Type} (computation : OracleComp HashSpec α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) = liftM (countAll computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM (OracleWorld.query (.inr input)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, countAll, QueryCap.counted_query_bind,
        liftM_bind, liftM_pure, ↓reduceIte]
      rfl

theorem simulate_countAll {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (countAll computation) = (simulateQ countedOracle computation).run := by
  simpa only [countAll, countedOracle, ite_true] using
    QueryCap.simulate_withCost (fun _ => True)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) computation

theorem run_counted_seed {α β : Type} (sample : ProbComp α)
    (computation : α → OracleComp HashSpec β) (cache : QueryCache HashSpec) :
    (simulateQ countedRomImpl (do
      let seed ← liftM sample
      liftM (computation seed) : OracleComp OracleWorld β)).run.run' cache = (do
      let seed ← sample
      (simulateQ countedOracle (computation seed)).run.run' cache) := by
  rw [← simulateQ_countHashQueries]
  simp only [countHashQueries_bind, countHashQueries_lift_prob, count_lift,
    bind_map_left, Nat.zero_add, simulateQ_bind]
  simp only [romImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_add_liftM_right,
    simulateQ_pure, StateT.run'_eq, StateT.run_bind, unifFwdImpl.simulateQ_run,
    bind_map_left, simulate_countAll, map_bind]
  rfl

theorem experiment_embed (adversary : Adversary) :
    (simulateQ countedRomImpl (SphincsSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅ =
      experiment adversary := by
  rw [game_embed, run_counted_seed]
  rfl

theorem advantage_embed (adversary : Adversary) :
    SphincsSecurity.forgeAdvantage Seeded.scheme (embed adversary) = forgeAdvantage adversary := by
  unfold forgeAdvantage SphincsSecurity.forgeAdvantage
  rw [← experiment_embed, ← simulateQ_countHashQueries]
  have h := congrArg (fun computation : OracleComp OracleWorld Bool =>
    (simulateQ romImpl computation).run' ∅)
    (countHashQueries_forget (SphincsSecurity.gameCore Seeded.scheme (embed adversary)))
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h]
  simpa only [probEvent_eq_eq_probOutput, Function.comp_def] using probEvent_map (mx := (simulateQ romImpl
    (countHashQueries (SphincsSecurity.gameCore Seeded.scheme (embed adversary)))).run' ∅)
    (f := Prod.fst) (q := fun result => result = true)

end SphincsSecurity.Security
