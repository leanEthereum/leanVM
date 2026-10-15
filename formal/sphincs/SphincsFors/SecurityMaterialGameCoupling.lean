import SphincsFors.SecurityPreparedScheme
import SphincsFors.Statement
import SphincsFors.RandomizedSupport
import SphincsFors.SecurityTreeWitness

/-!
Composing privileged honest-code compilation with an unchanged shared adversarial oracle: the
honest computations, and the whole game after the seed, are related to their compiled forms, with
the prepared material table kept in the shared cache throughout.
-/

open OracleComp OracleSpec

namespace SphincsFors.Security.MaterialGameCoupling
open SeedModel SeedCoupling PreparedScheme Completeness

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
attribute [local irreducible] programCache

/-- An already present material table is unchanged by programming it again. -/
theorem programCache_eq_self (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (hknown : programCache ∅ seed material ≤ base) : programCache base seed material = base := by
  funext input
  rw [programCache_lookup]
  cases hentry : programCache ∅ seed material input with
  | none => rfl
  | some answer => exact (hknown hentry).symm

theorem prepared_query_support_cache_le (input : PreparedWorld.Domain)
    (cache : QueryCache HashSpec) (answer : PreparedWorld.Range input) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((preparedRom input).run cache)) : cache ≤ cache' := by
  cases input with
  | inl input =>
      change (answer, cache') ∈ support
        ((fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _)) at hmem
      rw [support_map] at hmem
      obtain ⟨_, _, heq⟩ := hmem
      cases heq
      exact le_rfl
  | inr input =>
      cases input with
      | inl input => exact (query_support_cached input cache answer cache' hmem).1
      | inr input =>
          change (answer, cache') ∈ support (pure ((), cache) : ProbComp _) at hmem
          rw [mem_support_pure_iff] at hmem
          cases hmem
          exact le_rfl

theorem prepared_support_cache_le {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (result : α) (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ preparedRom computation).run cache)) : cache ≤ cache' := by
  induction computation using OracleComp.inductionOn generalizing cache result cache' with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hmem
      cases hmem
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, middle⟩, hquery, hrest⟩ := hmem
      exact (prepared_query_support_cache_le input cache answer middle hquery).trans
        (ih answer middle result cache' hrest)

/-- Source and target runtimes retain all counted calls and the complete final cache. -/
noncomputable def sourceRun {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : ProbComp ((α × Nat) × QueryCache HashSpec) :=
  (simulateQ romImpl (countHashQueries computation)).run cache

noncomputable def targetRun {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) : ProbComp ((α × Nat) × QueryCache HashSpec) :=
  (simulateQ preparedRom (countPreparedQueries computation)).run cache

theorem sourceRun_eq_counted {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : sourceRun computation cache =
      (simulateQ countedOracle computation).run.run cache := by
  rw [sourceRun, simulateQ_countHashQueries]

theorem targetRun_eq_counted {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) : targetRun computation cache =
      (simulateQ preparedCountedOracle computation).run.run cache := by
  rw [targetRun, simulateQ_countPreparedQueries]

def Related {α : Type} (known : QueryCache HashSpec) (left : OracleComp OracleWorld α)
    (right : OracleComp PreparedWorld α) : Prop :=
  ∀ cache, known ≤ cache → 𝒟[sourceRun left cache] = 𝒟[targetRun right cache]

/-- Honest compilation is valid on a shared cache already containing the material table.
This version keeps that table in the target cache, so ordinary adversarial calls remain valid. -/
theorem Related.honest {α : Type} (seed : MasterSeed) (material : Material)
    (computation : OracleComp OracleWorld α) :
    Related (programCache ∅ seed material) computation (simulateQ (compileWorld seed material) computation) := by
  intro cache hknown
  rw [sourceRun_eq_counted, targetRun_eq_counted]
  have hreplay := run_compileWorld_counted seed material computation cache
  rw [programCache_eq_self cache seed material hknown] at hreplay
  rw [hreplay]
  let target := (simulateQ preparedCountedOracle
    (simulateQ (compileWorld seed material) computation)).run.run cache
  change 𝒟[(fun result => (result.1, programCache result.2 seed material)) <$> target] = 𝒟[target]
  trans 𝒟[target >>= fun result => pure result]
  · rw [← bind_pure_comp]
    apply evalDist_bind_congr
    intro result hresult
    have hcache : cache ≤ result.2 := by
      dsimp only [target] at hresult
      rw [← simulateQ_countPreparedQueries] at hresult
      exact prepared_support_cache_le _ cache result.1 result.2 hresult
    rw [programCache_eq_self _ _ _ (hknown.trans hcache)]
  · rw [bind_pure]

theorem sourceRun_bind {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    sourceRun (first >>= next) cache = (do
      let a ← sourceRun first cache
      let b ← sourceRun (next a.1.1) a.2
      return ((b.1.1, a.1.2 + b.1.2), b.2)) := by
  simp only [sourceRun, countHashQueries, SphincsBase.QueryCap.counted_bind,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

theorem targetRun_bind {α β : Type} (first : OracleComp PreparedWorld α)
    (next : α → OracleComp PreparedWorld β) (cache : QueryCache HashSpec) :
    targetRun (first >>= next) cache = (do
      let a ← targetRun first cache
      let b ← targetRun (next a.1.1) a.2
      return ((b.1.1, a.1.2 + b.1.2), b.2)) := by
  simp only [targetRun, countPreparedQueries, SphincsBase.QueryCap.counted_bind,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]

theorem Related.pure' {α : Type} (known : QueryCache HashSpec) (value : α) :
    Related known (pure value) (pure value) := by
  intro cache hcache
  rfl

theorem Related.bind {α β : Type} {known : QueryCache HashSpec}
    {left : OracleComp OracleWorld α} {right : OracleComp PreparedWorld α}
    (h : Related known left right) (nextLeft : α → OracleComp OracleWorld β)
    (nextRight : α → OracleComp PreparedWorld β)
    (hnext : ∀ value, Related known (nextLeft value) (nextRight value)) :
    Related known (left >>= nextLeft) (right >>= nextRight) := by
  intro cache hknown
  rw [sourceRun_bind, targetRun_bind]
  trans 𝒟[targetRun right cache >>= fun a => sourceRun (nextLeft a.1.1) a.2 >>= fun b =>
    pure ((b.1.1, a.1.2 + b.1.2), b.2)]
  · rw [evalDist_bind, h cache hknown, evalDist_bind]
  · apply evalDist_bind_congr
    intro a ha
    have hcache := prepared_support_cache_le (countPreparedQueries right) cache a.1 a.2 ha
    rw [bind_pure_comp, bind_pure_comp, evalDist_map, evalDist_map,
      hnext a.1.1 a.2 (hknown.trans hcache)]

theorem Related.map {α β : Type} {known : QueryCache HashSpec}
    {left : OracleComp OracleWorld α} {right : OracleComp PreparedWorld α}
    (h : Related known left right) (f : α → β) : Related known (f <$> left) (f <$> right) := by
  simpa only [bind_pure_comp] using h.bind (fun value => pure (f value))
    (fun value => pure (f value)) (fun value => Related.pure' known (f value))

theorem counted_ordinaryWorld_query (input : OracleWorld.Domain) :
    simulateQ preparedCountedOracle (ordinaryWorld input) = countedOracle input := by
  cases input <;> rw [ordinaryWorld, simulateQ_spec_query] <;> rfl

/-- Ordinary calls, including arbitrary adversarial hash inputs, use exactly the same shared
cache and call counter on the two sides. -/
theorem Related.ordinary {α : Type} (known : QueryCache HashSpec)
    (computation : OracleComp OracleWorld α) :
    Related known computation (simulateQ ordinaryWorld computation) := by
  intro cache hknown
  rw [sourceRun_eq_counted, targetRun_eq_counted, ← QueryImpl.simulateQ_compose]
  have himpl : preparedCountedOracle ∘ₛ ordinaryWorld = countedOracle := by
    funext input
    exact counted_ordinaryWorld_query input
  rw [himpl]

/-- Lift the relation through a transcript-writing adversarial oracle simulation. -/
theorem Related.simulateQ_writer {I : Type} {spec : OracleSpec I} {α : Type}
    (known : QueryCache HashSpec)
    (left : QueryImpl spec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (right : QueryImpl spec (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)))
    (h : ∀ input, Related known (left input).run (right input).run)
    (computation : OracleComp spec α) :
    Related known (simulateQ left computation).run (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact Related.pure' known _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind]
      apply (h input).bind
      intro result
      exact (ih result.1).map _

/-- An ordinary source-world program embeds directly into the prepared world. -/
theorem ordinaryWorld_lift_hash {α : Type} (computation : OracleComp HashSpec α) :
    simulateQ ordinaryWorld (liftM computation : OracleComp OracleWorld α) =
      (liftM computation : OracleComp PreparedWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, simulateQ_bind, ih]
      apply congrArg (fun first => first >>= fun answer => (liftM (next answer) : OracleComp PreparedWorld α))
      change simulateQ ordinaryWorld (liftM (OracleWorld.query (.inr input))) = _
      rw [simulateQ_spec_query]
      rfl

variable [Params]

theorem Related.sign (seed : MasterSeed) (material : Material) (root : Digest) (message : Message) :
    Related (programCache ∅ seed material)
      (Randomized.sign ⟨seed, parameter material, root⟩ message) (PreparedScheme.sign material root message) := by
  have h := Related.honest seed material (Randomized.sign ⟨seed, parameter material, root⟩ message)
  rw [compile_sign] at h
  exact h

/-- Public-key equality and the explicit seed substitution suffice for the whole adversarial
signing interaction. Raw adversarial hash queries retain their original semantics. -/
theorem Related.adversary (seed : MasterSeed) (material : Material) (root : Digest)
    (adversary : Adversary) :
    Related (programCache ∅ seed material)
      (simulateQ (QueryImpl.ofLift OracleWorld
        (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) +
        signingOracle ⟨seed, parameter material, root⟩)
        (adversary.main ⟨root, parameter material⟩)).run
      (simulateQ (ordinaryWorld.liftTarget
        (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) +
        materialSigningOracle material root)
        (adversary.main ⟨root, parameter material⟩)).run := by
  apply Related.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      change Related _ ((fun answer => (answer, [])) <$>
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _))
        ((fun answer => (answer, [])) <$> ordinaryWorld input)
      have h := Related.ordinary (programCache ∅ seed material)
        (liftM (OracleWorld.query input) : OracleComp OracleWorld _)
      rw [simulateQ_spec_query] at h
      exact h.map _
  | inr message =>
      simp only [QueryImpl.add_apply_inr, signingOracle, materialSigningOracle,
        QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (Related.sign seed material root message).map _

omit [Params] in
theorem targetRun_map {α β : Type} (f : α → β) (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) :
    targetRun (f <$> computation) cache =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$> targetRun computation cache := by
  simp only [targetRun, countPreparedQueries, SphincsBase.QueryCap.counted_map,
    simulateQ_map, StateT.run_map]

omit [Params] in
theorem Related.bind_on_support {α β : Type} {known : QueryCache HashSpec}
    {left : OracleComp OracleWorld α} {right : OracleComp PreparedWorld α}
    (h : Related known left right) (nextLeft : α → OracleComp OracleWorld β)
    (nextRight : α → OracleComp PreparedWorld β)
    (hnext : ∀ cache, known ≤ cache → ∀ result ∈ support (targetRun right cache),
      Related known (nextLeft result.1.1) (nextRight result.1.1)) :
    Related known (left >>= nextLeft) (right >>= nextRight) := by
  intro cache hknown
  rw [sourceRun_bind, targetRun_bind]
  trans 𝒟[targetRun right cache >>= fun a => sourceRun (nextLeft a.1.1) a.2 >>= fun b =>
    pure ((b.1.1, a.1.2 + b.1.2), b.2)]
  · rw [evalDist_bind, h cache hknown, evalDist_bind]
  · apply evalDist_bind_congr
    intro a ha
    have hcache := prepared_support_cache_le (countPreparedQueries right) cache a.1 a.2 ha
    rw [bind_pure_comp, bind_pure_comp, evalDist_map, evalDist_map,
      hnext cache hknown a ha a.2 (hknown.trans hcache)]

noncomputable def sourceRest (adversary : Adversary) (publicKey : PublicKey)
    (secretKey : Seeded.SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle secretKey)
      (adversary.main publicKey)).run
  let verified ← liftM (Concrete.verify publicKey forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def targetRest (material : Material) (adversary : Adversary) (publicKey : PublicKey) :
    OracleComp PreparedWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (ordinaryWorld.liftTarget (WriterT (QueryLog SigningSpec) (OracleComp PreparedWorld)) +
      materialSigningOracle material publicKey.root) (adversary.main publicKey)).run
  let verified ← liftM (Concrete.verify publicKey forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem Related.rest (seed : MasterSeed) (material : Material) (root : Digest) (adversary : Adversary) :
    Related (programCache ∅ seed material)
      (sourceRest adversary ⟨root, parameter material⟩ ⟨seed, parameter material, root⟩)
      (targetRest material adversary ⟨root, parameter material⟩) := by
  unfold sourceRest targetRest
  apply (Related.adversary seed material root adversary).bind
  intro result
  have h := Related.ordinary (programCache ∅ seed material)
    (liftM (Concrete.verify ⟨root, parameter material⟩ result.1.message result.1.signature :
      OracleComp HashSpec Bool) : OracleComp OracleWorld Bool)
  rw [ordinaryWorld_lift_hash] at h
  exact h.bind _ _ (fun value => Related.pure' _ _)

/-- The seed-independent root computation includes the parameter derivation's virtual cost. -/
noncomputable def materialRoot (material : Material) : OracleComp PreparedHashSpec Digest := do
  let _ ← tick
  simulateQ (compileHash 0 material)
    (Seeded.treeRoot (parameter material) topLayer Concrete.rootTree 0 : OracleComp HashSpec Digest)

theorem keygen_map_root (material : Material) :
    keygen material = (fun root => (⟨root, parameter material⟩, ⟨0, parameter material, root⟩)) <$>
      materialRoot material := by
  rw [keygen_eq]
  simp only [materialRoot, map_bind, bind_pure_comp]

theorem gameAfterSeed_eq_bind (seed : MasterSeed) (adversary : Adversary) :
    gameAfterSeed adversary seed = (liftM (Seeded.keygenFromSeed seed) : OracleComp OracleWorld _) >>=
      fun result => sourceRest adversary result.1 result.2 := rfl

theorem materialGame_eq_bind (material : Material) (adversary : Adversary) :
    materialGame material adversary = (liftM (keygen material) : OracleComp PreparedWorld _) >>=
      fun result => targetRest material adversary result.1 := rfl

/-- Full-game erasure of honest seed derivations. The target still runs on the programmed
shared cache, so this statement makes no premature independence claim about adversarial answers. -/
theorem Related.gameAfterSeed (seed : MasterSeed) (material : Material) (adversary : Adversary) :
    Related (programCache ∅ seed material) (gameAfterSeed adversary seed) (materialGame material adversary) := by
  have hkey := Related.honest seed material
    (liftM (Seeded.keygenFromSeed seed) : OracleComp OracleWorld _)
  rw [compileWorld_lift_hash, compile_keygen, keygen_map_root, Functor.map_map, liftM_map] at hkey
  have hgame := hkey.bind_on_support
    (fun result => sourceRest adversary result.1 result.2)
    (fun result => targetRest material adversary result.1) (by
      intro cache hcache result hresult
      rw [targetRun_map, support_map] at hresult
      obtain ⟨⟨⟨root, cost⟩, finalCache⟩, hroot, rfl⟩ := hresult
      exact Related.rest seed material root adversary)
  rw [gameAfterSeed_eq_bind, materialGame_eq_bind, keygen_map_root, liftM_map, bind_map_left]
  simpa only [bind_map_left, reseedKey] using hgame

end SphincsFors.Security.MaterialGameCoupling
