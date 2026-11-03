import FORS.Reduction.ShortInputs
import FORS.Seed.Coupling

/-! Long adversarial hash inputs are simulated privately by the adversary. No honest party or
verifier queries an input longer than 2084 bytes, so the adversary can answer its long inputs from
a private cache. This file defines the internalized adversary, the run relation (`Block`) between
the original and the internalized executions with their short and total query counts, and shows
that the internalized game only queries short inputs. `Reduction/InternalizeGame` applies it to the
deterministic game. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Internalize

variable [Params]

open Completeness SeedCoupling Short

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def LongQuery : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ¬IsShort input

def ShortQuery : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => IsShort input

instance : DecidablePred LongQuery := fun input => by unfold LongQuery; split <;> infer_instance
instance : DecidablePred ShortQuery := fun input => by unfold ShortQuery; split <;> infer_instance

/-- Every hash query of a world computation is short. -/
def OnlyW {α : Type} (oa : OracleComp OracleWorld α) : Prop := oa.IsQueryBoundP LongQuery 0

theorem OnlyW.pure' {α : Type} (value : α) : OnlyW (pure value : OracleComp OracleWorld α) := trivial

theorem OnlyW.bind {α β : Type} {oa : OracleComp OracleWorld α}
    {next : α → OracleComp OracleWorld β}
    (h : OnlyW oa) (hnext : ∀ value, OnlyW (next value)) : OnlyW (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [OnlyW] using this

theorem OnlyW.map {α β : Type} {oa : OracleComp OracleWorld α} (f : α → β) (h : OnlyW oa) :
    OnlyW (f <$> oa) := by
  rw [OnlyW, isQueryBoundP_map_iff]
  exact h

theorem OnlyW.liftHash {α : Type} {oa : OracleComp HashSpec α} (h : Short.Only oa) :
    OnlyW (liftM oa : OracleComp OracleWorld α) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyW.pure' _
  | query_bind input next ih =>
      rw [Short.Only, isQueryBoundP_query_bind_iff] at h
      rw [liftM_bind]
      refine OnlyW.bind ?_ (fun answer => ih answer ?_)
      · change OnlyW (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _)
        rw [OnlyW, isQueryBoundP_query_iff]
        intro hlong
        rcases h.1 with hshort | hzero
        · exact absurd (Classical.not_not.mp hshort) hlong
        · omega
      · have hnext := h.2 answer
        split at hnext <;> simpa [Short.Only] using hnext

theorem OnlyW.liftProb {α : Type} (oa : ProbComp α) :
    OnlyW (liftM oa : OracleComp OracleWorld α) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyW.pure' _
  | query_bind input next ih =>
      rw [liftM_bind]
      refine OnlyW.bind ?_ ih
      change OnlyW (liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _)
      rw [OnlyW, isQueryBoundP_query_iff]
      intro h
      exact h.elim

/-- Separate counts of short and long hash calls. -/
noncomputable def count2 {α : Type} (oa : OracleComp OracleWorld α) :
    OracleComp OracleWorld ((α × Nat) × Nat) :=
  QueryCap.counted ShortQuery (QueryCap.counted LongQuery oa)

theorem count2_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    count2 (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← count2 (next answer)
      pure ((result.1.1, (if LongQuery input then 1 else 0) + result.1.2),
        (if ShortQuery input then 1 else 0) + result.2)) := by
  simp only [count2, QueryCap.counted_bind, QueryCap.counted_pure, bind_assoc,
    pure_bind, Nat.add_zero]
  rfl

theorem count2_pure {α : Type} (value : α) :
    count2 (pure value : OracleComp OracleWorld α) = pure ((value, 0), 0) := rfl

theorem countHashQueries_eq_count2 {α : Type} (oa : OracleComp OracleWorld α) :
    countHashQueries oa = (fun result => (result.1.1, result.2 + result.1.2)) <$> count2 oa := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [countHashQueries_query_bind, count2_query_bind]
      simp only [ih, map_bind, map_pure, bind_map_left]
      apply bind_congr
      intro answer
      apply bind_congr
      intro result
      congr 2
      cases input with
      | inl draw => simp [LongQuery, ShortQuery]
      | inr bytes =>
          by_cases hshort : IsShort bytes <;> simp [LongQuery, ShortQuery, hshort] <;> omega

theorem bind_map_congr' {α β β' γ : Type} (x : ProbComp α) (f : α → β) (g : α → β')
    (k₁ : β → ProbComp γ) (k₂ : β' → ProbComp γ) (h : ∀ a, k₁ (f a) = k₂ (g a)) :
    (f <$> x) >>= k₁ = (g <$> x) >>= k₂ := by
  rw [bind_map_left, bind_map_left]
  exact bind_congr h

/-- Overlay the short entries of one cache on the long entries of another. -/
def merge (short long : QueryCache HashSpec) : QueryCache HashSpec :=
  fun input => if IsShort input then short input else long input

theorem merge_cacheQuery_short (short long : QueryCache HashSpec) {input : HashInput}
    (hinput : IsShort input) (answer : HashOutput) :
    (merge short long).cacheQuery input answer = merge (short.cacheQuery input answer) long := by
  funext query
  by_cases hq : query = input
  · subst query
    simp [merge, hinput, QueryCache.cacheQuery_self]
  · simp only [merge, QueryCache.cacheQuery_of_ne _ _ hq]

theorem merge_cacheQuery_long (short long : QueryCache HashSpec) {input : HashInput}
    (hinput : ¬IsShort input) (answer : HashOutput) :
    (merge short long).cacheQuery input answer = merge short (long.cacheQuery input answer) := by
  funext query
  by_cases hq : query = input
  · subst query
    simp [merge, hinput, QueryCache.cacheQuery_self]
  · simp only [merge, QueryCache.cacheQuery_of_ne _ _ hq]

/-- A short-only world computation sees only the short part of the cache and leaves the long
part unchanged. -/
theorem run_count2_short {α : Type} (oa : OracleComp OracleWorld α) (h : OnlyW oa)
    (short long : QueryCache HashSpec) :
    (simulateQ romImpl (count2 oa)).run (merge short long) =
      (fun result => (((result.1.1, 0), result.1.2), merge result.2 long)) <$>
        (simulateQ romImpl (countHashQueries oa)).run short := by
  induction oa using OracleComp.inductionOn generalizing short with
  | pure value => simp [count2_pure, countHashQueries]; rfl
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      rw [count2_query_bind, countHashQueries_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, map_bind, map_pure]
      cases input with
      | inl draw =>
          have hnext : ∀ answer, OnlyW (next answer) := fun answer => by
            simpa [OnlyW, LongQuery] using h.2 answer
          change ((fun answer => (answer, merge short long)) <$>
              (liftM (unifSpec.query draw) : ProbComp _)) >>= _ =
            ((fun answer => (answer, short)) <$> (liftM (unifSpec.query draw) : ProbComp _)) >>= _
          refine bind_map_congr' _ _ _ _ _ (fun answer => ?_)
          dsimp only
          rw [ih answer (hnext answer) short]
          simp [LongQuery, ShortQuery]
      | inr bytes =>
          have hshort : IsShort bytes := by
            rcases h.1 with hnot | hzero
            · simpa [LongQuery] using hnot
            · omega
          have hnext : ∀ answer, OnlyW (next answer) := fun answer => by
            simpa [OnlyW, LongQuery, hshort] using h.2 answer
          change (randomOracle (spec := HashSpec) bytes).run (merge short long) >>= _ =
            (randomOracle (spec := HashSpec) bytes).run short >>= _
          have hlookup : merge short long bytes = short bytes := by simp [merge, hshort]
          cases hc : short bytes with
          | some answer =>
              rw [QueryImpl.withCaching_run_some _ (hlookup.trans hc),
                QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind,
                ih answer (hnext answer) short]
              simp [LongQuery, ShortQuery, hshort]
          | none =>
              rw [QueryImpl.withCaching_run_none _ (hlookup.trans hc),
                QueryImpl.withCaching_run_none _ hc]
              refine bind_map_congr' _ _ _ _ _ (fun answer => ?_)
              dsimp only
              rw [merge_cacheQuery_short short long hshort,
                ih answer (hnext answer) (short.cacheQuery bytes answer)]
              simp [LongQuery, ShortQuery, hshort]

/-! ### Short counts and the generic run relation -/

noncomputable def countShort {α : Type} (oa : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  QueryCap.counted ShortQuery oa

theorem countShort_eq_count2 {α : Type} (oa : OracleComp OracleWorld α) :
    countShort oa = (fun result => (result.1.1, result.2)) <$> count2 oa := by
  induction oa using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [countShort, QueryCap.counted_query_bind, count2_query_bind]
      simp only [map_bind, map_pure]
      refine bind_congr (fun answer => ?_)
      have hih := ih answer
      rw [countShort] at hih
      rw [hih, bind_map_left]

noncomputable def leftRun {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp ((α × Nat) × QueryCache HashSpec) :=
  (simulateQ romImpl (countShort oa)).run cache

noncomputable def rightRun {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp ((α × Nat) × QueryCache HashSpec) :=
  (simulateQ romImpl (countHashQueries oa)).run cache

theorem leftRun_bind {α β : Type} (oa : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    leftRun (oa >>= next) cache = leftRun oa cache >>= fun first =>
      (fun second => ((second.1.1, first.1.2 + second.1.2), second.2)) <$>
        leftRun (next first.1.1) first.2 := by
  simp only [leftRun, countShort, QueryCap.counted_bind, simulateQ_bind,
    StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map]

theorem rightRun_bind {α β : Type} (oa : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    rightRun (oa >>= next) cache = rightRun oa cache >>= fun first =>
      (fun second => ((second.1.1, first.1.2 + second.1.2), second.2)) <$>
        rightRun (next first.1.1) first.2 := by
  simp only [rightRun, countHashQueries, QueryCap.counted_bind, simulateQ_bind,
    StateT.run_bind, bind_pure_comp, simulateQ_map, StateT.run_map]

theorem leftRun_map {α β : Type} (f : α → β) (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    leftRun (f <$> oa) cache = (fun result => ((f result.1.1, result.1.2), result.2)) <$>
      leftRun oa cache := by
  simp only [leftRun, countShort, QueryCap.counted_map, simulateQ_map, StateT.run_map]

theorem rightRun_map {α β : Type} (f : α → β) (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    rightRun (f <$> oa) cache = (fun result => ((f result.1.1, result.1.2), result.2)) <$>
      rightRun oa cache := by
  simp only [rightRun, countHashQueries, QueryCap.counted_map, simulateQ_map,
    StateT.run_map]

theorem leftRun_short {α : Type} (oa : OracleComp OracleWorld α) (h : OnlyW oa)
    (short long : QueryCache HashSpec) :
    leftRun oa (merge short long) =
      (fun result => (result.1, merge result.2 long)) <$> rightRun oa short := by
  rw [leftRun, countShort_eq_count2, simulateQ_map, StateT.run_map, run_count2_short oa h,
    rightRun, Functor.map_map]

/-- Relating two computations through a shared distributional quotient. -/
theorem evalDist_bind_rel {X Y Z W : Type} (x : ProbComp X) (y : ProbComp Y)
    (F : X → W) (G : Y → W) (hxy : 𝒟[F <$> x] = 𝒟[G <$> y])
    (f : X → ProbComp Z) (g : Y → ProbComp Z) (k : W → ProbComp Z)
    (hf : ∀ r, 𝒟[f r] = 𝒟[k (F r)]) (hg : ∀ r, 𝒟[g r] = 𝒟[k (G r)]) :
    𝒟[x >>= f] = 𝒟[y >>= g] := by
  calc 𝒟[x >>= f] = 𝒟[x >>= fun r => k (F r)] := evalDist_bind_congr' x (fun r => hf r)
    _ = 𝒟[(F <$> x) >>= k] := by rw [bind_map_left]
    _ = 𝒟[(G <$> y) >>= k] := by rw [evalDist_bind, hxy, ← evalDist_bind]
    _ = 𝒟[y >>= fun r => k (G r)] := by rw [bind_map_left]
    _ = 𝒟[y >>= g] := (evalDist_bind_congr' y (fun r => hg r)).symm

theorem evalDist_map_congr_of_evalDist_eq {X W : Type} (x y : ProbComp X) (h : 𝒟[x] = 𝒟[y])
    (f g : X → W) (hfg : ∀ a, f a = g a) : 𝒟[f <$> x] = 𝒟[g <$> y] := by
  rw [evalDist_map, evalDist_map, h, funext hfg]

theorem evalDist_map_rel {X Y V W : Type} (x : ProbComp X) (y : ProbComp Y) (vX : X → V)
    (vY : Y → V) (h : 𝒟[vX <$> x] = 𝒟[vY <$> y]) (c : V → W) (f : X → W) (g : Y → W)
    (hf : ∀ a, f a = c (vX a)) (hg : ∀ b, g b = c (vY b)) : 𝒟[f <$> x] = 𝒟[g <$> y] := by
  have hf' : f = c ∘ vX := funext hf
  have hg' : g = c ∘ vY := funext hg
  rw [hf', hg']
  calc 𝒟[(c ∘ vX) <$> x] = 𝒟[c <$> (vX <$> x)] := by rw [Functor.map_map]; rfl
    _ = c <$> 𝒟[vX <$> x] := evalDist_map _ _
    _ = c <$> 𝒟[vY <$> y] := by rw [h]
    _ = 𝒟[c <$> (vY <$> y)] := (evalDist_map _ _).symm
    _ = 𝒟[(c ∘ vY) <$> y] := by rw [Functor.map_map]; rfl

/-! ### The internalized adversary -/

abbrev AdvSpec := OracleWorld + SigningSpec

noncomputable def liftWorldImpl : QueryImpl OracleWorld (OracleComp AdvSpec) :=
  fun t => liftM (AdvSpec.query (Sum.inl t))

/-- Embed a world computation as the left component of the adversary's interface. -/
noncomputable def liftWorld {α : Type} (x : OracleComp OracleWorld α) : OracleComp AdvSpec α :=
  simulateQ liftWorldImpl x

/-- A private lazy table answers long inputs from the adversary's own randomness. -/
noncomputable def privateRead (input : HashInput) :
    StateT (QueryCache HashSpec) (OracleComp AdvSpec) HashOutput := fun cache =>
  match cache input with
  | some answer => pure (answer, cache)
  | none => (fun answer => (answer, cache.cacheQuery input answer)) <$>
      liftWorld (liftM ($ᵗ HashOutput : ProbComp HashOutput) : OracleComp OracleWorld HashOutput)

/-- Forward a query unchanged, keeping the private table. -/
noncomputable def forward (input : AdvSpec.Domain) :
    StateT (QueryCache HashSpec) (OracleComp AdvSpec) (AdvSpec.Range input) := fun cache =>
  (fun answer => (answer, cache)) <$> (liftM (AdvSpec.query input) : OracleComp AdvSpec _)

noncomputable def internalImpl :
    QueryImpl AdvSpec (StateT (QueryCache HashSpec) (OracleComp AdvSpec))
  | .inl (.inl draw) => forward (.inl (.inl draw))
  | .inl (.inr input) => if IsShort input then forward (.inl (.inr input)) else privateRead input
  | .inr message => forward (.inr message)

/-- The adversary with every long hash input answered privately. -/
noncomputable def internalize (adversary : Adversary) : Adversary :=
  ⟨fun publicKey => (simulateQ internalImpl (adversary.main publicKey)).run' ∅⟩

/-- Left result: output, log, short count, cache. Right result: the same with the private table
merged back into the shared cache. -/
def leftView {β : Type} (result : ((β × QueryLog SigningSpec) × Nat) × QueryCache HashSpec) :
    (β × QueryLog SigningSpec) × Nat × QueryCache HashSpec :=
  (result.1.1, result.1.2, result.2)

def rightView {β : Type}
    (result : (((β × QueryCache HashSpec) × QueryLog SigningSpec) × Nat) × QueryCache HashSpec) :
    (β × QueryLog SigningSpec) × Nat × QueryCache HashSpec :=
  ((result.1.1.1.1, result.1.1.2), result.1.2, merge result.2 result.1.1.1.2)

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit Seeded.finishSign
  FORS.Seeded.signAttempt

theorem OnlyW.queryShort {input : HashInput} (h : IsShort input) :
    OnlyW (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _) := by
  rw [OnlyW, isQueryBoundP_query_iff]
  intro hlong
  exact absurd h hlong

theorem OnlyW.queryDraw (draw : unifSpec.Domain) :
    OnlyW (liftM (OracleWorld.query (.inl draw)) : OracleComp OracleWorld _) := by
  rw [OnlyW, isQueryBoundP_query_iff]
  intro h
  exact h.elim

theorem OnlyW.writerLift {α : Type} {oa : OracleComp OracleWorld α} (h : OnlyW oa) :
    OnlyW (liftM oa : WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) α).run := by
  rw [WriterT.run_liftM]
  exact OnlyW.map _ h

theorem run_simulateQ_ofLift_writer {α : Type} (x : OracleComp OracleWorld α) :
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) x).run =
      (fun value => (value, ∅)) <$> x := by
  induction x using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query, QueryImpl.ofLift_apply]
      change (liftM (liftM (OracleWorld.query input) : OracleComp OracleWorld _) :
        WriterT (QueryLog SigningSpec) (OracleComp OracleWorld) _).run >>= _ = _
      rw [WriterT.run_liftM, bind_map_left, map_bind]
      refine bind_congr (fun answer => ?_)
      dsimp only
      rw [ih answer]
      simp

theorem rightRun_liftProb {α : Type} (p : ProbComp α) (cache : QueryCache HashSpec) :
    rightRun (liftM p : OracleComp OracleWorld α) cache = (fun value => ((value, 0), cache)) <$> p := by
  rw [rightRun, countHashQueries_lift_prob, simulateQ_map, StateT.run_map, run_lift_prob,
    Functor.map_map]

theorem leftRun_longQuery {input : HashInput} (h : ¬IsShort input) (cache : QueryCache HashSpec) :
    leftRun (liftM (OracleWorld.query (.inr input))) cache =
      (fun result => ((result.1, 0), result.2)) <$> (randomOracle (spec := HashSpec) input).run cache := by
  rw [leftRun, countShort, QueryCap.counted_query, simulateQ_map, simulateQ_spec_query,
    StateT.run_map]
  simp only [ShortQuery, h, ↓reduceIte]
  rfl

/-! ### Verification and the split-count run -/

/-- The verifier and the final transcript test. -/
noncomputable def verifyPart (publicKey : PublicKey)
    (output : Forgery × QueryLog SigningSpec) : OracleComp OracleWorld Bool := do
  let verified ← liftM (Concrete.verify publicKey output.1.message output.1.signature :
    OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid output.2 ∧ ¬SigningTranscript.Contains output.2 output.1) &&
    verified

theorem OnlyW.verifyPart (publicKey : PublicKey) (output : Forgery × QueryLog SigningSpec) :
    OnlyW (verifyPart publicKey output) :=
  OnlyW.bind (OnlyW.liftHash (Short.Only.verify _ _ _)) (fun _ => OnlyW.pure' _)

theorem merge_empty : merge ∅ ∅ = (∅ : QueryCache HashSpec) := by
  funext input
  simp [merge]

/-- The short-count run and the total-count run are projections of one split-count run. -/
theorem leftRun_eq_split {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    leftRun oa cache = (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
      (simulateQ romImpl (count2 oa)).run cache := by
  rw [leftRun, countShort_eq_count2, simulateQ_map, StateT.run_map]

theorem rightRun_eq_split {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    rightRun oa cache = (fun result => ((result.1.1.1, result.1.2 + result.1.1.2), result.2)) <$>
      (simulateQ romImpl (count2 oa)).run cache := by
  rw [rightRun, countHashQueries_eq_count2, simulateQ_map, StateT.run_map]

end FORS.Security.Internalize

namespace FORS.Security.Internalize

variable [Params]
open Completeness SeedCoupling Short

attribute [local irreducible] count2 leftRun rightRun sampleMasterSeed

/-! ### The internalized game only queries short inputs -/

def LongAdv : AdvSpec.Domain → Prop
  | .inl (.inr input) => ¬IsShort input
  | _ => False

instance : DecidablePred LongAdv := fun input => by unfold LongAdv; split <;> infer_instance

def OnlyAdv {β : Type} (M : OracleComp AdvSpec β) : Prop := M.IsQueryBoundP LongAdv 0

theorem OnlyAdv.bind {α β : Type} {oa : OracleComp AdvSpec α} {next : α → OracleComp AdvSpec β}
    (h : OnlyAdv oa) (hnext : ∀ value, OnlyAdv (next value)) : OnlyAdv (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [OnlyAdv] using this

theorem OnlyAdv.map {α β : Type} {oa : OracleComp AdvSpec α} (f : α → β) (h : OnlyAdv oa) :
    OnlyAdv (f <$> oa) := by
  rw [OnlyAdv, isQueryBoundP_map_iff]
  exact h

theorem OnlyAdv.query {input : AdvSpec.Domain} (h : ¬LongAdv input) :
    OnlyAdv (liftM (AdvSpec.query input) : OracleComp AdvSpec _) := by
  rw [OnlyAdv, isQueryBoundP_query_iff]
  intro hlong
  exact absurd hlong h

theorem OnlyAdv.ofLiftWorld {α : Type} (x : OracleComp OracleWorld α) (h : OnlyW x) :
    OnlyAdv (liftWorld x) := by
  induction x using OracleComp.inductionOn with
  | pure value => simp [OnlyAdv, liftWorld]
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      rw [liftWorld, simulateQ_bind, simulateQ_spec_query]
      refine OnlyAdv.bind (OnlyAdv.query ?_) (fun answer => ih answer ?_)
      · rcases input with draw | bytes
        · simp [LongAdv]
        · rcases h.1 with hnot | hzero
          · simpa [LongAdv, LongQuery] using hnot
          · omega
      · have := h.2 answer
        split at this <;> simpa [OnlyW] using this

theorem OnlyAdv.liftWorldProb {α : Type} (p : ProbComp α) :
    OnlyAdv (liftWorld (liftM p : OracleComp OracleWorld α)) :=
  OnlyAdv.ofLiftWorld _ (OnlyW.liftProb p)

theorem OnlyAdv.internal {β : Type} (M : OracleComp AdvSpec β) (cache : QueryCache HashSpec) :
    OnlyAdv ((simulateQ internalImpl M).run cache) := by
  induction M using OracleComp.inductionOn generalizing cache with
  | pure value => simp [OnlyAdv]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine OnlyAdv.bind ?_ (fun result => ih result.1 result.2)
      rcases input with (draw | bytes) | message
      · exact OnlyAdv.map _ (OnlyAdv.query (by simp [LongAdv]))
      · by_cases h : IsShort bytes
        · simp only [internalImpl, h, ↓reduceIte]
          exact OnlyAdv.map _ (OnlyAdv.query (by simp [LongAdv, h]))
        · simp only [internalImpl, h, ↓reduceIte, StateT.run, privateRead]
          split
          · simp [OnlyAdv]
          · exact OnlyAdv.map _ (OnlyAdv.liftWorldProb _)
      · exact OnlyAdv.map _ (OnlyAdv.query (by simp [LongAdv]))

end FORS.Security.Internalize
