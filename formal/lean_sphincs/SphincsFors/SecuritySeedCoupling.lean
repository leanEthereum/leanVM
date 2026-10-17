import SphincsFors.SecuritySeedModel
import SphincsFors.World
import SphincsFors.Statement
import SphincsBase.Proof.Base.QueryCap
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-! Finite fresh-table preparation and the candidate's parameter-dependent derivation table.
The generic finite-table proof is adapted from leanVM b7a107256. Preparation explicitly performs
oracle queries; later theorems relate it to independent full-output material and its programmed
cache. Preparation is not silently counted as part of an adversary's existing query budget. -/

open OracleComp OracleSpec

namespace SphincsFors.Security.SeedCoupling

def finHeadTailEquiv (α : Type) (count : Nat) :
    (α × (Fin count → α)) ≃ (Fin (count + 1) → α) where
  toFun pair := Fin.cases pair.1 pair.2
  invFun values := (values 0, fun index => values index.succ)
  left_inv pair := by
    apply Prod.ext
    · simp
    · funext index
      simp
  right_inv values := by
    funext index
    cases index using Fin.cases <;> simp

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] [SampleableType (α × β)] :
    evalDist (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =
    evalDist ($ᵗ (α × β)) := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

variable {D R : Type} [DecidableEq D]

def cacheFin : {n : Nat} → QueryCache (D →ₒ R) → (Fin n → D) → (Fin n → R) →
    QueryCache (D →ₒ R)
  | 0, cache, _, _ => cache
  | _ + 1, cache, inputs, outputs =>
      cacheFin (cache.cacheQuery (inputs 0) (outputs 0))
        (fun i => inputs i.succ) (fun i => outputs i.succ)

theorem cacheFin_apply_of_not_mem {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (outputs : Fin n → R) (input : D)
    (hinput : ∀ i, input ≠ inputs i) : cacheFin cache inputs outputs input = cache input := by
  induction n generalizing cache with
  | zero => rfl
  | succ n ih =>
      rw [cacheFin, ih _ _ _ (fun i => hinput i.succ)]
      exact QueryCache.cacheQuery_of_ne cache (outputs 0) (hinput 0)

theorem cacheFin_apply {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (hinj : Function.Injective inputs) (outputs : Fin n → R) (i : Fin n) :
    cacheFin cache inputs outputs (inputs i) = some (outputs i) := by
  induction n generalizing cache with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [cacheFin, cacheFin_apply_of_not_mem]
          · exact QueryCache.cacheQuery_self _ _ _
          · intro j h
            have := hinj h
            exact Fin.succ_ne_zero j this.symm
      | succ i =>
          exact ih _ _ (fun _ _ h => Fin.succ_injective _ (hinj h)) _ i

variable [SampleableType R]

/-- Distinct fresh inputs give independent full outputs and the cache that records them. -/
theorem run_sequenceFin_fresh {n : Nat} (inputs : Fin n → D)
    (hinj : Function.Injective inputs) (cache : QueryCache (D →ₒ R))
    (hfresh : ∀ i, cache (inputs i) = none) :
    (simulateQ randomOracle (Concrete.sequenceFin fun i =>
      (liftM ((D →ₒ R).query (inputs i)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)
        pure (outputs, cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero => simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, pure_bind, cacheFin]
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh 0)]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp, map_bind]
      change (($ᵗ R) >>= _) = (($ᵗ R) >>= _)
      apply bind_congr
      intro head
      have htail : ∀ i : Fin n, (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro h
          exact Fin.succ_ne_zero i (hinj h)
      rw [ih (fun i => inputs i.succ) (fun _ _ h => Fin.succ_injective _ (hinj h)) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheFin]
      rfl

theorem evalDist_sequenceFin_uniform [Fintype R] (n : Nat) :
    𝒟[Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)] =
      𝒟[$ᵗ (Fin n → R)] := by
  classical
  induction n with
  | zero =>
      apply SPMF.ext
      intro values
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [Concrete.sequenceFin, heq]
  | succ n ih =>
      calc
        _ = 𝒟[finHeadTailEquiv R n <$> (do
            let head ← $ᵗ R
            let tail ← $ᵗ (Fin n → R)
            pure (head, tail))] := by
          simp only [Concrete.sequenceFin, map_bind, finHeadTailEquiv,
            Equiv.coe_fn_mk, bind_pure_comp]
          rw [evalDist_bind, evalDist_bind]
          congr 1
          funext head
          rw [evalDist_map, ih, evalDist_map, evalDist_map, Functor.map_map]
        _ = 𝒟[finHeadTailEquiv R n <$> ($ᵗ (R × (Fin n → R)))] := by
          rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
        _ = _ := evalDist_map_bijective_uniform_cross
          (α := R × (Fin n → R)) (β := Fin (n + 1) → R)
          (finHeadTailEquiv R n) (finHeadTailEquiv R n).bijective

end SphincsFors.Security.SeedCoupling

namespace SphincsFors.Security.SeedCoupling

set_option backward.isDefEq.respectTransparency false

variable (J R : Type) [Fintype J]

noncomputable def finTableEquiv : (Fin (Fintype.card J) → R) ≃ (J → R) where
  toFun values j := values (Fintype.equivFin J j)
  invFun values i := values ((Fintype.equivFin J).symm i)
  left_inv values := by funext i; simp
  right_inv values := by funext j; simp

variable {J R} {D : Type} [DecidableEq D]

noncomputable def cacheTable (cache : QueryCache (D →ₒ R)) (inputs : J → D) (outputs : J → R) :
    QueryCache (D →ₒ R) :=
  cacheFin cache (fun i => inputs ((Fintype.equivFin J).symm i))
    ((finTableEquiv J R).symm outputs)

theorem cacheTable_apply (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (hinj : Function.Injective inputs) (outputs : J → R) (j : J) :
    cacheTable cache inputs outputs (inputs j) = some (outputs j) := by
  have h := cacheFin_apply cache (fun i => inputs ((Fintype.equivFin J).symm i))
    (hinj.comp (Fintype.equivFin J).symm.injective) ((finTableEquiv J R).symm outputs)
    (Fintype.equivFin J j)
  rw [(Fintype.equivFin J).symm_apply_apply] at h
  simpa only [cacheTable, finTableEquiv, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply] using h

theorem cacheTable_apply_of_not_mem (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (outputs : J → R) (input : D) (hinput : ∀ j, input ≠ inputs j) :
    cacheTable cache inputs outputs input = cache input :=
  cacheFin_apply_of_not_mem _ _ _ _ (fun _ => hinput _)

noncomputable def queryTable (inputs : J → D) : OracleComp (D →ₒ R) (J → R) :=
  finTableEquiv J R <$> Concrete.sequenceFin fun i =>
    (liftM ((D →ₒ R).query (inputs ((Fintype.equivFin J).symm i))) : OracleComp (D →ₒ R) R)

variable [SampleableType R] [Fintype R] [SampleableType (J → R)]

theorem evalDist_queryTable_fresh (inputs : J → D) (hinj : Function.Injective inputs)
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ j, cache (inputs j) = none) :
    𝒟[(simulateQ randomOracle (queryTable inputs)).run cache] =
      𝒟[(fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R))] := by
  classical
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  simp only [bind_pure_comp, Functor.map_map]
  rw [evalDist_map, evalDist_sequenceFin_uniform]
  have htable := evalDist_map_bijective_uniform_cross
    (α := Fin (Fintype.card J) → R) (β := J → R) (finTableEquiv J R) (finTableEquiv J R).bijective
  rw [evalDist_map, ← htable]
  simp only [evalDist_map, Functor.map_map]
  congr 1
  funext outputs
  simp only [cacheTable, Equiv.symm_apply_apply]

end SphincsFors.Security.SeedCoupling

namespace SphincsFors.Security.SeedCoupling
open SeedModel Completeness

set_option backward.isDefEq.respectTransparency false

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- After the parameter response, all remaining addresses are fixed independently of their
own answers. The two values of one hash have the same address. -/
def secretInputs (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : HashInput :=
  keygenHashInput (truncateHash parameterOutput) (secretDomain position) seed

theorem secretInputs_ne_parameter (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : secretInputs seed parameterOutput position ≠ parameterInput seed :=
  secretInput_ne_parameterInput seed (parameterOutput, fun _ => 0) position

/-- The derivation hashes: one per pair of chain starts, one per pair of FORS secrets, one per
surrogate, each named by the first value it gives. -/
abbrev HashPosition := {position : SecretPosition // isSecond position = false}
abbrev HashOutputs := HashPosition → HashOutput
/-- The values of the table that no hash answer uses. -/
abbrev UnusedPosition := {position : SecretPosition // ¬isSecond position = false}
abbrev UnusedOutputs := UnusedPosition → HashOutput

noncomputable instance hashPositionFintype : Fintype HashPosition := Fintype.ofFinite _
noncomputable instance hashPositionDecidableEq : DecidableEq HashPosition := Classical.decEq _
noncomputable instance unusedPositionFintype : Fintype UnusedPosition := Fintype.ofFinite _
noncomputable instance unusedPositionDecidableEq : DecidableEq UnusedPosition := Classical.decEq _
noncomputable instance hashOutputsFintype : Fintype HashOutputs := Fintype.ofFinite _
noncomputable instance unusedOutputsFintype : Fintype UnusedOutputs := Fintype.ofFinite _

noncomputable opaque hashOutputsSampleableType : SampleableType HashOutputs :=
  SampleableType.ofFintype HashOutputs

noncomputable opaque unusedOutputsSampleableType : SampleableType UnusedOutputs :=
  SampleableType.ofFintype UnusedOutputs

noncomputable local instance : SampleableType HashOutputs := hashOutputsSampleableType
noncomputable local instance : SampleableType UnusedOutputs := unusedOutputsSampleableType

/-- The addresses of the derivation hashes. -/
def hashInputs (seed : MasterSeed) (parameterOutput : HashOutput) (position : HashPosition) : HashInput :=
  secretInputs seed parameterOutput position.1

theorem hashInputs_ne_parameter (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : HashPosition) : parameterInput seed ≠ hashInputs seed parameterOutput position :=
  (secretInputs_ne_parameter seed parameterOutput position.1).symm

/-- Distinct derivation hashes have distinct inputs. -/
theorem hashInputs_injective (seed : MasterSeed) (parameterOutput : HashOutput) :
    Function.Injective (hashInputs seed parameterOutput) := by
  intro left right h
  have hfirst := firstOf_eq_of_secretInput_eq (seed := seed)
    (material := (parameterOutput, fun _ => 0)) (left := left.1) (right := right.1) h
  rw [firstOf_of_not_second left.2, firstOf_of_not_second right.2] at hfirst
  exact Subtype.ext hfirst

/-- The answers of the derivation hashes that the material programs. -/
noncomputable def hashAnswers (outputs : SecretOutputs) : HashOutputs :=
  fun position => mix outputs position.1

/-- **The programmed answers are independent uniform outputs.** `mix` is a bijection of the table
of uniform values, and the answers are its coordinates at the first values. -/
theorem evalDist_hashAnswers :
    𝒟[hashAnswers <$> ($ᵗ SecretOutputs)] = 𝒟[$ᵗ HashOutputs] := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun position : SecretPosition => isSecond position = false)
    (fun _ => HashOutput)
  have hmap : hashAnswers <$> ($ᵗ SecretOutputs) =
      Prod.fst <$> ((fun outputs => split (mix outputs)) <$> ($ᵗ SecretOutputs)) := by
    rw [Functor.map_map]
    rfl
  have hbij : Function.Bijective (fun outputs : SecretOutputs => split (mix outputs)) :=
    split.bijective.comp mix_involutive.bijective
  rw [hmap, evalDist_map,
    evalDist_map_bijective_uniform_cross (α := SecretOutputs) (β := HashOutputs × UnusedOutputs) _ hbij,
    ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-- Any function of the programmed answers has the law it has on independent uniform outputs. -/
theorem evalDist_map_hashAnswers {β : Type} (g : HashOutputs → β) :
    𝒟[(g ∘ hashAnswers) <$> ($ᵗ SecretOutputs)] = 𝒟[g <$> ($ᵗ HashOutputs)] := by
  have hsplit : (g ∘ hashAnswers) <$> ($ᵗ SecretOutputs) =
      g <$> (hashAnswers <$> ($ᵗ SecretOutputs)) := (Functor.map_map hashAnswers g ($ᵗ SecretOutputs)).symm
  rw [hsplit]
  exact (evalDist_map _ _).trans
    ((congrArg (fun distribution => g <$> distribution) evalDist_hashAnswers).trans
      (evalDist_map _ _).symm)

/-- The sequential finite-cache construction implements exactly the candidate programming map. -/
theorem cacheTable_eq_programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    cacheTable (base.cacheQuery (parameterInput seed) material.1)
      (hashInputs seed material.1) (hashAnswers material.2) = programCache base seed material := by
  funext input
  by_cases hp : input = parameterInput seed
  · subst input
    rw [cacheTable_apply_of_not_mem (base.cacheQuery (parameterInput seed) material.1)
      (hashInputs seed material.1) (hashAnswers material.2) (parameterInput seed)
      (hashInputs_ne_parameter seed material.1)]
    rw [QueryCache.cacheQuery_self, programCache_parameter]
  · by_cases hs : ∃ position, input = secretInputs seed material.1 position
    · obtain ⟨position, rfl⟩ := hs
      have hinput : secretInputs seed material.1 position =
          hashInputs seed material.1 ⟨firstOf position, isSecond_firstOf position⟩ :=
        (secretInput_firstOf seed material position).symm
      rw [hinput, cacheTable_apply (base.cacheQuery (parameterInput seed) material.1)
        (hashInputs seed material.1) (hashInputs_injective seed material.1) (hashAnswers material.2)]
      rw [← hinput]
      exact (programCache_secret base seed material position).symm
    · have hmiss : ∀ position : HashPosition, input ≠ hashInputs seed material.1 position :=
        fun position heq => hs ⟨position.1, heq⟩
      rw [cacheTable_apply_of_not_mem (base.cacheQuery (parameterInput seed) material.1)
        (hashInputs seed material.1) (hashAnswers material.2) input hmiss,
        QueryCache.cacheQuery_of_ne _ _ hp, programCache_other _ _ _ _ hp]
      simpa only [not_exists, secretInput, parameter, secretInputs] using hs

/-- Explicitly query the parameter first and then every derivation hash at that parameter. -/
noncomputable def prepareMaterial (seed : MasterSeed) : OracleComp HashSpec (HashOutput × HashOutputs) := do
  let parameterOutput ← liftM (HashSpec.query (parameterInput seed))
  let outputs ← queryTable (hashInputs seed parameterOutput)
  return (parameterOutput, outputs)

attribute [local irreducible] cacheTable cacheFin programCache

/-- Exact distribution of the oracle cache after preparation: the programmed cache of independently
sampled material. No assertion about an arbitrary preexisting honest cache is needed: preparation
starts empty. -/
theorem evalDist_prepareMaterial (seed : MasterSeed) :
    𝒟[Prod.snd <$> (simulateQ randomOracle (prepareMaterial seed)).run ∅] =
      𝒟[(fun material => programCache ∅ seed material) <$> sampleMaterial] := by
  unfold prepareMaterial
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [QueryImpl.withCaching_run_none _ (by rfl)]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp,
    sampleMaterial, map_bind]
  apply evalDist_bind_congr'
  intro parameterOutput
  have hfresh : ∀ position, ((∅ : QueryCache HashSpec).cacheQuery
      (parameterInput seed) parameterOutput) (hashInputs seed parameterOutput position) = none := by
    intro position
    rw [hashInputs,
      QueryCache.cacheQuery_of_ne _ _ (secretInputs_ne_parameter seed parameterOutput position.1)]
    rfl
  have htable := evalDist_queryTable_fresh (R := HashOutput)
    (hashInputs seed parameterOutput) (hashInputs_injective seed parameterOutput)
    ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput) hfresh
  have hcache : (fun outputs : SecretOutputs => programCache ∅ seed (parameterOutput, outputs)) =
      (fun answers : HashOutputs => cacheTable ((∅ : QueryCache HashSpec).cacheQuery
        (parameterInput seed) parameterOutput) (hashInputs seed parameterOutput) answers) ∘ hashAnswers := by
    funext outputs
    exact (cacheTable_eq_programCache (∅ : QueryCache HashSpec) seed (parameterOutput, outputs)).symm
  rw [Functor.map_map, evalDist_map, htable, ← evalDist_map, Functor.map_map, Functor.map_map]
  change 𝒟[(fun answers : HashOutputs => cacheTable ((∅ : QueryCache HashSpec).cacheQuery
      (parameterInput seed) parameterOutput) (hashInputs seed parameterOutput) answers) <$>
        ($ᵗ HashOutputs)] =
    𝒟[(fun outputs : SecretOutputs => programCache ∅ seed (parameterOutput, outputs)) <$>
      ($ᵗ SecretOutputs)]
  rw [hcache]
  exact (evalDist_map_hashAnswers _).symm

theorem run'_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM (OracleWorld.query input) >>= next)).run' cache =
      ((romImpl input).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

theorem cacheQuery_comm (cache : QueryCache HashSpec) (left right : HashInput)
    (h : left ≠ right) (a b : HashOutput) :
    (cache.cacheQuery left a).cacheQuery right b = (cache.cacheQuery right b).cacheQuery left a := by
  funext input
  by_cases hl : input = left
  · subst input
    simp [QueryCache.cacheQuery_of_ne, h]
  · by_cases hr : input = right
    · subst input
      simp [QueryCache.cacheQuery_of_ne, hl]
    · simp [QueryCache.cacheQuery_of_ne, hl, hr]

/-- An unobserved query may be sampled early, whether or not the computation later uses it. -/
theorem evalDist_presample_fresh {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput) (hfresh : cache target = none) :
    𝒟[(simulateQ romImpl computation).run' cache] = 𝒟[do
      let output ← $ᵗ HashOutput
      (simulateQ romImpl computation).run' (cache.cacheQuery target output)] := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      apply evalDist_ext
      intro result
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inl input)) >>= next)).run' cache =
                ((liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                  (simulateQ romImpl (next answer)).run' cache) := by
            rw [run'_query_bind]
            change (((fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _)) >>= _) = _
            exact bind_map_left (m := ProbComp) (fun answer => (answer, cache))
              (liftM (unifSpec.query input) : ProbComp _)
              (fun result => (simulateQ romImpl (next result.1)).run' result.2)
          rw [hrun]
          trans 𝒟[do
            let answer ← (liftM (unifSpec.query input) : ProbComp _)
            let output ← $ᵗ HashOutput
            (simulateQ romImpl (next answer)).run' (cache.cacheQuery target output)]
          · exact evalDist_bind_congr' _ (fun answer => ih answer cache hfresh)
          · rw [evalDist_bind_bind_swap]
            apply evalDist_bind_congr'
            intro output
            rw [hrun]
      | inr input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inr input)) >>= next)).run' cache =
                ((randomOracle (spec := HashSpec) input).run cache >>= fun result =>
                  (simulateQ romImpl (next result.1)).run' result.2) := run'_query_bind _ _ _
          by_cases heq : input = target
          · subst target
            rw [hrun, QueryImpl.withCaching_run_none _ hfresh, bind_map_left]
            apply evalDist_bind_congr'
            intro output
            rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
          · have hfresh' (output : HashOutput) : (cache.cacheQuery input output) target = none := by
              rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq), hfresh]
            cases hinput : cache input with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind, ih answer cache hfresh]
                apply evalDist_bind_congr'
                intro output
                rw [hrun, QueryImpl.withCaching_run_some _ (by
                  rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), pure_bind]
            | none =>
                rw [hrun, QueryImpl.withCaching_run_none _ hinput, bind_map_left]
                trans 𝒟[do
                  let answer ← $ᵗ HashOutput
                  let output ← $ᵗ HashOutput
                  (simulateQ romImpl (next answer)).run' ((cache.cacheQuery input answer).cacheQuery target output)]
                · exact evalDist_bind_congr' _ (fun answer => ih answer _ (hfresh' answer))
                · rw [evalDist_bind_bind_swap]
                  apply evalDist_bind_congr'
                  intro output
                  rw [hrun, QueryImpl.withCaching_run_none _ (by
                    rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), bind_map_left]
                  apply evalDist_bind_congr'
                  intro answer
                  rw [cacheQuery_comm cache input target heq]

theorem evalDist_presample_query {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput) :
    𝒟[(simulateQ romImpl computation).run' cache] =
      𝒟[(randomOracle (spec := HashSpec) target).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2] := by
  cases hc : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
      exact evalDist_presample_fresh computation cache target hc
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]

theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl computation).run' cache] =
      𝒟[(simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2] := by
  induction preparation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      trans 𝒟[(romImpl input).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2]
      · cases input with
        | inl input =>
            apply evalDist_ext
            intro value
            simp [romImpl, unifFwdImpl]
        | inr input => exact evalDist_presample_query computation cache input
      · exact evalDist_bind_congr' _ (fun result => ih result.1 result.2)

/-- Every complete continuation has the same output distribution after table preparation.
The seed is fixed in this statement, so the continuation may perform actual seeded keygen,
signing, and verification. Its oracle state still contains the seed-addressed entries. -/
theorem evalDist_prepared_continuation {α : Type} (computation : OracleComp OracleWorld α)
    (seed : MasterSeed) :
    𝒟[(simulateQ romImpl computation).run' ∅] =
      𝒟[sampleMaterial >>= fun material =>
        (simulateQ romImpl computation).run' (programCache ∅ seed material)] := by
  rw [evalDist_presample_computation computation
    (liftM (prepareMaterial seed) : OracleComp OracleWorld (HashOutput × HashOutputs)) ∅,
    simulate_lift_hash]
  trans 𝒟[((fun material => programCache ∅ seed material) <$> sampleMaterial) >>=
    fun cache => (simulateQ romImpl computation).run' cache]
  · rw [← bind_map_left Prod.snd, evalDist_bind, evalDist_prepareMaterial, evalDist_bind]
  · rw [bind_map_left]

/-- Pure instrumentation counts all hash calls, including cached calls, and no private draws. -/
noncomputable def countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  SphincsBase.QueryCap.counted (fun input : OracleWorld.Domain => input matches .inr _) computation

theorem simulateQ_countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ romImpl (countHashQueries computation) = (simulateQ countedOracle computation).run := by
  rw [countHashQueries, SphincsBase.QueryCap.simulate_withCost]
  congr 2
  funext input
  cases input <;> rfl

/-- Uniform hidden seed sampling can be moved after seed-independent material sampling.
The oracle cache in the continuation remains programmed at the sampled seed's addresses. -/
theorem evalDist_seeded_prepared {α : Type} (next : MasterSeed → OracleComp OracleWorld α) :
    𝒟[(simulateQ romImpl ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run' ∅] =
      𝒟[sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)] := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  trans 𝒟[sampleMasterSeed >>= fun seed => sampleMaterial >>= fun material =>
    (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)]
  · apply evalDist_bind_congr'
    intro seed
    exact evalDist_prepared_continuation (next seed) seed
  · exact evalDist_bind_bind_swap _ _ _

theorem countHashQueries_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    countHashQueries (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← countHashQueries (next answer)
      pure (result.1, (if (fun query : OracleWorld.Domain => query matches .inr _) input then 1 else 0) + result.2)) := rfl

theorem countHashQueries_lift_prob {α : Type} (computation : ProbComp α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      rfl

theorem countHashQueries_sampling_bind {α β : Type} (sampling : ProbComp α)
    (next : α → OracleComp OracleWorld β) :
    countHashQueries ((liftM sampling : OracleComp OracleWorld α) >>= next) =
      (liftM sampling : OracleComp OracleWorld α) >>= fun value => countHashQueries (next value) := by
  rw [countHashQueries, SphincsBase.QueryCap.counted_bind]
  change (countHashQueries (liftM sampling : OracleComp OracleWorld α) >>= _) = _
  rw [countHashQueries_lift_prob, bind_map_left]
  simp only [Nat.zero_add, Prod.mk.eta, bind_pure]
  rfl

/-- The seed can be sampled after the material while preserving the counted continuation. -/
theorem evalDist_seeded_prepared_counted {α : Type}
    (next : MasterSeed → OracleComp OracleWorld α) :
    𝒟[(simulateQ countedOracle
      ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run.run' ∅] =
      𝒟[sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ countedOracle (next seed)).run.run' (programCache ∅ seed material)] := by
  rw [← simulateQ_countHashQueries, countHashQueries_sampling_bind]
  simpa only [simulateQ_countHashQueries] using
    evalDist_seeded_prepared (fun seed => countHashQueries (next seed))

variable [Params]

/-- The actual SUF-CMA computation after its master-seed sample; honest algorithms are unchanged. -/
noncomputable def gameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The seeded experiment with independently sampled full-output material programmed first.
The cache is seed-dependent; deriving a seed-independent adversarial view still requires hiding
the programmed addresses until the first explicit seed hit. -/
noncomputable def preparedExperiment (adversary : Adversary) : ProbComp (Bool × Nat) := do
  let material ← sampleMaterial
  let seed ← sampleMasterSeed
  (simulateQ countedOracle (gameAfterSeed adversary seed)).run.run' (programCache ∅ seed material)

end SphincsFors.Security.SeedCoupling
