import Sphincs.SecuritySeedModel
import Sphincs.World
import Sphincs.Statement
import SphincsBase.Proof.Base.QueryCap
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-! Finite fresh-table preparation and the candidate's parameter-dependent derivation table.
The generic finite-table proof is adapted from leanVM b7a107256. Preparation explicitly performs
oracle queries; later theorems relate it to independent full-output material and its programmed
cache. Preparation is not silently counted as part of an adversary's existing query budget. -/

open OracleComp OracleSpec

namespace Sphincs.Security.SeedCoupling

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
    (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) =ᵈ ($ᵗ (α × β)) := by
  refine EvalDistEq.of_forall_prEvent_eq fun p => ?_
  rw [SampleableType.prEvent_uniformSample_inst_irrel _ (instSampleableTypeProd α β) p,
    SampleableType.prEvent_uniformSample_prod]
  simp only [prEvent_norm]

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
    (Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)) =ᵈ ($ᵗ (Fin n → R)) := by
  classical
  induction n with
  | zero =>
      refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun values => ?_
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [Concrete.sequenceFin, heq, Subsingleton.elim (default : Fin 0 → R) Fin.elim0, Finset.filter_eq']
  | succ n ih =>
      refine EvalDistEq.trans (my := finHeadTailEquiv R n <$> (do
          let head ← $ᵗ R
          let tail ← $ᵗ (Fin n → R)
          pure (head, tail))) ?_ ?_
      · simp only [Concrete.sequenceFin, map_bind, finHeadTailEquiv,
          Equiv.coe_fn_mk, bind_pure_comp]
        refine EvalDistEq.bind_right _ fun head => ?_
        simpa only [Functor.map_map] using ih.map (fun tail => (Fin.cases head tail : Fin (n + 1) → R))
      refine (evalDist_independent_uniform_pair.map _).trans ?_
      exact SampleableType.map_uniformSample_evalDistEq_of_bijective
        (α := R × (Fin n → R)) (β := Fin (n + 1) → R) (finHeadTailEquiv R n).bijective

end Sphincs.Security.SeedCoupling

namespace Sphincs.Security.SeedCoupling

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
    ((simulateQ randomOracle (queryTable inputs)).run cache) =ᵈ ((fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R))) := by
  classical
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  simp only [bind_pure_comp, Functor.map_map]
  refine ((evalDist_sequenceFin_uniform _).map _).trans ?_
  have htable := SampleableType.map_uniformSample_evalDistEq_of_bijective
    (α := Fin (Fintype.card J) → R) (β := J → R) (finTableEquiv J R).bijective
  refine EvalDistEq.trans ?_ (htable.map _)
  rw [Functor.map_map]
  convert EvalDistEq.refl (_ <$> ($ᵗ (Fin (Fintype.card J) → R))) using 2
  funext outputs
  simp only [cacheTable, Equiv.symm_apply_apply]

end Sphincs.Security.SeedCoupling

namespace Sphincs.Security.SeedCoupling
open SeedModel Completeness

set_option backward.isDefEq.respectTransparency false

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- Uniform tables of derivation answers. -/
@[reducible] noncomputable def derivedOutputsSampleableType : SampleableType DerivedOutputs :=
  SampleableType.ofFintype DerivedOutputs

noncomputable local instance : SampleableType DerivedOutputs := derivedOutputsSampleableType

/-! ### Uniform material gives uniform derivation answers

The answer of a derivation is made of the first halves of the material at its two chain starts (or is
the material at a surrogate), and distinct derivations read distinct positions. Each table of answers
therefore comes from the same number of materials: one free second half per chain start. -/

/-- A map all of whose fibres have one size sends the uniform distribution to the uniform
distribution. -/
theorem evalDist_map_uniform_of_fiber {A B : Type} [Fintype A] [Nonempty A] [Fintype B]
    [DecidableEq B] [SampleableType A] [SampleableType B] (g : A → B) (k : ℕ)
    (hk : ∀ b, (Finset.univ.filter fun a => g a = b).card = k) :
    (g <$> ($ᵗ A : ProbComp A)) =ᵈ ($ᵗ B : ProbComp B) := by
  have hcard : Fintype.card A = Fintype.card B * k := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g) (s := Finset.univ) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)
    rw [Finset.card_univ] at h
    rw [h]
    simp only [hk, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hk0 : k ≠ 0 := by
    intro h0
    have hpos : 0 < Fintype.card A := Fintype.card_pos
    rw [hcard, h0, Nat.mul_zero] at hpos
    exact lt_irrefl 0 hpos
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun b => ?_
  rw [prEvent_map, SampleableType.prEvent_uniformSample, hk,
    SampleableType.prEvent_uniformSample_eq_singleton, hcard, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hk0) (ENNReal.natCast_ne_top _), mul_one]

/-- The hash outputs with a given first half: one per second half. The count is the same for every
first half. (It is kept as a variable below: a closed count such as `2^128` as the cardinality of a
type must never be evaluated.) -/
theorem card_filter_truncateHash (value : Digest)
    [DecidablePred fun output : HashOutput => truncateHash output = value] :
    (Finset.univ.filter fun output : HashOutput => truncateHash output = value).card =
      (Finset.univ : Finset Digest).card := by
  have h : (Finset.univ.filter fun output : HashOutput => truncateHash output = value) =
      (Finset.univ : Finset Digest).map
        ⟨joinHalves value, fun left right heq => by
          have := congrArg upperHash heq
          rwa [upperHash_joinHalves, upperHash_joinHalves] at this⟩ := by
    ext output
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl
      exact ⟨upperHash output, joinHalves_halves output⟩
    · rintro ⟨high, rfl⟩
      exact truncateHash_joinHalves value high
  rw [h, Finset.card_map]

/-- The number of values a table of answers allows at one secret position, with `count` hash
outputs per first half. -/
def fiberSize (count : ℕ) : SecretPosition → ℕ
  | .inl _ => count
  | .inr (.inl _) => count
  | .inr (.inr _) => 1

instance compatibleDecidable (table : DerivedOutputs) (position : SecretPosition) (value : HashOutput) :
    Decidable (Compatible table position value) :=
  match position with
  | .inl p => inferInstanceAs
      (Decidable (truncateHash value = secretHalf (.inl p) (table (secretDerivation (.inl p)))))
  | .inr (.inl p) => inferInstanceAs
      (Decidable (truncateHash value = secretHalf (.inr (.inl p)) (table (secretDerivation (.inr (.inl p))))))
  | .inr (.inr level) => inferInstanceAs (Decidable (value = table (.inr (.inr level))))

theorem card_compatible (count : ℕ)
    (hcount : ∀ value : Digest,
      (Finset.univ.filter fun output : HashOutput => truncateHash output = value).card = count)
    (table : DerivedOutputs) (position : SecretPosition) :
    (Finset.univ.filter fun value : HashOutput => Compatible table position value).card =
      fiberSize count position := by
  cases position with
  | inl p =>
      simp only [fiberSize]
      rw [← hcount (secretHalf (.inl p) (table (secretDerivation (.inl p))))]
      exact congrArg Finset.card (Finset.filter_congr fun value _ => Iff.rfl)
  | inr p =>
      cases p with
      | inl p =>
          simp only [fiberSize]
          rw [← hcount (secretHalf (.inr (.inl p)) (table (secretDerivation (.inr (.inl p)))))]
          exact congrArg Finset.card (Finset.filter_congr fun value _ => Iff.rfl)
      | inr level =>
          simp only [fiberSize]
          rw [Finset.card_eq_one]
          refine ⟨table (.inr (.inr level)), ?_⟩
          ext value
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact Iff.rfl

/-- Every table of answers comes from the same number of materials. -/
theorem card_fiber_derivedOutput (count : ℕ)
    (hcount : ∀ value : Digest,
      (Finset.univ.filter fun output : HashOutput => truncateHash output = value).card = count)
    (table : DerivedOutputs)
    [DecidablePred fun outputs : SecretOutputs => derivedOutput outputs = table] :
    (Finset.univ.filter fun outputs : SecretOutputs => derivedOutput outputs = table).card =
      ∏ position, fiberSize count position := by
  have h : (Finset.univ.filter fun outputs : SecretOutputs => derivedOutput outputs = table) =
      Fintype.piFinset (fun position => Finset.univ.filter fun value => Compatible table position value) := by
    ext outputs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      derivedOutput_eq_iff]
  rw [h, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun position _ => card_compatible count hcount table position

/-- **The secrets are still independent and uniform.** The answers of the derivations, read off
uniform material, are a uniform table: one uniform 256-bit answer per derivation. Conversely, the
two halves of an answer are the secrets of its pair of chains, so uniform independent answers of
distinct derivations give independent uniform secrets. -/
theorem evalDist_derivedOutput_uniform :
    (derivedOutput <$> ($ᵗ SecretOutputs : ProbComp SecretOutputs)) =ᵈ ($ᵗ DerivedOutputs : ProbComp DerivedOutputs) := by
  obtain ⟨count, hcount⟩ : ∃ count : ℕ, ∀ value : Digest,
      (Finset.univ.filter fun output : HashOutput => truncateHash output = value).card = count :=
    ⟨_, fun value => card_filter_truncateHash value⟩
  exact evalDist_map_uniform_of_fiber derivedOutput _
    (fun table => card_fiber_derivedOutput count hcount table)

/-- After the parameter response, all remaining addresses are fixed independently of their
own answers: one address per derivation. The complete 256-bit responses are stored. -/
def derivationInputs (seed : MasterSeed) (parameterOutput : HashOutput)
    (derivation : Derivation) : HashInput :=
  keygenHashInput (truncateHash parameterOutput) (derivationDomain derivation) seed

theorem derivationInputs_injective (seed : MasterSeed) (parameterOutput : HashOutput) :
    Function.Injective (derivationInputs seed parameterOutput) := by
  intro left right h
  exact derivationDomain_injective (keygenInput_injective h).2.1

theorem derivationInputs_ne_parameter (seed : MasterSeed) (parameterOutput : HashOutput)
    (derivation : Derivation) : derivationInputs seed parameterOutput derivation ≠ parameterInput seed := by
  intro h
  exact derivationDomain_ne_parameter derivation (keygenInput_injective h).2.1

/-- The sequential finite-cache construction implements exactly the candidate programming map. -/
theorem cacheTable_eq_programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    cacheTable (base.cacheQuery (parameterInput seed) material.1)
      (derivationInputs seed material.1) (derivedOutput material.2) = programCache base seed material := by
  classical
  refine QueryCache.ext fun input => ?_
  by_cases hp : input = parameterInput seed
  · subst input
    rw [cacheTable_apply_of_not_mem _ _ _ _
      (fun derivation => (derivationInputs_ne_parameter seed material.1 derivation).symm)]
    rw [QueryCache.cacheQuery_self, programCache_parameter]
  · by_cases hs : ∃ derivation, input = derivationInputs seed material.1 derivation
    · obtain ⟨derivation, rfl⟩ := hs
      rw [cacheTable_apply _ _ (derivationInputs_injective seed material.1)]
      exact (programCache_derivation base seed material derivation).symm
    · rw [cacheTable_apply_of_not_mem _ _ _ _ (by simpa only [not_exists] using hs),
        QueryCache.cacheQuery_of_ne _ _ hp, programCache_other _ _ _ _ hp]
      intro position heq
      exact hs ⟨secretDerivation position, heq⟩

/-- Explicitly query the parameter first and then every derivation at that parameter. -/
noncomputable def prepareTable (seed : MasterSeed) : OracleComp HashSpec (HashOutput × DerivedOutputs) := do
  let parameterOutput ← liftM (HashSpec.query (parameterInput seed))
  let outputs ← queryTable (derivationInputs seed parameterOutput)
  return (parameterOutput, outputs)

attribute [local irreducible] cacheTable cacheFin programCache

/-- Exact joint distribution of the queried table and the cache: the answers of the derivations of
independently sampled material and its full programmed cache.
No assertion about an arbitrary preexisting honest cache is needed: preparation starts empty. -/
theorem evalDist_prepareTable (seed : MasterSeed) :
    ((simulateQ randomOracle (prepareTable seed)).run ∅) =ᵈ ((fun material => ((material.1, derivedOutput material.2), programCache ∅ seed material)) <$>
        sampleMaterial) := by
  unfold prepareTable
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [QueryImpl.withCaching_run_none _ (by rfl)]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp,
    sampleMaterial, map_bind]
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  have hfresh : ∀ derivation, ((∅ : QueryCache HashSpec).cacheQuery
      (parameterInput seed) parameterOutput) (derivationInputs seed parameterOutput derivation) = none := by
    intro derivation
    rw [QueryCache.cacheQuery_of_ne _ _ (derivationInputs_ne_parameter seed parameterOutput derivation)]
    rfl
  have htable := evalDist_queryTable_fresh (R := HashOutput)
    (derivationInputs seed parameterOutput) (derivationInputs_injective seed parameterOutput)
    ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput) hfresh
  refine (htable.map _).trans ?_
  refine ((evalDist_derivedOutput_uniform.symm.map _).map _).trans ?_
  simp only [Functor.map_map]
  convert EvalDistEq.refl (_ <$> ($ᵗ SecretOutputs)) using 2
  funext outputs
  exact congrArg (fun cache : QueryCache HashSpec => ((parameterOutput, derivedOutput outputs), cache))
    (cacheTable_eq_programCache (∅ : QueryCache HashSpec) seed (parameterOutput, outputs)).symm

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
  refine QueryCache.ext fun input => ?_
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
    ((simulateQ romImpl computation).run' cache) =ᵈ (do
      let output ← $ᵗ HashOutput
      (simulateQ romImpl computation).run' (cache.cacheQuery target output)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
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
          refine EvalDistEq.trans (my := do
            let answer ← (liftM (unifSpec.query input) : ProbComp _)
            let output ← $ᵗ HashOutput
            (simulateQ romImpl (next answer)).run' (cache.cacheQuery target output)) ?_ ?_
          · exact EvalDistEq.bind_right _ (fun answer => ih answer cache hfresh)
          · refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
              (EvalDistEq.bind_right _ fun output => ?_)
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
            refine EvalDistEq.bind_right _ fun output => ?_
            rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
          · have hfresh' (output : HashOutput) : (cache.cacheQuery input output) target = none := by
              rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq), hfresh]
            cases hinput : cache input with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
                refine (ih answer cache hfresh).trans (EvalDistEq.bind_right _ fun output => ?_)
                rw [hrun, QueryImpl.withCaching_run_some _ (by
                  rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), pure_bind]
            | none =>
                rw [hrun, QueryImpl.withCaching_run_none _ hinput, bind_map_left]
                refine EvalDistEq.trans (my := do
                  let answer ← $ᵗ HashOutput
                  let output ← $ᵗ HashOutput
                  (simulateQ romImpl (next answer)).run' ((cache.cacheQuery input answer).cacheQuery target output))
                  ?_ ?_
                · exact EvalDistEq.bind_right _ (fun answer => ih answer _ (hfresh' answer))
                · refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans
                    (EvalDistEq.bind_right _ fun output => ?_)
                  rw [hrun, QueryImpl.withCaching_run_none _ (by
                    rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), bind_map_left]
                  refine EvalDistEq.bind_right _ fun answer => ?_
                  rw [cacheQuery_comm cache input target heq]

theorem evalDist_presample_query {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput) :
    ((simulateQ romImpl computation).run' cache) =ᵈ ((randomOracle (spec := HashSpec) target).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) := by
  cases hc : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
      exact evalDist_presample_fresh computation cache target hc
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]

theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    ((simulateQ romImpl computation).run' cache) =ᵈ ((simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) := by
  induction preparation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine EvalDistEq.trans (my := (romImpl input).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) ?_ ?_
      · cases input with
        | inl input =>
            have hstep : (romImpl (Sum.inl input)).run cache =
                (fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _) := rfl
            rw [hstep, bind_map_left]
            exact (OracleComp.EvalDistEq.bind_const _ _).symm
        | inr input => exact evalDist_presample_query computation cache input
      · exact EvalDistEq.bind_right _ (fun result => ih result.1 result.2)

/-- Every complete continuation has the same output distribution after table preparation.
The seed is fixed in this statement, so the continuation may perform actual seeded keygen,
signing, and verification. Its oracle state still contains the seed-addressed entries. -/
theorem evalDist_prepared_continuation {α : Type} (computation : OracleComp OracleWorld α)
    (seed : MasterSeed) :
    ((simulateQ romImpl computation).run' ∅) =ᵈ (sampleMaterial >>= fun material =>
        (simulateQ romImpl computation).run' (programCache ∅ seed material)) := by
  refine (evalDist_presample_computation computation
    (liftM (prepareTable seed) : OracleComp OracleWorld (HashOutput × DerivedOutputs)) ∅).trans ?_
  rw [simulate_lift_hash]
  refine EvalDistEq.trans (my := ((fun material => ((material.1, derivedOutput material.2),
      programCache ∅ seed material)) <$> sampleMaterial) >>= fun result =>
        (simulateQ romImpl computation).run' result.2) ?_ ?_
  · exact (evalDist_prepareTable seed).bind_left _
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
    ((simulateQ romImpl ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run' ∅) =ᵈ (sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  refine EvalDistEq.trans (my := sampleMasterSeed >>= fun seed => sampleMaterial >>= fun material =>
    (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)) ?_ ?_
  · exact EvalDistEq.bind_right _ fun seed => evalDist_prepared_continuation (next seed) seed
  · exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

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
    ((simulateQ countedOracle
      ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run.run' ∅) =ᵈ (sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ countedOracle (next seed)).run.run' (programCache ∅ seed material)) := by
  rw [← simulateQ_countHashQueries, countHashQueries_sampling_bind]
  simpa only [simulateQ_countHashQueries] using
    evalDist_seeded_prepared (fun seed => countHashQueries (next seed))

variable [Params]

/-- The actual SUF-CMA computation after its master-seed sample; honest algorithms are unchanged. -/
noncomputable def gameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← liftM (Seeded.keygenFromMaster seed)
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

end Sphincs.Security.SeedCoupling
