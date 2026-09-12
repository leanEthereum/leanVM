import SphincsSecurity.Statement
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

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

theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {A B : Type} {n : Nat}
    (f : A → B) (computation : Fin n → m A) :
    Concrete.sequenceFin (fun i => f <$> computation i) =
      (fun values i => f (values i)) <$> Concrete.sequenceFin computation := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, bind_map_left, ih, map_bind, bind_pure_comp, Functor.map_map]
      apply bind_congr
      intro head
      congr 1
      funext tail i
      cases i using Fin.cases <;> rfl

theorem evalDist_sequenceFin_congr {A : Type} {n : Nat}
    (left right : Fin n → ProbComp A) (h : ∀ i, 𝒟[left i] = 𝒟[right i]) :
    𝒟[Concrete.sequenceFin left] = 𝒟[Concrete.sequenceFin right] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Concrete.sequenceFin, bind_pure_comp, evalDist_bind]
      rw [h 0]
      congr 1
      funext head
      rw [evalDist_map, evalDist_map, ih _ _ (fun i => h i.succ)]

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

end SphincsSecurity.Seeded
