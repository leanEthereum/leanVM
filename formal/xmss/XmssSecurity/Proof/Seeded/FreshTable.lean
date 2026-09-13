import XmssSecurity.Statement
import XmssSecurity.Proof.UniformFiniteTable

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

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

def cacheRows : {rows cols : Nat} → QueryCache (D →ₒ R) → (Fin rows → Fin cols → D) →
    (Fin rows → Fin cols → R) → QueryCache (D →ₒ R)
  | 0, _, cache, _, _ => cache
  | _ + 1, _, cache, inputs, outputs =>
      cacheRows (cacheFin cache (inputs 0) (outputs 0))
        (fun i => inputs i.succ) (fun i => outputs i.succ)

omit [SampleableType R] in
theorem cacheRows_apply_of_not_mem {rows cols : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin rows → Fin cols → D) (outputs : Fin rows → Fin cols → R) (input : D)
    (hinput : ∀ i j, input ≠ inputs i j) : cacheRows cache inputs outputs input = cache input := by
  induction rows generalizing cache with
  | zero => rfl
  | succ rows ih =>
      rw [cacheRows, ih _ _ _ (fun i j => hinput i.succ j)]
      exact cacheFin_apply_of_not_mem _ _ _ _ (hinput 0)

/-- The row-major version used by the epoch and chain loops in XMSS key generation. -/
theorem run_sequenceFin_rows_fresh {rows cols : Nat} (inputs : Fin rows → Fin cols → D)
    (hinj : ∀ i j i' j', inputs i j = inputs i' j' → i = i' ∧ j = j')
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ i j, cache (inputs i j) = none) :
    (simulateQ randomOracle (Concrete.sequenceFin fun i => Concrete.sequenceFin fun j =>
      (liftM ((D →ₒ R).query (inputs i j)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← Concrete.sequenceFin fun _ : Fin rows =>
          Concrete.sequenceFin fun _ : Fin cols => ($ᵗ R : ProbComp R)
        pure (outputs, cacheRows cache inputs outputs)) := by
  induction rows generalizing cache with
  | zero => simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, pure_bind, cacheRows]
  | succ rows ih =>
      simp only [Concrete.sequenceFin]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rw [run_sequenceFin_fresh (inputs 0) (fun _ _ h => (hinj 0 _ 0 _ h).2) cache (hfresh 0)]
      simp only [bind_pure_comp, bind_map_left, map_bind]
      apply bind_congr
      intro head
      have htail : ∀ i : Fin rows, ∀ j : Fin cols,
          cacheFin cache (inputs 0) head (inputs i.succ j) = none := by
        intro i j
        rw [cacheFin_apply_of_not_mem]
        · exact hfresh i.succ j
        · intro k h
          exact Fin.succ_ne_zero i (hinj i.succ j 0 k h).1
      rw [ih (fun i => inputs i.succ)
        (fun i j i' j' h => ⟨Fin.succ_injective _ (hinj i.succ j i'.succ j' h).1,
          (hinj i.succ j i'.succ j' h).2⟩) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheRows]
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

end XmssSecurity.Seeded
