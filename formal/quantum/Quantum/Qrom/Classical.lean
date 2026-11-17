module

public import Quantum.Classical
public import Quantum.Qrom.Model

@[expose] public section

/-!
# The QROM on classical programs is the classical random-oracle model, with coins

VCVio's `Quantum.qromEvalDist₂_toQuantum_eq_randomOracle` covers classical algorithms whose only
randomness is the oracle. The schemes also sample coins, so this file proves the two facts for
algorithms over `unifSpec + (X →ₒ Y)` (at `X = HashDomain`, `Y = HashOutput`: `RomOracles`).

* **Lazy sampling is uniform sampling.** Run from a cache `c`, the lazily sampled random function
  (`lazyFunOracles`) gives every output the average, over all functions `H : X → Y`, of its
  probability when the queries are answered by `H` overlaid with `c` (`eagerFunOracles`,
  `card_mul_prEvent_lazyFun`): a fresh answer is uniform on all of `Y`, and resampling one value
  of a uniform function covers every function `|Y|` times (`sum_sum_update_eq_card_smul`). From
  the empty cache: `prEvent_lazyFun_eq`, `evalDist_lazyFun_eq`.
* **Classical calls of the QROM are classical queries.** The classical calls `funImpl B` (coins,
  then basis calls of the port at `(x, 0)`, reading the response, as `SufCma.romImpl` makes them)
  run against `additiveOracleRuntime H` as the queries answered by `H` (`classicalOn_funImpl`).
  So a program that runs classically against every `H` has in the QROM the distribution of its
  classical algorithm under the lazily sampled random function (`qromEvalDistMap_of_classicalOn`),
  in particular every classical algorithm run by classical calls
  (`qromEvalDistMap_toQuantumAt_funImpl`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal Kronecker

namespace Quantum.Qrom

/-! ## Lazy and eager sampling of a function -/

section LazyEager

variable {X Y : Type}

/-- The model's oracles answered by a fixed function `H`: coins forwarded, `H x` at `x`. -/
noncomputable def eagerFunOracles (H : X → Y) : QueryImpl (unifSpec + (X →ₒ Y)) ProbComp
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr x => pure (H x)

variable [Fintype X] [DecidableEq X] [Fintype Y]

/-- **Resampling one value.** Summing over a function and a fresh value `u` at `x` of a term that
also sees `u` counts every function `|Y|` times, with `u` its value at `x`. -/
theorem sum_sum_update_eq_card_smul {β : Type*} [AddCommMonoid β] (x : X)
    (g : (X → Y) → Y → β) :
    ∑ u : Y, ∑ H : X → Y, g (Function.update H x u) u =
      Fintype.card Y • ∑ H : X → Y, g H (H x) := by
  let φ : Y × (X → Y) → Y × (X → Y) := fun p ↦ (p.2 x, Function.update p.2 x p.1)
  have hφ : Function.Involutive φ := fun p ↦ by
    simp only [φ, Function.update_idem, Function.update_eq_self, Function.update_self]
  rw [← Fintype.sum_prod_type' (fun u H ↦ g (Function.update H x u) u),
    Fintype.sum_equiv hφ.toPerm (fun p ↦ g (Function.update p.2 x p.1) p.1)
      (fun p ↦ g p.2 (p.2 x)) (fun p ↦ by simp [φ]), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]

variable [SampleableType Y]

omit [Fintype X] [Fintype Y] in
/-- A computation over the coins alone, run against the model's oracles, leaves the cache as it
is. -/
theorem run_simulateQ_lazyFunOracles_liftM {α : Type} (p : ProbComp α)
    (c : (X →ₒ Y).QueryCache) :
    (simulateQ (lazyFunOracles X Y) (liftM p : OracleComp (unifSpec + (X →ₒ Y)) α)).run c =
      (·, c) <$> p := by
  rw [← liftComp_eq_liftM]
  induction p using OracleComp.inductionOn generalizing c with
  | pure a => simp
  | query_bind n k ih =>
    have hq : simulateQ (lazyFunOracles X Y) (liftComp (liftM (unifSpec.query n) : ProbComp _)
        (unifSpec + (X →ₒ Y))) =
          (liftM (unifSpec.query n) : StateT (X →ₒ Y).QueryCache ProbComp (Fin (n + 1))) := by
      rw [liftComp_liftM_query, OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query,
        simulateQ_spec_query]
      rfl
    rw [liftComp_bind, simulateQ_bind, hq, StateT.run_bind]
    simp only [ih]
    rfl

/-- **Lazy sampling from a cache is uniform overlaid sampling.** Run from the cache `c`, the
lazily sampled random function gives every output a probability whose `|X → Y|` multiple is the
sum, over all functions `H`, of its probability against `H` overlaid with `c`. -/
theorem card_mul_prEvent_lazyFun {α : Type} (oa : OracleComp (unifSpec + (X →ₒ Y)) α)
    (c : (X →ₒ Y).QueryCache) (a : α) :
    (Fintype.card (X → Y) : ℝ≥0∞) *
        Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run' c}[z = a] =
      ∑ H : X → Y, Pr{let z ← simulateQ (eagerFunOracles (tableExtending c H)) oa}[z = a] := by
  classical
  induction oa using OracleComp.inductionOn generalizing c with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  | query_bind t k ih =>
    have hlazy : (simulateQ (lazyFunOracles X Y)
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k)).run' c =
          (lazyFunOracles X Y t).run c >>= fun p ↦
            (simulateQ (lazyFunOracles X Y) (k p.1)).run' p.2 := by
      simp [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    have heager (H : X → Y) :
        simulateQ (eagerFunOracles H) (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k) =
          eagerFunOracles H t >>= fun u ↦ simulateQ (eagerFunOracles H) (k u) := by
      simp [simulateQ_bind]
    change _ * Pr{let z ← (simulateQ (lazyFunOracles X Y)
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k)).run' c}[z = a] =
      ∑ H, Pr{let z ← (simulateQ (eagerFunOracles (tableExtending c H))
        (liftM ((unifSpec + (X →ₒ Y)).query t) >>= k))}[z = a]
    simp only [hlazy, heager]
    rcases t with n | x
    · have hrun : (lazyFunOracles X Y (.inl n)).run c =
          ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u ↦ pure (u, c)) := rfl
      have he (H : X → Y) : eagerFunOracles H (.inl n) =
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl
      simp only [hrun, he, bind_assoc, pure_bind, prEvent_bind_eq_sum_fintype]
      rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [mul_left_comm, ih u c, Finset.mul_sum]
      rfl
    · cases hc : c x with
      | some y =>
        have hrun : (lazyFunOracles X Y (.inr x)).run c = pure (y, c) := by
          rw [lazyFunOracles, randomOracle.run_eq, hc]
        have he (H : X → Y) : eagerFunOracles (tableExtending c H) (.inr x) = pure y := by
          simp [eagerFunOracles, tableExtending, hc]
        simp only [hrun, he, pure_bind]
        exact ih y c
      | none =>
        have hrun : (lazyFunOracles X Y (.inr x)).run c =
            ($ᵗ Y) >>= fun u ↦ pure (u, c.cacheQuery x u) := by
          rw [lazyFunOracles, randomOracle.run_eq, hc]
        have he (H : X → Y) : eagerFunOracles (tableExtending c H) (.inr x) = pure (H x) := by
          simp [eagerFunOracles, tableExtending, hc]
        simp only [hrun, he, bind_assoc, pure_bind]
        rw [prEvent_bind_eq_sum_fintype, Finset.mul_sum]
        have hY : (Fintype.card Y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        calc
          _ = ∑ u : Y, (Fintype.card Y : ℝ≥0∞)⁻¹ * ∑ H : X → Y,
              Pr{let z ← (simulateQ (eagerFunOracles (tableExtending c (Function.update H x u)))
                (k u))}[z = a] := by
            refine Finset.sum_congr rfl fun u _ ↦ ?_
            rw [SampleableType.prEvent_uniformSample_eq_singleton, mul_left_comm,
              ih u (c.cacheQuery x u)]
            refine congrArg _ (Finset.sum_congr rfl fun H _ ↦ ?_)
            rw [tableExtending_cacheQuery, tableExtending_update_of_none c H hc]
          _ = _ := by
            rw [← Finset.mul_sum, sum_sum_update_eq_card_smul x fun H u ↦
                Pr{let z ← simulateQ (eagerFunOracles (tableExtending c H)) (k u)}[z = a],
              nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hY (ENNReal.natCast_ne_top _),
              one_mul]

/-- **Lazy sampling is uniform sampling.** The lazily sampled random function, run from the empty
cache, gives every output the average, over all functions `H : X → Y`, of its probability when the
queries are answered by `H`. -/
theorem prEvent_lazyFun_eq {α : Type} (oa : OracleComp (unifSpec + (X →ₒ Y)) α) (a : α) :
    Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run' ∅}[z = a] =
      (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ *
        ∑ H : X → Y, Pr{let z ← simulateQ (eagerFunOracles H) oa}[z = a] := by
  have h := card_mul_prEvent_lazyFun oa ∅ a
  simp only [tableExtending_empty] at h
  rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _), one_mul]

/-- **Lazy sampling is uniform sampling**, as output measures: the run of the lazily sampled
random function from the empty cache is the uniform mixture of the runs against fixed
functions. -/
theorem evalDist_lazyFun_eq {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    𝒟[(simulateQ (lazyFunOracles X Y) oa).run' ∅] =
      (Fintype.card (X → Y) : ℝ≥0∞)⁻¹ • ∑ H : X → Y, 𝒟[simulateQ (eagerFunOracles H) oa] := by
  classical
  ext s hs
  have hP (m : ProbComp α) :
      𝒟[m] s = ∑' x, if x ∈ s then Pr{let z ← m}[z = x] else 0 := by
    rw [← prEvent_eq_tsum_ite, prEvent_eq_evalDist m (· ∈ s) hs.mem, Set.ofPred_mem_eq]
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp only [hP, prEvent_lazyFun_eq]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a ↦ ?_
  split_ifs <;> simp

end LazyEager

/-! ## Classical calls of the QROM -/

section Runtime

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- The oracle of `H` as an emulated oracle: its oracle unitary, beside the trivial private
register. -/
noncomputable def funEmulated (H : X → Y) : EmulatedOracle Unit fun _ ↦ QReg.of (X × Y) where
  S := QReg.of Unit
  init := SubState.basis ()
  U _ := oracleUnitary H ⊗ₖ (1 : Matrix Unit Unit ℂ)
  unitary _ := Matrix.kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup _) (one_mem _)

/-- The runtime of the oracle of `H` is the runtime of its emulated oracle. -/
theorem additiveOracleRuntime_eq_toRuntime (H : X → Y) :
    additiveOracleRuntime H = (funEmulated H).toRuntime := by
  refine congrArg (QuantumRuntime.mk _ _) (funext fun p ↦ DSubInstrument.ext <| funext fun r ↦ ?_)
  rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply, MatrixMap.amplify_conj]
  rfl

/-- **A basis call of the QROM against a fixed function**: from the basis input `a`, the call
reads `(a.1, a.2 + H a.1)` with certainty and leaves the held register untouched. -/
theorem branch_run₂_callBasis_additiveOracleRuntime (H : X → Y) (B : QReg) (a : X × Y)
    {β : Type} [DecidableEq β] (read : X × Y → Unit → β) (c : β) :
    ((additiveOracleRuntime H).run₂ .instruments
        (QComp.callBasis (spec := qromSpec X Y) () B a read)).branch c =
      if read (a.1, a.2 + H a.1) () = c then LinearMap.id else 0 := by
  rw [additiveOracleRuntime_eq_toRuntime]
  refine ((funEmulated H).branch_run₂_callBasis () B a read c).trans ?_
  have hblock (o : X × Y) : (funEmulated H).block () o a =
      if o = (a.1, a.2 + H a.1) then 1 else 0 := by
    ext d d'
    obtain ⟨⟩ := d
    obtain ⟨⟩ := d'
    change oracleUnitary H o a * (1 : Matrix Unit Unit ℂ) () () = _
    rw [oracleUnitary_apply, Matrix.one_apply_eq, mul_one]
    split_ifs <;> rfl
  simp only [hblock]
  rw [Finset.sum_eq_single (a.1, a.2 + H a.1)]
  · simp [MatrixMap.conj_one]
  · intro o _ ho
    simp [ho, MatrixMap.conj_zero]
  · simp

/-- **The model's oracles by classical calls of the QROM** beside a held register `B`: coins by
uniform coins, `H x` by a basis call of the port at `(x, 0)`, reading the response. At
`X = HashDomain`, `Y = HashOutput` it is `SufCma.romImpl`. -/
noncomputable def funImpl (B : QReg) :
    QueryImpl (unifSpec + (X →ₒ Y)) (QComp (qromSpec X Y) B B)
  | .inl n => QComp.coinImpl (qromSpec X Y) B n
  | .inr x => QComp.callBasis (spec := qromSpec X Y) () B ((x, 0) : X × Y)
      fun o _ ↦ (o : X × Y).2

/-- Against the oracle of `H`, each classical call branches as `H` answers it. -/
theorem classicalOn_funImpl (B : QReg) (H : X → Y) (t : (unifSpec + (X →ₒ Y)).Domain) :
    ClassicalOn (additiveOracleRuntime H) (funImpl B t) (eagerFunOracles H t) LinearMap.id := by
  classical
  intro y
  rcases t with n | x
  · have hp : Pr{let z ← eagerFunOracles H (.inl n)}[z = y] =
        (Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹ := by
      change Pr{let z ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))}[z = y] = _
      simpa [Finset.filter_eq'] using
        (prEvent_liftM_query_eq_card_div (spec := unifSpec) n (fun x ↦ x = y))
    rw [hp, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    change ((additiveOracleRuntime H).run₂ .instruments
      (QComp.coinImpl (qromSpec X Y) B n)).branch y = _
    rw [QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
      DSubInstrument.branch_frame_apply]
    refine LinearMap.ext fun ρ ↦ ?_
    ext x x'
    simp [SubInstrument.branch_uniform_apply]
  · change ((additiveOracleRuntime H).run₂ .instruments (QComp.callBasis (spec := qromSpec X Y)
      () B ((x, 0) : X × Y) fun o _ ↦ (o : X × Y).2)).branch y = _
    rw [branch_run₂_callBasis_additiveOracleRuntime]
    simp only [eagerFunOracles, prEvent_pure, zero_add]
    split_ifs <;> simp

/-- Against the oracle of `H`, a classical algorithm run by classical calls runs as the
algorithm with its queries answered by `H`. -/
theorem classicalOn_toQuantumAt_funImpl (B : QReg) (H : X → Y) {α : Type}
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) :
    ClassicalOn (additiveOracleRuntime H) (oa.toQuantumAt (funImpl B))
      (simulateQ (eagerFunOracles H) oa) LinearMap.id :=
  classicalOn_toQuantumAt (classicalOn_funImpl B H) oa

variable [SampleableType Y]

/-- **A program that runs classically against every function, in the QROM.** If against the
oracle of every `H` the program `x` runs as `oa` with its queries answered by `H`, its observed
distribution in the QROM, from the held substate `ρ`, is the output measure of `oa` against the
lazily sampled random function, scaled by the trace of `ρ`. -/
theorem qromEvalDistMap_of_classicalOn {B : QReg} {α β : Type} [MeasurableSpace β]
    {x : QComp (qromSpec X Y) B B α} {oa : OracleComp (unifSpec + (X →ₒ Y)) α}
    (hx : ∀ H, ClassicalOn (additiveOracleRuntime H) x (simulateQ (eagerFunOracles H) oa)
      LinearMap.id)
    (ρ : SubState B) (g : α → β) :
    qromEvalDistMap .instruments x ρ (fun _ p ↦ g p.2.2) =
      ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> (simulateQ (lazyFunOracles X Y) oa).run' ∅] := by
  have hH (H : X → Y) :
      (additiveOracleRuntime H).evalDistMap .instruments x ρ (fun p ↦ g p.2.2) =
        ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> simulateQ (eagerFunOracles H) oa] := by
    refine (QuantumRuntime.evalDist₂_map_eq_evalDistMap _ _ g _ ρ).symm.trans ?_
    rw [QuantumRuntime.evalDist₂, ((hx H).map g).outcomeMeasure, SubState.trace_re_prod,
      trace_re_additiveOracleRuntime_init, mul_one]
  have hlazy : g <$> (simulateQ (lazyFunOracles X Y) oa).run' ∅ =
      (simulateQ (lazyFunOracles X Y) (g <$> oa)).run' ∅ := by
    simp [StateT.run'_eq, StateT.run_map]
  refine (sampledEvalDistMap_eq_sum _ _ _ _ _).trans ?_
  rw [hlazy, evalDist_lazyFun_eq]
  simp only [hH, simulateQ_map]
  rw [← Finset.smul_sum, smul_comm]

/-- **A program on the trivial register that runs classically against every function** returns
each value in the QROM, from the trivial state, with the probability that `oa` returns it against
the lazily sampled random function. -/
theorem qromEvalDistMap_of_classicalOn_singleton {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] {x : QComp (qromSpec X Y) (QReg.of Unit) (QReg.of Unit) α}
    {oa : OracleComp (unifSpec + (X →ₒ Y)) α}
    (hx : ∀ H, ClassicalOn (additiveOracleRuntime H) x (simulateQ (eagerFunOracles H) oa)
      LinearMap.id) (a : α) :
    qromEvalDistMap .instruments x (SubState.basis ()) (fun _ p ↦ p.2.2) {a} =
      Pr{let z ← (simulateQ (lazyFunOracles X Y) oa).run' ∅}[z = a] := by
  have h := qromEvalDistMap_of_classicalOn hx (SubState.basis ()) id
  rw [SubState.matrix_basis, Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one,
    one_smul, id_map] at h
  rw [prEvent_eq_evalDist_singleton]
  exact congrArg (· {a}) h

/-- **The QROM on classical programs is the classical random-oracle model.** A classical
algorithm over coins and `H`, run in the QROM by classical calls beside a held register in the
substate `ρ`, has as observed distribution the output measure of the algorithm against the lazily
sampled random function, scaled by the trace of `ρ`. -/
theorem qromEvalDistMap_toQuantumAt_funImpl (B : QReg) {α β : Type} [MeasurableSpace β]
    (oa : OracleComp (unifSpec + (X →ₒ Y)) α) (ρ : SubState B) (g : α → β) :
    qromEvalDistMap .instruments (oa.toQuantumAt (funImpl B)) ρ (fun _ p ↦ g p.2.2) =
      ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> (simulateQ (lazyFunOracles X Y) oa).run' ∅] :=
  qromEvalDistMap_of_classicalOn (fun H ↦ classicalOn_toQuantumAt_funImpl B H oa) ρ g

end Runtime

end Quantum.Qrom

end
