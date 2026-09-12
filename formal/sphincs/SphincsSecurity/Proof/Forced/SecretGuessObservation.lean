import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.SecretGuessObservation

open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {Coordinate Value : Type} [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value]

def restrict (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) : Coordinate → Finset Value :=
  Function.update allowed coordinate ((allowed coordinate).filter fun value => hit = decide (value = candidate))

omit [Fintype Coordinate] in
theorem restrict_subset (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (other : Coordinate) : restrict allowed coordinate candidate hit other ⊆ allowed other := by
  by_cases heq : other = coordinate
  · subst other
    rw [restrict, Function.update_self]
    exact Finset.filter_subset _ _
  · simp only [restrict, Function.update_of_ne heq, Finset.Subset.refl]

omit [Fintype Coordinate] in
theorem restrict_membership (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    (∀ other, labels other ∈ restrict allowed coordinate candidate hit other) ↔
      (∀ other, labels other ∈ allowed other) ∧ hit = decide (labels coordinate = candidate) := by
  constructor
  · intro h
    refine ⟨fun other => restrict_subset allowed coordinate candidate hit other (h other), ?_⟩
    have hc := h coordinate
    rw [restrict, Function.update_self, Finset.mem_filter] at hc
    exact hc.2
  · rintro ⟨h, hh⟩ other
    by_cases heq : other = coordinate
    · subst other
      rw [restrict, Function.update_self]
      exact Finset.mem_filter.mpr ⟨h coordinate, hh⟩
    · simpa only [restrict, Function.update_of_ne heq] using h other

theorem restrict_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    (if hit = decide (labels coordinate = candidate) then complete allowed labels else 0) =
      restrictionWeight allowed (restrict allowed coordinate candidate hit) *
        complete (restrict allowed coordinate candidate hit) labels := by
  have h := restrict_guard allowed _ (restrict_subset allowed coordinate candidate hit) _
    (restrict_membership allowed coordinate candidate hit) labels
  by_cases hh : hit = decide (labels coordinate = candidate)
  · simpa only [if_pos hh] using h
  · simpa only [if_neg hh] using h

noncomputable def trial (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) : SPMF Bool :=
  complete allowed >>= fun labels => pure (decide (labels coordinate = candidate))

theorem trial_apply (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    trial allowed coordinate candidate hit = restrictionWeight allowed (restrict allowed coordinate candidate hit) := by
  rw [trial, SPMF.bind_apply_eq_tsum]
  simp only [SPMF.pure_apply, mul_ite, mul_one, mul_zero, restrict_mass, ENNReal.tsum_mul_left,
    weight_tsum_complete]

theorem trial_mass (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (labels : Coordinate → Value) :
    trial allowed coordinate candidate hit * complete (restrict allowed coordinate candidate hit) labels =
      if hit = decide (labels coordinate = candidate) then complete allowed labels else 0 := by
  rw [trial_apply, restrict_mass]

theorem trial_nonempty (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (hit : Bool) (hhit : trial allowed coordinate candidate hit ≠ 0) :
    ∀ other, (restrict allowed coordinate candidate hit other).Nonempty := by
  by_contra hn
  rw [trial_apply, weight_of_empty _ _ hn] at hhit
  exact hhit rfl

theorem bind_trial {Result : Type} (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (next : Bool → (Coordinate → Value) → SPMF Result) :
    (complete allowed >>= fun labels => next (decide (labels coordinate = candidate)) labels) =
      (trial allowed coordinate candidate >>= fun hit =>
        complete (restrict allowed coordinate candidate hit) >>= next hit) := by
  apply SPMF.ext
  intro result
  simp only [SPMF.bind_apply_eq_tsum, ← ENNReal.tsum_mul_left, ← mul_assoc, trial_mass, ite_mul, zero_mul]
  rw [ENNReal.tsum_comm]
  simp [Classical.em]

theorem trial_true (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty)
    (coordinate : Coordinate) (candidate : Value) :
    trial allowed coordinate candidate true =
      if candidate ∈ allowed coordinate then ((allowed coordinate).card : ENNReal)⁻¹ else 0 := by
  rw [trial, SPMF.bind_apply_eq_tsum, complete_of_nonempty allowed ha]
  simpa only [SPMF.pure_apply, SPMF.liftM_apply, eq_comm (a := true), decide_eq_true_eq, mul_ite, mul_one, mul_zero,
    probEvent_eq_tsum_ite, PMF.probOutput_eq_apply] using probEvent_uniformTable_eq allowed ha coordinate candidate

structure State (Coordinate Value Memory : Type) where
  allowed : Coordinate → Finset Value
  retired : Finset Coordinate
  guesses : Finset Coordinate
  probes : Nat
  memory : Memory

def SecretSpec (Coordinate Value : Type) : OracleSpec ((Coordinate × Value) ⊕ Coordinate)
  | .inl _ => Bool
  | .inr _ => Value

abbrev World {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Value : Type) :=
  auxSpec + SecretSpec Coordinate Value

structure Environment {AuxIndex : Type} (auxSpec : OracleSpec AuxIndex) (Coordinate Value Memory : Type) where
  auxiliary : State Coordinate Value Memory → (input : auxSpec.Domain) → PMF (auxSpec.Range input × Memory)
  trial : Memory → Coordinate → Value → Bool → Memory
  disclosure : Memory → Coordinate → Value → Memory

variable {Memory AuxIndex : Type} {auxSpec : OracleSpec AuxIndex}

def afterTrial (environment : Environment auxSpec Coordinate Value Memory) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) : State Coordinate Value Memory :=
  { allowed := restrict state.allowed coordinate candidate hit
    retired := if hit then insert coordinate state.retired else state.retired
    guesses := if hit = true ∧ coordinate ∉ state.retired then insert coordinate state.guesses else state.guesses
    probes := state.probes + 1
    memory := environment.trial state.memory coordinate candidate hit }

def afterDisclosure (environment : Environment auxSpec Coordinate Value Memory) (state : State Coordinate Value Memory)
    (coordinate : Coordinate) (value : Value) : State Coordinate Value Memory :=
  { state with
    allowed := discloseTableValue state.allowed coordinate value
    retired := insert coordinate state.retired
    memory := environment.disclosure state.memory coordinate value }

noncomputable def fixedImpl (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => StateT.mk fun state =>
      (fun result => (result.1, { state with memory := result.2 })) <$> (liftM (environment.auxiliary state input) : SPMF _)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      let hit := decide (labels coordinate = candidate)
      pure (hit, afterTrial environment state coordinate candidate hit)
  | .inr (.inr coordinate) => StateT.mk fun state =>
      pure (labels coordinate, afterDisclosure environment state coordinate (labels coordinate))

noncomputable def lazyImpl (environment : Environment auxSpec Coordinate Value Memory) :
    QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF)
  | .inl input => StateT.mk fun state =>
      (fun result => (result.1, { state with memory := result.2 })) <$> (liftM (environment.auxiliary state input) : SPMF _)
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, afterTrial environment state coordinate candidate hit)) <$> trial state.allowed coordinate candidate
  | .inr (.inr coordinate) => StateT.mk fun state =>
      (fun value => (value, afterDisclosure environment state coordinate value)) <$> cell (state.allowed coordinate)

noncomputable def runWith {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    SPMF (Result × State Coordinate Value Memory) :=
  (simulateQ implementation computation).run state

noncomputable def fixedRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (labels : Coordinate → Value) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) := runWith (fixedImpl environment labels) computation state

noncomputable def lazyRun {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :=
  runWith (lazyImpl environment) computation state

def probeStep : (World auxSpec Coordinate Value).Domain → Nat
  | .inr (.inl _) => 1
  | _ => 0

theorem lazyImpl_probes (environment : Environment auxSpec Coordinate Value Memory)
    (state : State Coordinate Value Memory) (input : (World auxSpec Coordinate Value).Domain)
    (result : (World auxSpec Coordinate Value).Range input × State Coordinate Value Memory)
    (hr : (lazyImpl environment input).run state result ≠ 0) :
    result.2.probes = state.probes + probeStep input := by
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact (Nat.add_zero _).symm
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, _, rfl⟩ := hr
          rfl
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact (Nat.add_zero _).symm

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem runWith_pure {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (result : Result) (state : State Coordinate Value Memory) :
    runWith implementation (pure result) state = pure (result, state) := by
  simp only [runWith, simulateQ_pure, StateT.run_pure]

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem runWith_query_bind {Result : Type}
    (implementation : QueryImpl (World auxSpec Coordinate Value) (StateT (State Coordinate Value Memory) SPMF))
    (input : (World auxSpec Coordinate Value).Domain)
    (next : (World auxSpec Coordinate Value).Range input → OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) :
    runWith implementation (liftM ((World auxSpec Coordinate Value).query input) >>= next) state =
      ((implementation input).run state >>= fun result => runWith implementation (next result.1) result.2) := by
  simp only [runWith, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem run_posterior {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    (complete state.allowed >>= fun labels => (fun result => (labels, result)) <$> fixedRun environment labels computation state) =
      (lazyRun environment computation state >>= fun result =>
        (fun labels => (labels, result)) <$> complete result.2.allowed) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure result => simp only [fixedRun, lazyRun, runWith_pure, pure_bind, ← bind_pure_comp]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
            StateT.run_mk, bind_map_left, map_bind, bind_assoc]
          rw [RetainedObservation.bind_comm]
          exact congrArg ((liftM (environment.auxiliary state input) : SPMF _) >>= ·)
            (funext fun answer => ih answer.1 { state with memory := answer.2 })
      | inr input =>
          cases input with
          | inl probe =>
              rcases probe with ⟨coordinate, candidate⟩
              simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
                StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
              rw [bind_trial state.allowed coordinate candidate (fun hit labels =>
                (fun result => (labels, result)) <$> runWith (fixedImpl environment labels) (next hit)
                  (afterTrial environment state coordinate candidate hit))]
              exact congrArg (trial state.allowed coordinate candidate >>= ·)
                (funext fun hit => ih hit (afterTrial environment state coordinate candidate hit))
          | inr coordinate =>
              simp only [fixedRun, lazyRun, runWith_query_bind, fixedImpl, lazyImpl,
                StateT.run_mk, pure_bind, bind_map_left, bind_assoc]
              rw [bind_disclose state.allowed coordinate (fun value labels =>
                (fun result => (labels, result)) <$> runWith (fixedImpl environment labels) (next value)
                  (afterDisclosure environment state coordinate value))]
              exact congrArg (cell (state.allowed coordinate) >>= ·)
                (funext fun value => ih value (afterDisclosure environment state coordinate value))

theorem lazyRun_preserves {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (invariant : State Coordinate Value Memory → Prop)
    (hstep : ∀ state, invariant state → ∀ input result,
      (lazyImpl environment input).run state result ≠ 0 → invariant result.2)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (hinvariant : invariant state) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [lazyRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hinvariant
  | query_bind input next ih =>
      rw [lazyRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 middle.2 (hstep state hinvariant input middle hm) result hr

theorem lazyRun_nonempty {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : ∀ coordinate, (result.2.allowed coordinate).Nonempty := by
  apply lazyRun_preserves environment (fun state => ∀ coordinate, (state.allowed coordinate).Nonempty) _ computation state ha result hr
  intro state hs input result hr
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact hs
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, hh, rfl⟩ := hr
          exact trial_nonempty state.allowed coordinate candidate hit hh
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact discloseTableValue_nonempty state.allowed hs coordinate value

theorem run_erasure {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (computation : OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) :
    (complete state.allowed >>= fun labels => fixedRun environment labels computation state) =
      lazyRun environment computation state := by
  have h := congrArg (Functor.map Prod.snd) (run_posterior environment computation state)
  simp only [map_bind, Functor.map_map, id_map'] at h
  calc
    _ = lazyRun environment computation state >>= fun result =>
        (fun _ => result) <$> complete result.2.allowed := h
    _ = lazyRun environment computation state >>= pure := by
      apply RetainedObservation.bind_congr
      intro result hr
      rw [complete_of_nonempty result.2.allowed (lazyRun_nonempty environment computation state ha result hr),
        map_eq_bind_pure_comp]
      exact RetainedObservation.lift_bind_const _ _
    _ = _ := bind_pure _

omit [Fintype Coordinate] in
theorem restrict_false (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value) :
    restrict allowed coordinate candidate false = eraseTableValue allowed coordinate candidate := by
  funext other
  by_cases heq : other = coordinate
  · subst other
    rw [restrict, eraseTableValue, Function.update_self, Function.update_self]
    ext value
    by_cases hv : value = candidate
    · simp [hv]
    · simp [hv]
  · simp only [restrict, eraseTableValue, Function.update_of_ne heq]

omit [Fintype Coordinate] in
theorem restrict_false_card (allowed : Coordinate → Finset Value) (coordinate : Coordinate) (candidate : Value)
    (other : Coordinate) : (allowed other).card ≤ (restrict allowed coordinate candidate false other).card + 1 := by
  rw [restrict_false]
  by_cases heq : other = coordinate
  · subst other
    rw [eraseTableValue, Function.update_self]
    have h := Finset.pred_card_le_card_erase (s := allowed coordinate) (a := candidate)
    omega
  · rw [eraseTableValue, Function.update_of_ne heq]
    omega

def Invariant (size : Nat) (state : State Coordinate Value Memory) : Prop :=
  (∀ coordinate, coordinate ∉ state.retired → size ≤ (state.allowed coordinate).card + state.probes) ∧
    state.guesses ⊆ state.retired

omit [Fintype Coordinate] in
theorem afterTrial_invariant (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    Invariant size (afterTrial environment state coordinate candidate hit) := by
  cases hit with
  | false =>
      constructor
      · intro other ho
        have hb := hs.1 other ho
        have hc := restrict_false_card state.allowed coordinate candidate other
        change size ≤ (restrict state.allowed coordinate candidate false other).card + (state.probes + 1)
        omega
      · simpa only [afterTrial, Bool.false_eq_true, false_and, if_false] using hs.2
  | true =>
      constructor
      · intro other ho
        have hn : other ≠ coordinate ∧ other ∉ state.retired := by
          simpa only [afterTrial, if_true, Finset.mem_insert, not_or] using ho
        have hb := hs.1 other hn.2
        change size ≤ (restrict state.allowed coordinate candidate true other).card + (state.probes + 1)
        rw [restrict, Function.update_of_ne hn.1]
        omega
      · simp only [afterTrial, if_true, true_and]
        split
        · exact Finset.insert_subset_insert coordinate hs.2
        · exact hs.2.trans (Finset.subset_insert _ _)

omit [Fintype Coordinate] [DecidableEq Value] in
theorem afterDisclosure_invariant (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (state : State Coordinate Value Memory) (hs : Invariant size state)
    (coordinate : Coordinate) (value : Value) : Invariant size (afterDisclosure environment state coordinate value) := by
  constructor
  · intro other ho
    have hn : other ≠ coordinate ∧ other ∉ state.retired := by
      simpa only [afterDisclosure, Finset.mem_insert, not_or] using ho
    change size ≤ (discloseTableValue state.allowed coordinate value other).card + state.probes
    rw [discloseTableValue, Function.update_of_ne hn.1]
    exact hs.1 other hn.2
  · exact hs.2.trans (Finset.subset_insert _ _)

theorem lazyRun_invariant {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (size : Nat) (computation : OracleComp (World auxSpec Coordinate Value) Result)
    (state : State Coordinate Value Memory) (hs : Invariant size state) (result : Result × State Coordinate Value Memory)
    (hr : lazyRun environment computation state result ≠ 0) : Invariant size result.2 := by
  apply lazyRun_preserves environment (Invariant size) _ computation state hs result hr
  intro state hs input result hr
  cases input with
  | inl input =>
      simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
        Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      exact hs
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨hit, _, rfl⟩ := hr
          exact afterTrial_invariant environment size state hs coordinate candidate hit
      | inr coordinate =>
          simp only [lazyImpl, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero,
            Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
          obtain ⟨value, _, rfl⟩ := hr
          exact afterDisclosure_invariant environment size state hs coordinate value

omit [Fintype Coordinate] in
theorem afterTrial_guesses_card (environment : Environment auxSpec Coordinate Value Memory)
    (state : State Coordinate Value Memory) (hs : state.guesses ⊆ state.retired)
    (coordinate : Coordinate) (candidate : Value) (hit : Bool) :
    (afterTrial environment state coordinate candidate hit).guesses.card =
      state.guesses.card + if hit = true ∧ coordinate ∉ state.retired then 1 else 0 := by
  by_cases hh : hit = true ∧ coordinate ∉ state.retired
  · simp only [afterTrial, if_pos hh]
    exact Finset.card_insert_of_notMem (fun hm => hh.2 (hs hm))
  · simp only [afterTrial, if_neg hh, Nat.add_zero]

theorem trial_true_le (size q : Nat) (state : State Coordinate Value Memory)
    (hs : Invariant size state) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hq : state.probes ≤ q) (coordinate : Coordinate) (hc : coordinate ∉ state.retired) (candidate : Value) :
    trial state.allowed coordinate candidate true ≤ ((size - q : Nat) : ENNReal)⁻¹ := by
  rw [trial_true state.allowed ha]
  split
  · apply ENNReal.inv_le_inv.mpr
    have h := hs.1 coordinate hc
    exact_mod_cast (show size - q ≤ (state.allowed coordinate).card by omega)
  · exact bot_le

def initialState [Fintype Value] (memory : Memory) : State Coordinate Value Memory :=
  ⟨fun _ => Finset.univ, ∅, ∅, 0, memory⟩

omit [Fintype Coordinate] [DecidableEq Coordinate] [DecidableEq Value] in
theorem initialState_invariant [Fintype Value] (memory : Memory) :
    Invariant (Fintype.card Value) (initialState (Coordinate := Coordinate) (Value := Value) memory) := by
  simp [Invariant, initialState]

def disclosure (coordinate : Coordinate) : OracleComp (World auxSpec Coordinate Value) Value :=
  liftM ((World auxSpec Coordinate Value).query (.inr (.inr coordinate)))

def disclosureSequenceState (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) (state : State Coordinate Value Memory) : State Coordinate Value Memory :=
  (List.ofFn coordinates).foldl (fun state coordinate => afterDisclosure environment state coordinate (labels coordinate)) state

omit [Fintype Coordinate] [DecidableEq Value] in
theorem disclosureSequenceState_counts (environment : Environment auxSpec Coordinate Value Memory) (labels : Coordinate → Value)
    {n : Nat} (coordinates : Fin n → Coordinate) (state : State Coordinate Value Memory) :
    ((disclosureSequenceState environment labels coordinates state).guesses,
      (disclosureSequenceState environment labels coordinates state).probes) = (state.guesses, state.probes) := by
  unfold disclosureSequenceState
  generalize List.ofFn coordinates = entries
  induction entries generalizing state with
  | nil => rfl
  | cons coordinate entries ih => exact ih (afterDisclosure environment state coordinate (labels coordinate))

omit [Fintype Coordinate] in
theorem fixedRun_disclosureSequence_bind {Result : Type} (environment : Environment auxSpec Coordinate Value Memory)
    (labels : Coordinate → Value) {n : Nat} (coordinates : Fin n → Coordinate)
    (next : (Fin n → Value) → OracleComp (World auxSpec Coordinate Value) Result) (state : State Coordinate Value Memory) :
    fixedRun environment labels ((sequenceFin fun index => disclosure (coordinates index)) >>= next) state =
      fixedRun environment labels (next (fun index => labels (coordinates index)))
        (disclosureSequenceState environment labels coordinates state) := by
  induction n generalizing state with
  | zero =>
      have hv : (Fin.elim0 : Fin 0 → Value) = (fun index => labels (coordinates index)) := by
        funext index
        exact Fin.elim0 index
      simp only [sequenceFin, pure_bind, hv, disclosureSequenceState, List.ofFn_zero, List.foldl_nil]
  | succ n ih =>
      rw [sequenceFin, bind_assoc]
      change runWith (fixedImpl environment labels)
        (liftM ((World auxSpec Coordinate Value).query (.inr (.inr (coordinates 0)))) >>= _) state = _
      rw [runWith_query_bind]
      simp only [fixedImpl, StateT.run_mk, pure_bind, bind_assoc]
      change fixedRun environment labels
        ((sequenceFin fun index => disclosure (coordinates index.succ)) >>=
          fun tail => next (Fin.cons (labels (coordinates 0)) tail))
        (afterDisclosure environment state (coordinates 0) (labels (coordinates 0))) = _
      rw [ih]
      have hv : Fin.cons (labels (coordinates 0)) (fun index => labels (coordinates index.succ)) =
          (fun index => labels (coordinates index)) := by
        funext index
        cases index using Fin.cases <;> rfl
      rw [hv]
      simp only [disclosureSequenceState, List.ofFn_succ, List.foldl_cons]

end SphincsSecurity.Concrete.SecretGuessObservation
