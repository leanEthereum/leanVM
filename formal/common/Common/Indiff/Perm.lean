module

public import Common.Indiff.Real

@[expose] public section

/-!
# Indifferentiability: a random permutation is a random function, up to collisions

The real world over the lazily sampled random permutation (`realGame`) and over the lazily
sampled random function (`funImpl`) differ only when a fresh answer of the random function hits
an answer already given, in the same direction: probability at most `q² / |S|` for `q`
permutation calls in all, counting the sponge's (`realGame_funGame_le`).

The proof first unfolds the hash queries into the sponge's permutation queries (`toPerm`), so
that each step makes at most one fresh draw; then compares the two lazy samplers with a
collision flag: a fresh draw of the random function that falls on a used point raises the flag,
and the random permutation redraws there (`permFlag`, `funFlag`). Until the flag rises the two
agree; a fresh permutation answer drawn by rejection is uniform over the unused points
(`uniformAvoiding_rejection`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Generic

variable {S : Type} [Fintype S] [DecidableEq S] [SampleableType S]

/-- **Rejection sampling.** A uniform draw, redrawn uniformly outside `l` when it falls in `l`, is
a uniform draw outside `l`. -/
theorem uniformAvoiding_rejection (l : List S) :
    (($ᵗ S) >>= fun u ↦ if u ∈ l then uniformAvoiding l else pure u) =ᵈ uniformAvoiding l := by
  by_cases h : ∃ y, y ∉ l
  · set g : S → ProbComp S := fun u ↦ if u ∈ l then uniformAvoiding l else pure u with hg
    rw [evalDistEq_iff_forall_prEvent_eq_output]
    intro a
    rw [prEvent_bind_eq_sum_fintype]
    simp only [SampleableType.prEvent_uniformSample_eq_singleton]
    set r := Pr{let y ← uniformAvoiding l}[y = a] with hr
    have key : ∀ x, Pr{let y ← g x}[y = a] = if x ∈ l then r else if x = a then 1 else 0 := by
      intro x; simp only [hg]; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun x _ ↦ congrArg _ (key x)]
    rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_ite_eq' (Finset.univ.filter fun x ↦ x ∉ l) a (fun _ ↦ (1 : ℝ≥0∞))]
    have hk := prEvent_uniformAvoiding h (· = a)
    rw [← hr] at hk
    set n := Fintype.card S with hn
    set j := (Finset.univ.filter fun x : S ↦ x ∈ l).card with hj
    set k := (Finset.univ.filter fun x : S ↦ x ∉ l).card with hk'
    have hjk : j + k = n := by
      rw [hj, hk', hn, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    have hk0 : k ≠ 0 := by
      obtain ⟨y, hy⟩ := h
      exact Finset.card_ne_zero.mpr ⟨y, by simpa using hy⟩
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      have : 0 < n := Fintype.card_pos
      exact_mod_cast this.ne'
    by_cases ha : a ∈ l
    · have hr0 : r = 0 := by
        rw [hk]
        have : (Finset.univ.filter fun y : S ↦ y ∉ l ∧ y = a) = ∅ := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          rintro hy rfl
          exact hy ha
        rw [this, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
      simp [hr0, ha]
    · have hr1 : r = (k : ℝ≥0∞)⁻¹ := by
        rw [hk]
        have : (Finset.univ.filter fun y : S ↦ y ∉ l ∧ y = a) = {a} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]; constructor
          · exact fun h ↦ h.2
          · rintro rfl; exact ⟨ha, rfl⟩
        rw [this, Finset.card_singleton, Nat.cast_one, one_div]
      simp only [Finset.mem_filter, Finset.mem_univ, ha, not_false_eq_true, and_self,
        ↓reduceIte, hr1]
      have hkf : (k : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top k
      have hk0' : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk0
      calc (n : ℝ≥0∞)⁻¹ * (j * (k : ℝ≥0∞)⁻¹ + 1)
          = (n : ℝ≥0∞)⁻¹ * ((j + k : ℕ) * (k : ℝ≥0∞)⁻¹) := by
            rw [Nat.cast_add, add_mul, ENNReal.mul_inv_cancel hk0' hkf]
        _ = (k : ℝ≥0∞)⁻¹ := by
            rw [hjk, ← mul_assoc, ENNReal.inv_mul_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  · push Not at h
    have : (($ᵗ S) >>= fun u ↦ if u ∈ l then uniformAvoiding l else pure u) =
        (($ᵗ S) >>= fun _ ↦ uniformAvoiding l) :=
      bind_congr fun u ↦ by simp [h u]
    rw [this]
    exact EvalDistEq.bind_const _ _

/-- A uniform draw lands in `l` with probability at most `|l| / |S|`. -/
theorem prEvent_uniform_mem_le (l : List S) :
    Pr{let u ← $ᵗ S}[u ∈ l] ≤ l.length / (Fintype.card S : ℝ≥0∞) := by
  rw [SampleableType.prEvent_uniformSample]
  gcongr
  calc (Finset.univ.filter fun u : S ↦ u ∈ l).card
      ≤ l.toFinset.card := Finset.card_le_card fun u hu ↦ by simpa using hu
    _ ≤ l.length := List.toFinset_card_le l

/-- Coins forwarded, permutation queries to `impl`. -/
noncomputable def permExt {σ : Type} (impl : QueryImpl (permutationOracleSpec S) (StateT σ ProbComp)) :
    QueryImpl (unifSpec + permutationOracleSpec S) (StateT σ ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => impl q

/-- The weight of a permutation-model query: a permutation query weighs one, a coin nothing. -/
def permWeight : (unifSpec + permutationOracleSpec S).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The lazy permutation with a collision flag: a fresh answer is drawn uniformly; when it
falls on a used point the flag rises and the answer is redrawn outside the used points. -/
noncomputable def permFlag : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp)
  | .forward x => StateT.mk fun s ↦
      match forwardLookup s.1 x with
      | some y => pure (y, s)
      | none => do
        let u ← $ᵗ S
        if u ∈ s.1.map Prod.snd then do
          let y ← uniformAvoiding (s.1.map Prod.snd)
          pure (y, ((x, y) :: s.1, true))
        else pure (u, ((x, u) :: s.1, s.2))
  | .inverse y => StateT.mk fun s ↦
      match inverseLookup s.1 y with
      | some x => pure (x, s)
      | none => do
        let u ← $ᵗ S
        if u ∈ s.1.map Prod.fst then do
          let x ← uniformAvoiding (s.1.map Prod.fst)
          pure (x, ((x, y) :: s.1, true))
        else pure (u, ((u, y) :: s.1, s.2))

/-- The lazy random function with a collision flag: a fresh answer falling on a used point
raises the flag. -/
noncomputable def funFlag : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp)
  | .forward x => StateT.mk fun s ↦
      match forwardLookup s.1 x with
      | some y => pure (y, s)
      | none => do
        let u ← $ᵗ S
        if u ∈ s.1.map Prod.snd then pure (u, ((x, u) :: s.1, true))
        else pure (u, ((x, u) :: s.1, s.2))
  | .inverse y => StateT.mk fun s ↦
      match inverseLookup s.1 y with
      | some x => pure (x, s)
      | none => do
        let u ← $ᵗ S
        if u ∈ s.1.map Prod.fst then pure (u, ((u, y) :: s.1, true))
        else pure (u, ((u, y) :: s.1, s.2))

/-- The flagged lazy permutation is the lazy permutation once the flag is forgotten. -/
theorem permFlag_proj (q : PermutationQuery S) (s : PermutationEdges S × Bool) :
    Prod.map id Prod.fst <$> (permFlag q).run s =ᵈ (lazyRandomPermutation q).run s.1 := by
  cases q with
  | forward x =>
    simp only [permFlag, lazyRandomPermutation, StateT.run_mk]
    rcases h : forwardLookup s.1 x with _ | y
    · have := (uniformAvoiding_rejection (s.1.map Prod.snd)).map
        (fun y ↦ (y, (x, y) :: s.1))
      refine EvalDistEq.trans ?_ this
      simp only [map_bind]
      refine EvalDistEq.bind_right _ fun u ↦ ?_
      split_ifs <;> simp
    · simp
  | inverse y =>
    simp only [permFlag, lazyRandomPermutation, StateT.run_mk]
    rcases h : inverseLookup s.1 y with _ | x
    · have := (uniformAvoiding_rejection (s.1.map Prod.fst)).map
        (fun x ↦ (x, (x, y) :: s.1))
      refine EvalDistEq.trans ?_ this
      simp only [map_bind]
      refine EvalDistEq.bind_right _ fun u ↦ ?_
      split_ifs <;> simp
    · simp

/-- The flagged lazy function is the lazy function once the flag is forgotten. -/
theorem funFlag_proj (q : PermutationQuery S) (s : PermutationEdges S × Bool) :
    Prod.map id Prod.fst <$> (funFlag q).run s = (lazyFun q).run s.1 := by
  cases q with
  | forward x =>
    simp only [funFlag, lazyFun, StateT.run_mk]
    rcases h : forwardLookup s.1 x with _ | y
    · simp only [map_bind]
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun u ↦ ?_
      split_ifs <;> simp
    · simp
  | inverse y =>
    simp only [funFlag, lazyFun, StateT.run_mk]
    rcases h : inverseLookup s.1 y with _ | x
    · simp only [map_bind]
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun u ↦ ?_
      split_ifs <;> simp
    · simp

/-- The flagged samplers agree away from a raised flag. -/
theorem permFlag_funFlag_agree (q : PermutationQuery S) (s : PermutationEdges S × Bool)
    (p : S × (PermutationEdges S × Bool) → Prop) :
    Pr{let z ← (permFlag q).run s}[p z ∧ ¬ z.2.2 = true] =
      Pr{let z ← (funFlag q).run s}[p z ∧ ¬ z.2.2 = true] := by
  have key : ∀ (l : List S) (e : S → PermutationEdges S),
      Pr{let z ← (($ᵗ S) >>= fun u ↦ if u ∈ l then (uniformAvoiding l >>= fun y ↦
          pure (y, (e y, true))) else pure (u, (e u, s.2)))}[p z ∧ ¬ z.2.2 = true] =
        Pr{let z ← (($ᵗ S) >>= fun u ↦ if u ∈ l then pure (u, (e u, true))
          else pure (u, (e u, s.2)))}[p z ∧ ¬ z.2.2 = true] := by
    intro l e
    refine prEvent_bind_congr _ _ _ _ _ fun u ↦ ?_
    split_ifs
    · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_,
        prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
      · simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact h.2 rfl
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨y, -, rfl⟩ := hz
        exact h.2 rfl
    · rfl
  cases q with
  | forward x =>
    simp only [permFlag, funFlag, StateT.run_mk]
    split
    · rfl
    · exact key _ fun y ↦ (x, y) :: s.1
  | inverse y =>
    simp only [permFlag, funFlag, StateT.run_mk]
    split
    · rfl
    · exact key _ fun x ↦ (x, y) :: s.1

/-- A raised flag stays raised. -/
theorem flag_mono (impl : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp))
    (himpl : impl = permFlag ∨ impl = funFlag) (t : (unifSpec + permutationOracleSpec S).Domain)
    (s : PermutationEdges S × Bool) (hs : s.2 = true) {z} (hz : z ∈ support ((permExt impl t).run s)) :
    z.2.2 = true := by
  rcases t with n | q
  · simp only [permExt, StateT.run_monadLift, monadLift_self, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · simp only [permExt] at hz
    rcases himpl with rfl | rfl <;> cases q <;>
      simp only [permFlag, funFlag, StateT.run_mk] at hz <;> split at hz <;>
      simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at hz
    all_goals first
      | (subst hz; exact hs)
      | (obtain ⟨u, -, hz⟩ := hz
         split_ifs at hz <;>
           simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at hz <;>
           first | (subst hz; first | rfl | exact hs) | (obtain ⟨y, -, rfl⟩ := hz; rfl))

/-- One step of a flagged sampler raises the flag with probability at most `N / |S|` from a log
shorter than `N`. -/
theorem flag_step_le (impl : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp))
    (himpl : impl = permFlag ∨ impl = funFlag) (N : ℕ) (t : (unifSpec + permutationOracleSpec S).Domain)
    (s : PermutationEdges S × Bool) (hs : ¬ s.2 = true) (hN : s.1.length + permWeight t ≤ N) :
    Pr{let z ← (permExt impl t).run s}[z.2.2 = true] ≤
      permWeight t * (N / (Fintype.card S : ℝ≥0∞)) := by
  rcases t with n | q
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
    · exact zero_le
    · simp only [permExt, StateT.run_monadLift, monadLift_self, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs h
  · simp only [permWeight, Nat.cast_one, one_mul]
    simp only [permWeight] at hN
    have hl : ∀ l : List S, l.length = s.1.length →
        Pr{let u ← $ᵗ S}[u ∈ l] ≤ N / (Fintype.card S : ℝ≥0∞) := fun l hl ↦
      (prEvent_uniform_mem_le l).trans (by gcongr; exact_mod_cast (by omega : l.length ≤ N))
    -- a fresh draw raises the flag only when it falls in the used points
    have hdraw : ∀ (l : List S) {β : Type} (f : S → ProbComp (β × (PermutationEdges S × Bool))),
        l.length = s.1.length →
        (∀ u, u ∉ l → ∀ z ∈ support (f u), ¬ z.2.2 = true) →
        Pr{let z ← ($ᵗ S) >>= f}[z.2.2 = true] ≤ N / (Fintype.card S : ℝ≥0∞) := by
      intro l β f hlen hf
      refine (prEvent_bind_le_prEvent_add_of_support _ _ (· ∈ l) _ (ε := 0)
        fun u _ hu ↦ ?_).trans ?_
      · exact le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ hf u hu z hz h)
      · rw [add_zero]; exact hl l hlen
    simp only [permExt]
    rcases himpl with rfl | rfl <;> cases q with
    | forward x =>
      simp only [permFlag, funFlag, StateT.run_mk]
      split
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
        · exact zero_le
        · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hs h
      · refine hdraw (s.1.map Prod.snd) _ (by simp) fun u hu z hz h ↦ ?_
        simp only [hu, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs h
    | inverse y =>
      simp only [permFlag, funFlag, StateT.run_mk]
      split
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h ↦ ?_]
        · exact zero_le
        · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hs h
      · refine hdraw (s.1.map Prod.fst) _ (by simp) fun u hu z hz h ↦ ?_
        simp only [hu, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hs h

/-- A step of a flagged sampler adds at most one edge per permutation query. -/
theorem flag_size_le (impl : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp))
    (himpl : impl = permFlag ∨ impl = funFlag) (t : (unifSpec + permutationOracleSpec S).Domain)
    (s : PermutationEdges S × Bool) {z} (hz : z ∈ support ((permExt impl t).run s)) :
    z.2.1.length ≤ s.1.length + permWeight t := by
  rcases t with n | q
  · simp only [permExt, StateT.run_monadLift, monadLift_self, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp [permWeight]
  · simp only [permExt, permWeight] at hz ⊢
    rcases himpl with rfl | rfl <;> cases q <;>
      simp only [permFlag, funFlag, StateT.run_mk] at hz <;> split at hz <;>
      simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at hz
    all_goals first
      | (subst hz; simp)
      | (obtain ⟨u, -, hz⟩ := hz
         split_ifs at hz <;>
           simp only [support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at hz <;>
           first | (subst hz; simp) | (obtain ⟨y, -, rfl⟩ := hz; simp))

/-- The flagged samplers raise the flag with probability at most `q² / |S|` over `q` permutation
queries. -/
theorem prEvent_flag_le (impl : QueryImpl (permutationOracleSpec S) (StateT (PermutationEdges S × Bool) ProbComp))
    (himpl : impl = permFlag ∨ impl = funFlag) {α : Type}
    (oa : OracleComp (unifSpec + permutationOracleSpec S) α) (q : ℕ) (hq : QueryCostAtMost oa permWeight q) :
    Pr{let z ← (simulateQ (permExt impl) oa).run ([], false)}[z.2.2 = true] ≤
      q * (q / (Fintype.card S : ℝ≥0∞)) := by
  have := prEvent_run_bad_le (spec' := unifSpec) (permExt impl) (fun s ↦ s.2 = true)
    (fun _ ↦ True) permWeight (fun s ↦ s.1.length) q (q / (Fintype.card S : ℝ≥0∞))
    (fun _ _ _ _ _ ↦ trivial) (fun t s _ z hz ↦ flag_size_le impl himpl t s hz)
    (fun t s _ hs hN ↦ flag_step_le impl himpl q t s hs hN) oa q hq ([], false) trivial
    (by simp)
  simpa using this

end Generic

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The distinguisher's queries in the permutation model: a hash query becomes the sponge's
permutation queries. -/
noncomputable def toPerm : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (OracleComp (unifSpec + permutationOracleSpec (SpState Dg E C)))
  | .inl n => liftM ((unifSpec + permutationOracleSpec (SpState Dg E C)).query (.inl n))
  | .inr (.inl m) => (spongeWith P iv (fun x ↦
      liftM ((unifSpec + permutationOracleSpec (SpState Dg E C)).query (.inr (.forward x)))) m :
      OracleComp (unifSpec + permutationOracleSpec (SpState Dg E C)) Dg)
  | .inr (.inr q) => liftM ((unifSpec + permutationOracleSpec (SpState Dg E C)).query (.inr q))

/-- Simulating the sponge's permutation queries is the sponge over the implementation. -/
theorem simulateQ_absorbAll {σ : Type}
    (impl : QueryImpl (unifSpec + permutationOracleSpec (SpState Dg E C)) (StateT σ ProbComp))
    (s : SpState Dg E C) (bs : List (Dg × E)) :
    simulateQ impl (absorbAll (fun x ↦
      liftM ((unifSpec + permutationOracleSpec (SpState Dg E C)).query (.inr (.forward x)))) s bs) =
      absorbAll (fun x ↦ impl (.inr (.forward x))) s bs := by
  induction bs generalizing s with
  | nil => simp
  | cons B bs ih =>
    simp only [absorbAll_cons, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, ih]

/-- **The real world unfolds into the permutation model.** -/
theorem realGame_eq_toPerm {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    realGame P iv D = (simulateQ (permExt lazyRandomPermutation) (simulateQ (toPerm P iv) D)).run' [] := by
  rw [realGame, ← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  rcases t with n | m | q
  · simp [toPerm, permExt, realImpl]
  · simp [toPerm, realImpl, spongeWith, simulateQ_absorbAll, permExt]
  · simp [toPerm, permExt, realImpl]

/-- **The real world over random functions unfolds into the permutation model.** -/
theorem funGame_eq_toPerm {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    (simulateQ (funImpl P iv) D).run' [] =
      (simulateQ (permExt lazyFun) (simulateQ (toPerm P iv) D)).run' [] := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext t
  rcases t with n | m | q
  · simp [toPerm, permExt, funImpl]
  · simp [toPerm, funImpl, spongeWith, simulateQ_absorbAll, permExt]
  · simp [toPerm, permExt, funImpl]

/-- The sponge makes one permutation query per block. -/
theorem isWeightBound_absorbAll (s : SpState Dg E C) (bs : List (Dg × E)) :
    QueryCostAtMost (absorbAll (fun x ↦
      (liftM ((unifSpec + permutationOracleSpec (SpState Dg E C)).query (.inr (.forward x))) :
        OracleComp (unifSpec + permutationOracleSpec (SpState Dg E C)) _)) s bs)
      permWeight bs.length := by
  induction bs generalizing s with
  | nil => trivial
  | cons B bs ih =>
    rw [absorbAll_cons, List.length_cons, add_comm]
    exact QueryCostAtMost.bind (isWeightBound_query permWeight _) fun y ↦ ih y

/-- **The unfolded distinguisher makes at most `q` permutation queries.** -/
theorem isWeightBound_toPerm {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost (Dg := Dg) P) q) :
    QueryCostAtMost (simulateQ (toPerm P iv) D) permWeight q := by
  induction D using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at hD
    obtain ⟨ht, hk⟩ := hD
    rw [simulateQ_query_bind]
    have h1 : QueryCostAtMost (toPerm P iv t) permWeight (queryCost P t) := by
      rcases t with n | m | q'
      · exact isWeightBound_query permWeight (.inl n)
      · simp only [toPerm, spongeWith, queryCost]
        rw [QueryCostAtMost, isQueryBound_map_iff]
        exact isWeightBound_absorbAll iv (P.pad m)
      · exact isWeightBound_query permWeight (.inr q')
    have := h1.bind fun u ↦ ih u (q - queryCost P t) (hk u)
    rwa [Nat.add_sub_cancel' ht] at this

/-- **A random permutation is a random function, up to collisions.** For a distinguisher making
at most `q` permutation calls in all (counting the sponge's), the real world over the random
permutation and over the random function give every event probabilities within `q² / |S|`. -/
theorem realGame_funGame_le {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost (Dg := Dg) P) q) (p : α → Prop) :
    Pr{let a ← realGame P iv D}[p a] ≤ Pr{let a ← (simulateQ (funImpl P iv) D).run' []}[p a] +
        q * (q / (Fintype.card (SpState Dg E C) : ℝ≥0∞)) ∧
      Pr{let a ← (simulateQ (funImpl P iv) D).run' []}[p a] ≤ Pr{let a ← realGame P iv D}[p a] +
        q * (q / (Fintype.card (SpState Dg E C) : ℝ≥0∞)) := by
  have hD' := isWeightBound_toPerm P iv D q hD
  rw [realGame_eq_toPerm, funGame_eq_toPerm]
  set D' := simulateQ (toPerm P iv) D
  have hcoin : ∀ (σ : Type) (n : ℕ) (s : σ),
      ((liftM (unifSpec.query n : ProbComp (Fin (n + 1))) : StateT σ ProbComp _)).run s =
        (fun u ↦ (u, s)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
    intro σ n s; simp [map_eq_bind_pure_comp]
  have hperm : (simulateQ (permExt lazyRandomPermutation) D').run' [] =ᵈ
      (simulateQ (permExt permFlag) D').run' (([] : PermutationEdges (SpState Dg E C)), false) :=
    (run'_simulateQ_evalDistEq_of_inv (permExt permFlag) (permExt lazyRandomPermutation) (fun _ ↦ True)
      Prod.fst (fun _ _ _ _ _ ↦ trivial) (fun t s _ ↦ by
        rcases t with n | q'
        · simp [permExt, hcoin, Functor.map_map]
        · exact permFlag_proj q' s) D' (([] : PermutationEdges (SpState Dg E C)), false) trivial).symm
  have hfun : (simulateQ (permExt lazyFun) D').run' [] =
      (simulateQ (permExt funFlag) D').run' (([] : PermutationEdges (SpState Dg E C)), false) :=
    (OracleComp.run'_simulateQ_eq_of_query_map_eq (permExt funFlag) (permExt lazyFun)
      Prod.fst (fun t s ↦ by
        rcases t with n | q'
        · simp [permExt, hcoin, Functor.map_map]
        · exact funFlag_proj q' s) D' (([] : PermutationEdges (SpState Dg E C)), false)).symm
  have hagree : ∀ t (s : PermutationEdges (SpState Dg E C) × Bool), ¬ s.2 = true →
      ∀ r : _ → Prop, Pr{let z ← (permExt permFlag t).run s}[r z ∧ ¬ z.2.2 = true] =
        Pr{let z ← (permExt funFlag t).run s}[r z ∧ ¬ z.2.2 = true] := by
    intro t s _ r
    rcases t with n | q'
    · rfl
    · exact permFlag_funFlag_agree q' s r
  have hmono₁ := flag_mono (S := SpState Dg E C) permFlag (Or.inl rfl)
  have hmono₂ := flag_mono (S := SpState Dg E C) funFlag (Or.inr rfl)
  rw [hperm.prEvent_eq, hfun, StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map]
  constructor
  · refine (prEvent_run_le_add_bad (permExt permFlag) (permExt funFlag) (fun s ↦ s.2 = true)
      hagree hmono₁ hmono₂ D' _ p).trans ?_
    gcongr
    exact prEvent_flag_le funFlag (Or.inr rfl) D' q hD'
  · refine (prEvent_run_le_add_bad (permExt funFlag) (permExt permFlag) (fun s ↦ s.2 = true)
      (fun t s hs r ↦ (hagree t s hs r).symm) hmono₂ hmono₁ D' _ p).trans ?_
    gcongr
    exact prEvent_flag_le permFlag (Or.inl rfl) D' q hD'

end Setting

end Common
