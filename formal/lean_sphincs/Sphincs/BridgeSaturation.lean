import Sphincs.BridgeDebt
import Sphincs.SecurityHiddenCost
import SphincsBase.Proof.Fts.PrimitiveMessagePotential

/-! A saturating potential on the lazy comparison. Every hash input has at most one target:
none, a fixed digest, or the table value of a hidden coordinate. A guess at an unexposed
coordinate, and an answer whose target is still hidden, become debts of that coordinate; they
are resolved, with exact probability, when the coordinate is sampled. Fixed targets are hit
immediately with probability 2^-128. Composing these hazards multiplicatively keeps the x^2
slack of the bound 1 - (1 - 2^-128)^(2q). The saturation theorem, with weighted payments, is in
`BridgeSatW`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenDebt

open HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance saturationDecEqInput : DecidableEq D := Classical.decEq _
noncomputable local instance saturationDecEqCoordinate : DecidableEq ι := Classical.decEq _

/-- The single possible target of a hash input. -/
inductive TargetKind (ι : Type) where
  | none
  | fixed (value : Digest)
  | hidden (coordinate : ι)

/-- How answers are compared with targets, which inputs have which target, and which inputs are
message-digest queries paying the FORS baseline. -/
structure Targeting (D R ι : Type) where
  trunc : R → Digest
  kind : D → TargetKind ι
  digest : D → Prop

variable (tg : Targeting D R ι) (initial : Cache D R)

/-- Values whose exposure at a coordinate would complete a hit: recorded guesses, and truncated
answers of new inputs whose target is that coordinate. -/
def debts (state : DebtState D R ι) (coordinate : ι) : Set Digest :=
  {value | (coordinate, value) ∈ state.guesses} ∪
    {value | ∃ input output, state.cache input = some output ∧ initial input = none ∧
      tg.kind input = .hidden coordinate ∧ tg.trunc output = value}

/-- A new answer equals its fixed target. -/
def FixedHit (state : DebtState D R ι) : Prop :=
  ∃ input output value, state.cache input = some output ∧ initial input = none ∧
    tg.kind input = .fixed value ∧ tg.trunc output = value

/-- A hit already decided by the current state. -/
def Realized (state : DebtState D R ι) : Prop :=
  FixedHit tg initial state ∨ ∃ coordinate value, state.known coordinate = some value ∧
    value ∈ debts tg initial state coordinate

/-- The final hit event once the unexposed coordinates are completed by a table. -/
def Hit (table : ι → Digest) (state : DebtState D R ι) : Prop :=
  Realized tg initial state ∨ ∃ coordinate, state.known coordinate = none ∧
    table coordinate ∈ debts tg initial state coordinate

/-- Number of digests. -/
noncomputable def space : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 128

/-- Probability that completing the unexposed coordinates avoids every debt. -/
noncomputable def survival (state : DebtState D R ι) : ℝ≥0∞ :=
  ∏ coordinate, if state.known coordinate = none then
    1 - ((debts tg initial state coordinate).encard : ℝ≥0∞) / space else 1

theorem card_digest : Fintype.card Digest = 2 ^ 128 := by
  simp [Digest, digestBits]

/-- **Exact avoidance.** Completing a knowledge cache avoids finite sets at its unexposed
coordinates with the product probability. -/
theorem completion_avoid (known : Knowledge ι) (avoid : ι → Finset Digest) :
    Pr{let table ← completion known}[∀ coordinate, known coordinate = none → table coordinate ∉ avoid coordinate] =
      ∏ coordinate, if known coordinate = none then
        (((Fintype.card Digest - (avoid coordinate).card : Nat) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞))
        else 1 := by
  classical
  let allowed : ι → Finset Digest := fun coordinate =>
    if known coordinate = none then Finset.univ \ avoid coordinate else Finset.univ
  have hset : (Finset.univ.filter (fun fresh : ι → Digest =>
      ∀ coordinate, known coordinate = none → tableExtending known fresh coordinate ∉ avoid coordinate)) =
      Fintype.piFinset allowed := by
    ext fresh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, allowed]
    constructor
    · intro h coordinate
      by_cases hc : known coordinate = none
      · rw [ite_eq_left hc, Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        have := h coordinate hc
        simpa [tableExtending, hc] using this
      · rw [ite_eq_right hc]
        exact Finset.mem_univ _
    · intro h coordinate hc
      have := h coordinate
      rw [ite_eq_left hc, Finset.mem_sdiff] at this
      simpa [tableExtending, hc] using this.2
  rw [completion, prEvent_map, @SampleableType.prEvent_uniformSample _ HiddenReveal.tableSampleable, hset, Fintype.card_piFinset, Fintype.card_fun]
  rw [Nat.cast_prod, Nat.cast_pow, show ((Fintype.card Digest : ℝ≥0∞)) ^ (Fintype.card ι) =
      ∏ _coordinate : ι, (Fintype.card Digest : ℝ≥0∞) by rw [Finset.prod_const, Finset.card_univ],
    ← ENNReal.prod_div_distrib_of_ne_zero]
  · refine Finset.prod_congr rfl fun coordinate _ => ?_
    by_cases hc : known coordinate = none
    · simp only [allowed, ite_eq_left hc, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    · simp only [allowed, ite_eq_right hc, Finset.card_univ]
      exact ENNReal.div_self (by simp) (by simp)
  · intro coordinate _
    simp

/-! ### How debts change -/

omit [Fintype ι] [SampleableType R] in
theorem debts_record (state : DebtState D R ι) (guess : ι × Digest) (coordinate : ι) :
    debts tg initial (state.record guess) coordinate =
      if coordinate = guess.1 then insert guess.2 (debts tg initial state coordinate)
      else debts tg initial state coordinate := by
  ext value
  simp only [debts, DebtState.record, List.mem_cons, Set.mem_union, Set.mem_ofPred_eq]
  split_ifs with h
  · subst h
    simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_ofPred_eq, Prod.ext_iff]
    tauto
  · constructor
    · rintro (⟨heq | hmem⟩ | hcache)
      · exact absurd (congrArg Prod.fst heq) h
      · exact Or.inl hmem
      · exact Or.inr hcache
    · rintro (hmem | hcache)
      · exact Or.inl (Or.inr hmem)
      · exact Or.inr hcache

/-- A fresh answer stored in the cache. -/
noncomputable def DebtState.store (state : DebtState D R ι) (input : D) (output : R) : DebtState D R ι :=
  { state with cache := state.cache.cacheQuery input output }

omit [Fintype ι] [SampleableType R] in
theorem debts_store (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) (coordinate : ι) :
    debts tg initial (state.store input output) coordinate =
      if tg.kind input = .hidden coordinate then insert (tg.trunc output) (debts tg initial state coordinate)
      else debts tg initial state coordinate := by
  ext value
  simp only [debts, DebtState.store, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (hguess | ⟨other, out, hcache, hinit, hkind, htrunc⟩)
    · split_ifs <;> simp [hguess]
    · by_cases heq : other = input
      · subst other
        rw [QueryCache.cacheQuery_self] at hcache
        cases hcache
        rw [ite_eq_left hkind]
        exact Set.mem_insert_iff.mpr (Or.inl htrunc.symm)
      · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hcache
        have hold : value ∈ debts tg initial state coordinate :=
          Or.inr ⟨other, out, hcache, hinit, hkind, htrunc⟩
        split_ifs
        · exact Set.mem_insert_of_mem _ hold
        · exact hold
  · intro h
    split_ifs at h with hkind
    · rcases h with rfl | (hguess | ⟨other, out, hcache, hinit, hk, htrunc⟩)
      · exact Or.inr ⟨input, output, QueryCache.cacheQuery_self _ _ _, hinitial, hkind, rfl⟩
      · exact Or.inl hguess
      · have hne : other ≠ input := fun heq => by subst heq; simp [hfresh] at hcache
        exact Or.inr ⟨other, out, by rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hcache, hinit, hk, htrunc⟩
    · rcases h with hguess | ⟨other, out, hcache, hinit, hk, htrunc⟩
      · exact Or.inl hguess
      · have hne : other ≠ input := fun heq => by subst heq; simp [hfresh] at hcache
        exact Or.inr ⟨other, out, by rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hcache, hinit, hk, htrunc⟩

omit [Fintype ι] [SampleableType R] in
theorem debts_expose (state : DebtState D R ι) (exposed : ι) (value : Digest) (coordinate : ι) :
    debts tg initial (state.expose exposed value) coordinate = debts tg initial state coordinate := rfl

omit [Fintype ι] [SampleableType R] in
theorem fixedHit_store (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) :
    FixedHit tg initial (state.store input output) ↔
      FixedHit tg initial state ∨ ∃ value, tg.kind input = .fixed value ∧ tg.trunc output = value := by
  constructor
  · rintro ⟨other, out, value, hcache, hinit, hkind, htrunc⟩
    by_cases heq : other = input
    · subst other
      simp only [DebtState.store, QueryCache.cacheQuery_self] at hcache
      cases hcache
      exact Or.inr ⟨value, hkind, htrunc⟩
    · simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ heq] at hcache
      exact Or.inl ⟨other, out, value, hcache, hinit, hkind, htrunc⟩
  · rintro (⟨other, out, value, hcache, hinit, hkind, htrunc⟩ | ⟨value, hkind, htrunc⟩)
    · have hne : other ≠ input := fun heq => by subst heq; simp [hfresh] at hcache
      exact ⟨other, out, value, by simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hne]; exact hcache,
        hinit, hkind, htrunc⟩
    · exact ⟨input, output, value, QueryCache.cacheQuery_self _ _ _, hinitial, hkind, htrunc⟩

omit [Fintype ι] [SampleableType R] in
theorem fixedHit_record (state : DebtState D R ι) (guess : ι × Digest) :
    FixedHit tg initial (state.record guess) ↔ FixedHit tg initial state := Iff.rfl

omit [Fintype ι] [SampleableType R] in
theorem fixedHit_expose (state : DebtState D R ι) (coordinate : ι) (value : Digest) :
    FixedHit tg initial (state.expose coordinate value) ↔ FixedHit tg initial state := Iff.rfl

/-! ### Survival weight and the final completion -/

/-- Survival weight: zero once a hit is decided, else the avoidance product. -/
noncomputable def weight (state : DebtState D R ι) : ℝ≥0∞ :=
  if Realized tg initial state then 0 else survival tg initial state

theorem space_eq : space = (Fintype.card Digest : ℝ≥0∞) := by
  rw [space, card_digest]
  norm_num

omit [SampleableType R] in
/-- At the end, the survival weight is at most the probability that completion avoids a hit. -/
theorem weight_le_noHit_of (state : DebtState D R ι)
    (hfinite : ∀ coordinate, state.known coordinate = none → (debts tg initial state coordinate).Finite) :
    weight tg initial state ≤ Pr{let table ← completion state.known}[¬Hit tg initial table state] := by
  unfold weight
  split_ifs with hrealized
  · exact bot_le
  · let avoid : ι → Finset Digest := fun coordinate =>
      if h : state.known coordinate = none then (hfinite coordinate h).toFinset else ∅
    have hevent : (fun table => ¬Hit tg initial table state) =
        fun table => ∀ coordinate, state.known coordinate = none → table coordinate ∉ avoid coordinate := by
      funext table
      simp only [Hit, hrealized, false_or, not_exists, not_and]
      refine propext (forall_congr' fun coordinate => imp_congr_right fun hc => ?_)
      simp only [avoid, dite_eq_left hc, Set.Finite.mem_toFinset]
    rw [hevent, completion_avoid]
    refine le_of_eq (Finset.prod_congr rfl fun coordinate _ => ?_)
    split_ifs with hc
    · have hcard : (debts tg initial state coordinate).encard = ((avoid coordinate).card : ℕ∞) := by
        simp only [avoid, dite_eq_left hc]
        rw [Set.Finite.encard_eq_coe_toFinset_card (hfinite coordinate hc)]
      have hle : (avoid coordinate).card ≤ Fintype.card Digest := Finset.card_le_univ _
      rw [hcard, space_eq, ENat.toENNReal_coe, ENNReal.natCast_sub,
        ENNReal.sub_div (fun _ _ => by simp),
        ENNReal.div_self (by simp) (by simp)]
    · rfl

omit [SampleableType R] in
/-- At the end, the survival weight is at most the probability that completion avoids a hit. -/
theorem weight_le_noHit (state : DebtState D R ι) :
    weight tg initial state ≤ Pr{let table ← completion state.known}[¬Hit tg initial table state] := by
  by_cases hfinite : ∀ coordinate, state.known coordinate = none → (debts tg initial state coordinate).Finite
  · exact weight_le_noHit_of tg initial state hfinite
  · push Not at hfinite
    obtain ⟨coordinate, hc, hinfinite⟩ := hfinite
    have hzero : weight tg initial state = 0 := by
      unfold weight
      split_ifs
      · rfl
      · unfold survival
        refine Finset.prod_eq_zero (Finset.mem_univ coordinate) ?_
        rw [ite_eq_left hc, Set.Infinite.encard_eq hinfinite, ENat.toENNReal_top,
          ENNReal.top_div_of_ne_top (by simp [space] : space ≠ ⊤)]
        exact tsub_eq_zero_of_le le_top
    rw [hzero]
    exact bot_le

omit [SampleableType R] in
theorem weight_le_one (state : DebtState D R ι) : weight tg initial state ≤ 1 := by
  unfold weight survival
  split_ifs
  · exact zero_le_one
  · refine Finset.prod_le_one fun coordinate _ => ?_
    split_ifs
    · exact tsub_le_self
    · exact le_rfl

/-! ### Exposing a coordinate is a martingale step -/

omit [Fintype ι] [SampleableType R] in
theorem realized_expose (state : DebtState D R ι) (coordinate : ι) (value : Digest)
    (hc : state.known coordinate = none) :
    Realized tg initial (state.expose coordinate value) ↔
      Realized tg initial state ∨ value ∈ debts tg initial state coordinate := by
  simp only [Realized, fixedHit_expose, debts_expose]
  constructor
  · rintro (hfix | ⟨other, known, hk, hw⟩)
    · exact Or.inl (Or.inl hfix)
    · by_cases heq : other = coordinate
      · subst heq
        simp only [DebtState.expose, QueryCache.cacheQuery_self, Option.some.injEq] at hk
        subst hk
        exact Or.inr hw
      · simp only [DebtState.expose, QueryCache.cacheQuery_of_ne _ _ heq] at hk
        exact Or.inl (Or.inr ⟨other, known, hk, hw⟩)
  · rintro ((hfix | ⟨other, known, hk, hw⟩) | hv)
    · exact Or.inl hfix
    · have hne : other ≠ coordinate := fun h => by subst h; simp [hc] at hk
      exact Or.inr ⟨other, known, by simp only [DebtState.expose, QueryCache.cacheQuery_of_ne _ _ hne, hk], hw⟩
    · exact Or.inr ⟨coordinate, value, by simp only [DebtState.expose, QueryCache.cacheQuery_self], hv⟩

/-- The factor of one unexposed coordinate. -/
noncomputable def factor (state : DebtState D R ι) (coordinate : ι) : ℝ≥0∞ :=
  1 - ((debts tg initial state coordinate).encard : ℝ≥0∞) / space

omit [SampleableType R] in
theorem survival_expose (state : DebtState D R ι) (coordinate : ι) (value : Digest)
    (hc : state.known coordinate = none) :
    survival tg initial state = factor tg initial state coordinate *
      survival tg initial (state.expose coordinate value) := by
  unfold survival
  rw [Fintype.prod_eq_mul_prod_compl coordinate, Fintype.prod_eq_mul_prod_compl coordinate (f := fun other =>
    if (state.expose coordinate value).known other = none then
      1 - ((debts tg initial (state.expose coordinate value) other).encard : ℝ≥0∞) / space else 1)]
  simp only [hc, ite_true, DebtState.expose, QueryCache.cacheQuery_self, reduceCtorEq, ite_false, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun other hother => ?_
  have hne : other ≠ coordinate := by simpa using hother
  simp only [QueryCache.cacheQuery_of_ne _ _ hne]
  rfl

theorem prob_uniform_not_mem (set : Set Digest) (hfinite : set.Finite) :
    Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∉ set] = 1 - (set.encard : ℝ≥0∞) / space := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hfilter : (Finset.univ.filter fun value : Digest => value ∉ set) = Finset.univ \ hfinite.toFinset := by
    ext value
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Set.Finite.mem_toFinset]
  rw [hfilter, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ENNReal.natCast_sub,
    Set.Finite.encard_eq_coe_toFinset_card hfinite, ENat.toENNReal_coe, space_eq,
    ENNReal.sub_div (fun _ _ => by simp),
    ENNReal.div_self (by simp) (by simp)]

omit [SampleableType R] in
/-- **Exposure.** Sampling an unexposed coordinate leaves the survival weight unchanged in
expectation: a debt is hit with exactly its share of the space. -/
theorem weight_expose_mean (state : DebtState D R ι) (coordinate : ι)
    (hc : state.known coordinate = none) (hfinite : (debts tg initial state coordinate).Finite) :
    (∑' value, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = value] *
      weight tg initial (state.expose coordinate value)) = weight tg initial state := by
  by_cases hrealized : Realized tg initial state
  · have hzero : ∀ value, weight tg initial (state.expose coordinate value) = 0 := fun value => by
      rw [weight, ite_eq_left ((realized_expose tg initial state coordinate value hc).2 (Or.inl hrealized))]
    rw [weight, ite_eq_left hrealized]
    exact (tsum_congr fun value => by rw [hzero value, mul_zero]).trans tsum_zero
  · have hrest : ∀ value, survival tg initial (state.expose coordinate value) =
        survival tg initial (state.expose coordinate 0) := by
      intro value
      unfold survival
      refine Finset.prod_congr rfl fun other _ => ?_
      by_cases heq : other = coordinate
      · subst heq
        simp [DebtState.expose, QueryCache.cacheQuery_self]
      · simp only [DebtState.expose, QueryCache.cacheQuery_of_ne _ _ heq]
        rfl
    have hpoint : ∀ value, weight tg initial (state.expose coordinate value) =
        (if value ∈ debts tg initial state coordinate then 0 else 1) *
          survival tg initial (state.expose coordinate 0) := by
      intro value
      rw [weight, hrest]
      by_cases hv : value ∈ debts tg initial state coordinate
      · rw [ite_eq_left ((realized_expose tg initial state coordinate value hc).2 (Or.inr hv)), ite_eq_left hv, zero_mul]
      · have hnot : ¬Realized tg initial (state.expose coordinate value) := fun h =>
          ((realized_expose tg initial state coordinate value hc).1 h).elim hrealized hv
        rw [ite_eq_right hnot, ite_eq_right hv, one_mul]
    simp_rw [hpoint, ← mul_assoc]
    rw [ENNReal.tsum_mul_right]
    have hprob : (∑' value, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = value] *
        (if value ∈ debts tg initial state coordinate then 0 else 1)) =
        Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∉ debts tg initial state coordinate] := by
      rw [OracleComp.prEvent_eq_tsum_ite]
      refine tsum_congr fun value => ?_
      split_ifs <;> first | contradiction | simp only [mul_zero, mul_one]
    rw [hprob, prob_uniform_not_mem _ hfinite, weight, ite_eq_right hrealized,
      survival_expose tg initial state coordinate 0 hc]
    rfl

/-! ### A fresh answer -/

theorem space_ne_zero : space ≠ 0 := by simp [space]

theorem space_ne_top : space ≠ ⊤ := by simp [space]

/-- Averaging the factor after one more uniformly placed debt value. -/
theorem factor_insert_mean (count : ℕ) (hcount : count ≤ 2 ^ 128) :
    (count : ℝ≥0∞) / space * (1 - (count : ℝ≥0∞) / space) +
        (1 - (count : ℝ≥0∞) / space) * (1 - ((count + 1 : ℕ) : ℝ≥0∞) / space) =
      (1 - (count : ℝ≥0∞) / space) * (1 - 1 / space) := by
  set share := (count : ℝ≥0∞) / space with hshare
  set unit := (1 : ℝ≥0∞) / space with hunit
  have hle : share ≤ 1 := by
    rw [hshare, ENNReal.div_le_iff space_ne_zero space_ne_top, one_mul, space]
    exact_mod_cast hcount
  have hsucc : ((count + 1 : ℕ) : ℝ≥0∞) / space = share + unit := by
    rw [hshare, hunit, Nat.cast_succ, ENNReal.add_div]
  rw [hsucc, ← tsub_tsub]
  rcases Nat.lt_or_ge count (2 ^ 128) with hlt | hge
  · have hsharetop : share ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hunitle : unit ≤ 1 - share := by
      rw [ENNReal.le_sub_iff_add_le_right hsharetop hle, hunit, hshare, ← ENNReal.add_div,
        ENNReal.div_le_iff space_ne_zero space_ne_top, one_mul, space]
      have h : 1 + count ≤ 2 ^ 128 := by omega
      exact_mod_cast h
    have hunittop : unit ≠ ⊤ := by rw [hunit]; exact ENNReal.div_ne_top ENNReal.one_ne_top space_ne_zero
    rw [mul_comm share, ← mul_add, add_comm share, ENNReal.sub_add_eq_add_sub hunitle hunittop,
      tsub_add_cancel_of_le hle]
  · have heq : count = 2 ^ 128 := le_antisymm hcount hge
    have hzero : 1 - share = 0 := by
      rw [hshare, heq, space, Nat.cast_pow, Nat.cast_ofNat, ENNReal.div_self (by simp) (by simp), tsub_self]
    simp only [hzero, mul_zero, zero_mul, add_zero, zero_tsub]

/-- Truncation of a uniform answer is uniform. -/
def UniformTruncation : Prop :=
  (tg.trunc <$> ($ᵗ R : ProbComp R)) =ᵈ ($ᵗ Digest : ProbComp Digest)

omit [Fintype ι] in
theorem truncation_mean (htrunc : UniformTruncation (R := R) tg) (φ : Digest → ℝ≥0∞) :
    ∑' output, Pr{let x ← ($ᵗ R : ProbComp R)}[x = output] * φ (tg.trunc output) =
      ∑' value, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = value] * φ value := by
  rw [← OracleComp.tsum_prEvent_map_mul]
  refine tsum_congr fun value => ?_
  rw [htrunc.prEvent_eq]

theorem prob_uniform_mem (set : Set Digest) (hfinite : set.Finite) :
    Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∈ set] = (set.encard : ℝ≥0∞) / space := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hfilter : (Finset.univ.filter fun value : Digest => value ∈ set) = hfinite.toFinset := by
    ext value
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.Finite.mem_toFinset]
  rw [hfilter, Set.Finite.encard_eq_coe_toFinset_card hfinite, ENat.toENNReal_coe, space_eq]

/-- A uniform digest falls in a set or not: the mean of a two-valued function. -/
theorem uniform_split (set : Set Digest) (inside outside : ℝ≥0∞) :
    (∑' value, Pr{let x ← ($ᵗ Digest : ProbComp Digest)}[x = value] * (if value ∈ set then inside else outside)) =
      Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∈ set] * inside +
        Pr{let value ← ($ᵗ Digest : ProbComp Digest)}[value ∉ set] * outside := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add]
  refine tsum_congr fun value => ?_
  split_ifs <;> first | contradiction | simp only [zero_mul, add_zero, zero_add]

omit [SampleableType R] in
theorem survival_split (state : DebtState D R ι) (coordinate : ι) :
    survival tg initial state = (if state.known coordinate = none then factor tg initial state coordinate else 1) *
      ∏ other ∈ ({coordinate}ᶜ : Finset ι), (if state.known other = none then
        factor tg initial state other else 1) := by
  unfold survival factor
  exact Fintype.prod_eq_mul_prod_compl coordinate _

omit [SampleableType R] in
theorem survival_store_eq (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none)
    (hkind : ∀ coordinate, tg.kind input = .hidden coordinate → state.known coordinate ≠ none) :
    survival tg initial (state.store input output) = survival tg initial state := by
  unfold survival
  refine Finset.prod_congr rfl fun coordinate _ => ?_
  have hknown : (state.store input output).known = state.known := rfl
  rw [hknown]
  split_ifs with hc
  · rw [debts_store tg initial state input output hfresh hinitial, ite_eq_right (fun h => hkind coordinate h hc)]
  · rfl

omit [Fintype ι] [SampleableType R] in
theorem realized_store_of_none (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) (hkind : tg.kind input = .none) :
    Realized tg initial (state.store input output) ↔ Realized tg initial state := by
  have hknown : (state.store input output).known = state.known := rfl
  simp only [Realized, fixedHit_store tg initial state input output hfresh hinitial, hkind,
    debts_store tg initial state input output hfresh hinitial, reduceCtorEq, ite_false, false_and,
    exists_false, or_false, hknown]

/-- The truncated values that a fresh answer must avoid, given its target. -/
def Fatal : TargetKind ι → Knowledge ι → Digest → Prop
  | .none, _, _ => False
  | .fixed value, _, output => output = value
  | .hidden coordinate, known, output => known coordinate = some output

omit [Fintype ι] [SampleableType R] in
theorem realized_store (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) :
    Realized tg initial (state.store input output) ↔
      Realized tg initial state ∨ Fatal (tg.kind input) state.known (tg.trunc output) := by
  have hknown : (state.store input output).known = state.known := rfl
  unfold Realized
  rw [fixedHit_store tg initial state input output hfresh hinitial, hknown]
  simp only [debts_store tg initial state input output hfresh hinitial]
  cases hk : tg.kind input with
  | none => simp [Fatal]
  | fixed value =>
      simp only [reduceCtorEq, ite_false, TargetKind.fixed.injEq, exists_eq_left', Fatal]
      exact or_right_comm
  | hidden coordinate =>
      simp only [reduceCtorEq, false_and, exists_false, or_false, TargetKind.hidden.injEq, Fatal]
      constructor
      · rintro (hfix | ⟨other, known, hk', hv⟩)
        · exact Or.inl (Or.inl hfix)
        · split_ifs at hv with hcc
          · subst hcc
            rcases Set.mem_insert_iff.1 hv with rfl | hmem
            · exact Or.inr hk'
            · exact Or.inl (Or.inr ⟨coordinate, known, hk', hmem⟩)
          · exact Or.inl (Or.inr ⟨other, known, hk', hv⟩)
      · rintro ((hfix | ⟨other, known, hk', hv⟩) | hfatal)
        · exact Or.inl hfix
        · refine Or.inr ⟨other, known, hk', ?_⟩
          split_ifs
          · exact Set.mem_insert_of_mem _ hv
          · exact hv
        · exact Or.inr ⟨coordinate, tg.trunc output, hfatal, by rw [ite_eq_left rfl]; exact Set.mem_insert _ _⟩

/-- The survival factors of all coordinates but one. -/
noncomputable def rest (state : DebtState D R ι) (coordinate : ι) : ℝ≥0∞ :=
  ∏ other ∈ ({coordinate}ᶜ : Finset ι), (if state.known other = none then factor tg initial state other else 1)

omit [SampleableType R] in
theorem survival_split' (state : DebtState D R ι) (coordinate : ι) :
    survival tg initial state = (if state.known coordinate = none then factor tg initial state coordinate else 1) *
      rest tg initial state coordinate := survival_split tg initial state coordinate

omit [SampleableType R] in
theorem survival_store_hidden (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) (coordinate : ι)
    (hk : tg.kind input = .hidden coordinate) (hc : state.known coordinate = none) :
    survival tg initial (state.store input output) =
      (1 - ((insert (tg.trunc output) (debts tg initial state coordinate)).encard : ℝ≥0∞) / space) *
        rest tg initial state coordinate := by
  have hknown : (state.store input output).known = state.known := rfl
  rw [survival_split' tg initial _ coordinate, hknown, ite_eq_left hc, factor,
    debts_store tg initial state input output hfresh hinitial, ite_eq_left hk]
  congr 1
  refine Finset.prod_congr rfl fun other hother => ?_
  have hne : other ≠ coordinate := by simpa using hother
  simp only [hknown, factor, debts_store tg initial state input output hfresh hinitial, hk,
    TargetKind.hidden.injEq, hne.symm, ite_false]

theorem tsum_uniform_const (value : ℝ≥0∞) :
    ∑' output, Pr{let x ← ($ᵗ R : ProbComp R)}[x = output] * value = value := by
  rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one _, one_mul]

/-- **Fresh answer.** Storing a fresh uniform answer keeps at least a `1 - 2^-128` share of the
survival weight in expectation, whatever its target. -/
theorem weight_store_mean (htrunc : UniformTruncation (R := R) tg) (state : DebtState D R ι)
    (input : D) (hfresh : state.cache input = none) (hinitial : initial input = none)
    (hfinite : ∀ coordinate, (debts tg initial state coordinate).Finite) :
    (1 - 1 / space) * weight tg initial state ≤
      ∑' output, Pr{let x ← ($ᵗ R : ProbComp R)}[x = output] * weight tg initial (state.store input output) := by
  by_cases hrealized : Realized tg initial state
  · rw [weight, ite_eq_left hrealized, mul_zero]
    exact bot_le
  have hweight : ∀ output, weight tg initial (state.store input output) =
      if Fatal (tg.kind input) state.known (tg.trunc output) then 0
      else survival tg initial (state.store input output) := by
    intro output
    rw [weight]
    simp only [realized_store tg initial state input output hfresh hinitial, hrealized, false_or]
  simp_rw [hweight]
  rw [weight, ite_eq_right hrealized]
  -- one fatal truncated value, survival unchanged
  have hone : ∀ fatal : Digest, (∀ output, Fatal (tg.kind input) state.known (tg.trunc output) ↔
      tg.trunc output = fatal) → (∀ output, survival tg initial (state.store input output) =
        survival tg initial state) →
      (1 - 1 / space) * survival tg initial state ≤ ∑' output, Pr{let x ← ($ᵗ R : ProbComp R)}[x = output] *
        (if Fatal (tg.kind input) state.known (tg.trunc output) then 0
          else survival tg initial (state.store input output)) := by
    intro fatal hfatal hsame
    simp_rw [hfatal, hsame]
    have hmean := truncation_mean tg htrunc (fun value => if value = fatal then 0 else survival tg initial state)
    rw [hmean]
    have hsplit := uniform_split ({fatal} : Set Digest) 0 (survival tg initial state)
    simp only [Set.mem_singleton_iff] at hsplit
    have hnot := prob_uniform_not_mem ({fatal} : Set Digest) (Set.finite_singleton _)
    simp only [Set.mem_singleton_iff, Set.encard_singleton] at hnot
    rw [hsplit, mul_zero, zero_add, hnot]
    simp
  cases hk : tg.kind input with
  | none =>
      have hsame : ∀ output, survival tg initial (state.store input output) = survival tg initial state :=
        fun output => survival_store_eq tg initial state input output hfresh hinitial
          (fun coordinate h => by rw [hk] at h; cases h)
      simp only [Fatal, ite_false, hsame, tsum_uniform_const]
      exact mul_le_of_le_one_left' tsub_le_self
  | fixed value =>
      rw [hk] at hone
      exact hone value (fun output => Iff.rfl) fun output =>
        survival_store_eq tg initial state input output hfresh hinitial
          (fun coordinate h => by rw [hk] at h; cases h)
  | hidden coordinate =>
      cases hc : state.known coordinate with
      | some value =>
          rw [hk] at hone
          exact hone value (fun output => by simp only [Fatal, hc, Option.some.injEq]; exact eq_comm)
            fun output => survival_store_eq tg initial state input output hfresh hinitial
              (fun other h => by rw [hk] at h; cases h; rw [hc]; simp)
      | none =>
          have hnot : ∀ output, ¬Fatal (TargetKind.hidden coordinate) state.known (tg.trunc output) := by
            intro output h
            simp [Fatal, hc] at h
          simp only [hnot, ite_false]
          simp_rw [survival_store_hidden tg initial state input _ hfresh hinitial coordinate hk hc]
          have hmean := truncation_mean tg htrunc (fun value =>
            (1 - ((insert value (debts tg initial state coordinate)).encard : ℝ≥0∞) / space) *
              rest tg initial state coordinate)
          rw [hmean]
          set debt := debts tg initial state coordinate with hdebt
          set count := (hfinite coordinate).toFinset.card with hcount
          have hencard : (debt.encard : ℝ≥0∞) = (count : ℝ≥0∞) := by
            rw [Set.Finite.encard_eq_coe_toFinset_card (hfinite coordinate), ENat.toENNReal_coe]
          have hpoint : ∀ value, (1 - ((insert value debt).encard : ℝ≥0∞) / space) *
              rest tg initial state coordinate =
              if value ∈ debt then (1 - (count : ℝ≥0∞) / space) * rest tg initial state coordinate
              else (1 - ((count + 1 : ℕ) : ℝ≥0∞) / space) * rest tg initial state coordinate := by
            intro value
            split_ifs with hv
            · rw [Set.insert_eq_of_mem hv, hencard]
            · rw [Set.encard_insert_of_notMem hv, ENat.toENNReal_add, hencard]
              push_cast
              rfl
          simp_rw [hpoint]
          rw [uniform_split, prob_uniform_mem _ (hfinite coordinate),
            prob_uniform_not_mem _ (hfinite coordinate), hencard, survival_split' tg initial state coordinate,
            ite_eq_left hc, factor, hencard]
          have hle : count ≤ 2 ^ 128 := by
            rw [hcount, ← card_digest]
            exact Finset.card_le_univ _
          have hmean := factor_insert_mean count hle
          refine le_of_eq ?_
          calc (1 - 1 / space) * ((1 - (count : ℝ≥0∞) / space) * rest tg initial state coordinate)
              = ((1 - (count : ℝ≥0∞) / space) * (1 - 1 / space)) * rest tg initial state coordinate := by ring
            _ = _ := by rw [← hmean]; ring

/-! ### Real-valued budget -/

/-- The space size as a real number. -/
noncomputable def spaceReal : ℝ := (2 : ℝ) ^ 128

theorem spaceReal_pos : 0 < spaceReal := by unfold spaceReal; positivity

theorem space_eq_ofReal : space = ENNReal.ofReal spaceReal := by
  rw [space, spaceReal, ENNReal.ofReal_pow (by norm_num)]
  simp

theorem oneSub_div_space (count : ℕ) (hcount : count ≤ 2 ^ 128) :
    1 - (count : ℝ≥0∞) / space = ENNReal.ofReal (1 - count / spaceReal) := by
  have hle : (count : ℝ) / spaceReal ≤ 1 := by
    rw [div_le_one spaceReal_pos, spaceReal]
    exact_mod_cast hcount
  rw [ENNReal.ofReal_sub _ (div_nonneg (Nat.cast_nonneg _) spaceReal_pos.le), ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos spaceReal_pos, ← space_eq_ofReal, ENNReal.ofReal_natCast]

/-- Remaining-budget weight: `((N - p - r) / (N - p))^2`, the survival of `r` further probes after
`p` probes, each of which may carry two hazards of size `1 / (N - p)`. -/
noncomputable def budget (probes remaining : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((spaceReal - probes - remaining) / (spaceReal - probes)) ^ 2)

/-- The share kept by one hazard of size `1 / (N - p)`. -/
noncomputable def probeFactor (probes : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - 1 / (spaceReal - probes))

theorem budget_le_one (probes remaining : ℕ) (hbudget : (probes + remaining : ℝ) < spaceReal) :
    budget probes remaining ≤ 1 := by
  rw [budget, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < spaceReal - probes := by linarith
  have hnum : 0 ≤ (spaceReal - probes - remaining) / (spaceReal - probes) := div_nonneg (by linarith) hden.le
  have hone : (spaceReal - probes - remaining) / (spaceReal - probes) ≤ 1 :=
    (div_le_one hden).mpr (by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)])
  nlinarith

theorem budget_succ_le (probes remaining : ℕ) (hbudget : (probes + remaining + 1 : ℝ) ≤ spaceReal) :
    budget probes (remaining + 1) ≤ budget probes remaining := by
  rw [budget, budget]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < spaceReal - probes := by linarith
  push_cast
  have hlow : 0 ≤ (spaceReal - probes - (remaining + 1)) / (spaceReal - probes) :=
    div_nonneg (by linarith) hden.le
  have hord : (spaceReal - probes - (remaining + 1)) / (spaceReal - probes) ≤
      (spaceReal - probes - remaining) / (spaceReal - probes) :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  nlinarith

theorem budget_le_of_le (probes before after : ℕ) (horder : before ≤ after)
    (hbudget : (probes + after : ℝ) ≤ spaceReal) :
    budget probes after ≤ budget probes before := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le horder
  induction extra with
  | zero => rfl
  | succ extra ih =>
      have hcast : ((before + (extra + 1) : ℕ) : ℝ) = (before + extra : ℕ) + 1 := by push_cast; ring
      rw [hcast] at hbudget
      exact (budget_succ_le probes (before + extra) (by linarith)).trans
        (ih (by omega) (by linarith))

/-- One probe step: two hazards of size `1 / (N - p)` move one unit of budget into the probe count. -/
theorem budget_probe (probes remaining : ℕ) (hbudget : (probes + remaining + 1 : ℝ) < spaceReal) :
    budget probes (remaining + 1) = probeFactor probes ^ 2 * budget (probes + 1) remaining := by
  have hden : 0 < spaceReal - probes - 1 := by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)]
  have hden' : 0 < spaceReal - probes := by linarith
  have hfactor : 0 ≤ 1 - 1 / (spaceReal - probes) := by
    rw [sub_nonneg, div_le_one hden']
    linarith
  have hden1 : spaceReal - ((probes : ℝ) + 1) ≠ 0 := by linarith
  have hden0 : spaceReal - (probes : ℝ) ≠ 0 := hden'.ne'
  rw [budget, budget, probeFactor, ← ENNReal.ofReal_pow hfactor, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  have key : (spaceReal - probes - (remaining + 1)) / (spaceReal - probes) =
      (1 - 1 / (spaceReal - probes)) * ((spaceReal - (probes + 1) - remaining) / (spaceReal - (probes + 1))) := by
    field_simp
    ring
  rw [key, mul_pow]

theorem probeFactor_le_fresh (probes : ℕ) (hprobes : (probes : ℝ) < spaceReal) :
    probeFactor probes ≤ 1 - 1 / space := by
  have hone : (1 : ℕ) ≤ 2 ^ 128 := Nat.one_le_two_pow
  have h := oneSub_div_space 1 hone
  simp only [Nat.cast_one] at h
  rw [h, probeFactor]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < spaceReal - probes := by linarith
  have : 1 / spaceReal ≤ 1 / (spaceReal - probes) :=
    one_div_le_one_div_of_le hden (by linarith [(Nat.cast_nonneg probes : (0 : ℝ) ≤ probes)])
  linarith

/-- A deterministic new debt at a coordinate with at most `p` debts keeps a `probeFactor p` share. -/
theorem probeFactor_debt (count probes : ℕ) (hcount : count ≤ probes) (hprobes : (probes : ℝ) < spaceReal) :
    probeFactor probes * (1 - (count : ℝ≥0∞) / space) ≤ 1 - ((count + 1 : ℕ) : ℝ≥0∞) / space := by
  have hspace : (probes : ℝ) + 1 ≤ spaceReal := by
    have : (probes : ℝ) < spaceReal := hprobes
    have h2 : spaceReal = ((2 ^ 128 : ℕ) : ℝ) := by norm_num [spaceReal]
    rw [h2] at this ⊢
    have : probes < 2 ^ 128 := by exact_mod_cast this
    exact_mod_cast this
  have hnat : count + 1 ≤ 2 ^ 128 := by
    have h2 : spaceReal = ((2 ^ 128 : ℕ) : ℝ) := by norm_num [spaceReal]
    rw [h2] at hspace
    have : probes + 1 ≤ 2 ^ 128 := by exact_mod_cast hspace
    omega
  rw [oneSub_div_space count (by omega), oneSub_div_space (count + 1) hnat, probeFactor,
    ← ENNReal.ofReal_mul]
  · apply ENNReal.ofReal_le_ofReal
    have hden : 0 < spaceReal - probes := by linarith
    have hc : (count : ℝ) ≤ probes := by exact_mod_cast hcount
    push_cast
    have hsp : 0 < spaceReal := spaceReal_pos
    have hden0 : spaceReal - (probes : ℝ) ≠ 0 := hden.ne'
    have hu : (1 / (spaceReal - probes)) * (spaceReal - probes) = 1 := by field_simp
    have hge : 1 ≤ (1 / (spaceReal - probes)) * (spaceReal - count) := by
      calc (1 : ℝ) = _ := hu.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have key : (1 - 1 / (spaceReal - probes)) * (1 - count / spaceReal) =
        (1 - (count + 1) / spaceReal) + (1 - (1 / (spaceReal - probes)) * (spaceReal - count)) / spaceReal := by
      field_simp
      ring
    rw [key]
    have : (1 - (1 / (spaceReal - probes)) * (spaceReal - count)) / spaceReal ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hsp.le
    linarith
  · have hden : 0 < spaceReal - probes := by linarith
    rw [sub_nonneg, div_le_one hden]
    linarith

theorem probeFactor_le_one (probes : ℕ) (hprobes : (probes : ℝ) < spaceReal) : probeFactor probes ≤ 1 :=
  (probeFactor_le_fresh probes hprobes).trans tsub_le_self

/-! ### Outside reads and guesses -/

omit [Fintype ι] in
theorem readOutside_cached (bytes : D) (state : DebtState D R ι) (output : R)
    (hc : state.cache bytes = some output) : readOutside bytes state = pure (output, state) := by
  rw [readOutside, outsideRead, QueryImpl.withCaching_run_some _ hc, map_pure]

omit [Fintype ι] in
theorem readOutside_fresh (bytes : D) (state : DebtState D R ι) (hc : state.cache bytes = none) :
    readOutside bytes state = (fun output => (output, state.store bytes output)) <$> ($ᵗ R : ProbComp R) := by
  rw [readOutside, outsideRead, QueryImpl.withCaching_run_none _ hc, Functor.map_map]
  rfl

/-- The prepared cache stays in the run cache. -/
def Prepared (state : DebtState D R ι) : Prop :=
  ∀ input output, initial input = some output → state.cache input = some output

omit [Fintype ι] [SampleableType R] in
theorem initial_none_of_fresh (state : DebtState D R ι) (hprepared : Prepared initial state) (bytes : D)
    (hc : state.cache bytes = none) : initial bytes = none := by
  cases hi : initial bytes with
  | none => rfl
  | some output =>
      have := hprepared bytes output hi
      rw [hc] at this
      cases this

theorem weight_readOutside_mean (htrunc : UniformTruncation (R := R) tg) (bytes : D) (state : DebtState D R ι)
    (hprepared : Prepared initial state) (hfinite : ∀ coordinate, (debts tg initial state coordinate).Finite) :
    (1 - 1 / space) * weight tg initial state ≤
      ∑' result, Pr{let x ← readOutside bytes state}[x = result] * weight tg initial result.2 := by
  cases hc : state.cache bytes with
  | some output =>
      rw [readOutside_cached bytes state output hc, OracleComp.tsum_prEvent_pure_mul]
      exact mul_le_of_le_one_left' tsub_le_self
  | none =>
      rw [readOutside_fresh bytes state hc, OracleComp.tsum_prEvent_map_mul]
      exact weight_store_mean tg initial htrunc state bytes hc
        (initial_none_of_fresh initial state hprepared bytes hc) hfinite

omit [Fintype ι] in
theorem readOutside_support (bytes : D) (state : DebtState D R ι) (result : R × DebtState D R ι)
    (hresult : result ∈ support (readOutside bytes state)) :
    result.2 = state ∨ (state.cache bytes = none ∧ result.2 = state.store bytes result.1) := by
  cases hc : state.cache bytes with
  | some output =>
      rw [readOutside_cached bytes state output hc, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      exact Or.inl rfl
  | none =>
      rw [readOutside_fresh bytes state hc, support_map] at hresult
      obtain ⟨output, _, rfl⟩ := hresult
      exact Or.inr ⟨rfl, rfl⟩

omit [Fintype ι] [SampleableType R] in
theorem realized_record (state : DebtState D R ι) (guess : ι × Digest) (hc : state.known guess.1 = none) :
    Realized tg initial (state.record guess) ↔ Realized tg initial state := by
  have hknown : (state.record guess).known = state.known := rfl
  unfold Realized
  rw [fixedHit_record, hknown]
  simp only [debts_record]
  constructor
  · rintro (hfix | ⟨other, value, hk, hv⟩)
    · exact Or.inl hfix
    · split_ifs at hv with hother
      · subst hother
        rw [hc] at hk
        cases hk
      · exact Or.inr ⟨other, value, hk, hv⟩
  · rintro (hfix | ⟨other, value, hk, hv⟩)
    · exact Or.inl hfix
    · refine Or.inr ⟨other, value, hk, ?_⟩
      split_ifs
      · exact Set.mem_insert_of_mem _ hv
      · exact hv

omit [SampleableType R] in
theorem survival_record (state : DebtState D R ι) (guess : ι × Digest) (hc : state.known guess.1 = none) :
    survival tg initial (state.record guess) =
      (1 - ((insert guess.2 (debts tg initial state guess.1)).encard : ℝ≥0∞) / space) *
        rest tg initial state guess.1 := by
  have hknown : (state.record guess).known = state.known := rfl
  rw [survival_split' tg initial _ guess.1, hknown, ite_eq_left hc, factor, debts_record, ite_eq_left rfl]
  congr 1
  unfold rest
  refine Finset.prod_congr rfl fun other hother => ?_
  have hne : other ≠ guess.1 := by simpa using hother
  simp only [hknown, factor, debts_record, hne, ite_false]

omit [SampleableType R] in
/-- **Guess.** Recording a guess at an unexposed coordinate with at most `p` debts keeps a
`probeFactor p` share of the survival weight. -/
theorem weight_record (state : DebtState D R ι) (guess : ι × Digest) (hc : state.known guess.1 = none)
    (hfinite : (debts tg initial state guess.1).Finite) (probes : ℕ)
    (hcount : (debts tg initial state guess.1).encard ≤ probes) (hprobes : (probes : ℝ) < spaceReal) :
    probeFactor probes * weight tg initial state ≤ weight tg initial (state.record guess) := by
  by_cases hrealized : Realized tg initial state
  · rw [weight, ite_eq_left hrealized, mul_zero]
    exact bot_le
  rw [weight, weight, ite_eq_right hrealized, ite_eq_right (by rwa [realized_record tg initial state guess hc]),
    survival_record tg initial state guess hc, survival_split' tg initial state guess.1, ite_eq_left hc, factor,
    ← mul_assoc]
  refine mul_le_mul_left ?_ _
  set count := hfinite.toFinset.card with hcountdef
  have hencard : ((debts tg initial state guess.1).encard : ℝ≥0∞) = (count : ℝ≥0∞) := by
    rw [Set.Finite.encard_eq_coe_toFinset_card hfinite, ENat.toENNReal_coe]
  have hcount' : count ≤ probes := by
    have h : ((count : ℕ) : ℕ∞) ≤ probes := by
      rw [hcountdef, ← Set.Finite.encard_eq_coe_toFinset_card hfinite]
      exact hcount
    exact_mod_cast h
  by_cases hv : guess.2 ∈ debts tg initial state guess.1
  · rw [Set.insert_eq_of_mem hv]
    exact mul_le_of_le_one_left' (probeFactor_le_one probes hprobes)
  · rw [Set.encard_insert_of_notMem hv, ENat.toENNReal_add, hencard]
    have h := probeFactor_debt count probes hcount' hprobes
    push_cast at h ⊢
    exact h

/-! ### The invariant -/

/-- Invariant after `probes` hazardous queries: at most `probes` debts per coordinate, at most
`2 * probes` debts in total, and the prepared cache is kept. -/
structure Inv (state : DebtState D R ι) (probes : ℕ) : Prop where
  finite : ∀ coordinate, (debts tg initial state coordinate).Finite
  bound : ∀ coordinate, (debts tg initial state coordinate).encard ≤ probes
  total : ∑ coordinate, ((debts tg initial state coordinate).encard : ℝ≥0∞) ≤ 2 * probes
  prepared : Prepared initial state

/-- Debt growth from one state to the next, coordinate by coordinate. -/
def Growth (before after : DebtState D R ι) (extra : ι → ℕ) : Prop :=
  ∀ coordinate, (debts tg initial after coordinate).encard ≤
    (debts tg initial before coordinate).encard + extra coordinate

omit [Fintype ι] [SampleableType R] in
theorem Growth.refl (state : DebtState D R ι) : Growth tg initial state state 0 :=
  fun _ => le_self_add

omit [Fintype ι] [SampleableType R] in
theorem Growth.trans {first second third : DebtState D R ι} {extra extra' : ι → ℕ}
    (h : Growth tg initial first second extra) (h' : Growth tg initial second third extra') :
    Growth tg initial first third (extra + extra') := fun coordinate => by
  calc _ ≤ _ := h' coordinate
    _ ≤ (debts tg initial first coordinate).encard + extra coordinate + extra' coordinate := by
        gcongr
        exact h coordinate
    _ = _ := by simp [add_assoc]

omit [Fintype ι] [SampleableType R] in
theorem growth_record (state : DebtState D R ι) (guess : ι × Digest) :
    Growth tg initial state (state.record guess) (fun coordinate => if coordinate = guess.1 then 1 else 0) := by
  intro coordinate
  dsimp only
  rw [debts_record]
  split_ifs
  · simpa using Set.encard_insert_le _ _
  · simp

omit [Fintype ι] [SampleableType R] in
theorem growth_store (state : DebtState D R ι) (input : D) (output : R)
    (hfresh : state.cache input = none) (hinitial : initial input = none) :
    Growth tg initial state (state.store input output)
      (fun coordinate => if tg.kind input = .hidden coordinate then 1 else 0) := by
  intro coordinate
  dsimp only
  rw [debts_store tg initial state input output hfresh hinitial]
  split_ifs
  · simpa using Set.encard_insert_le _ _
  · simp

omit [Fintype ι] [SampleableType R] in
theorem prepared_store (state : DebtState D R ι) (hprepared : Prepared initial state) (input : D) (output : R)
    (hfresh : state.cache input = none) : Prepared initial (state.store input output) := by
  intro other value hother
  by_cases heq : other = input
  · subst heq
    rw [hprepared other value hother] at hfresh
    cases hfresh
  · simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ heq]
    exact hprepared other value hother

omit [SampleableType R] in
theorem Inv.same {state state' : DebtState D R ι} {probes : ℕ} (hinv : Inv tg initial state probes)
    (hdebts : ∀ coordinate, debts tg initial state' coordinate = debts tg initial state coordinate)
    (hprepared : Prepared initial state') : Inv tg initial state' probes where
  finite coordinate := by rw [hdebts]; exact hinv.finite coordinate
  bound coordinate := by rw [hdebts]; exact hinv.bound coordinate
  total := by simp only [hdebts]; exact hinv.total
  prepared := hprepared

omit [SampleableType R] in
theorem Inv.expose {state : DebtState D R ι} {probes : ℕ} (hinv : Inv tg initial state probes)
    (coordinate : ι) (value : Digest) : Inv tg initial (state.expose coordinate value) probes :=
  hinv.same tg initial (fun _ => rfl) hinv.prepared

omit [SampleableType R] in
theorem Inv.mono {state : DebtState D R ι} {probes probes' : ℕ} (hinv : Inv tg initial state probes)
    (hle : probes ≤ probes') : Inv tg initial state probes' where
  finite := hinv.finite
  bound coordinate := (hinv.bound coordinate).trans (by exact_mod_cast hle)
  total := hinv.total.trans (by gcongr)
  prepared := hinv.prepared

omit [SampleableType R] in
theorem Inv.grow {state state' : DebtState D R ι} {probes : ℕ} {extra : ι → ℕ}
    (hinv : Inv tg initial state probes) (hgrowth : Growth tg initial state state' extra)
    (hone : ∀ coordinate, extra coordinate ≤ 1) (htwo : ∑ coordinate, extra coordinate ≤ 2)
    (hprepared : Prepared initial state') : Inv tg initial state' (probes + 1) where
  finite coordinate := by
    have hlt : (debts tg initial state' coordinate).encard < ⊤ :=
      (hgrowth coordinate).trans_lt (ENat.add_lt_top.mpr ⟨(hinv.finite coordinate).encard_lt_top,
        ENat.natCast_lt_top _⟩)
    exact Set.encard_lt_top_iff.mp hlt
  bound coordinate := by
    calc _ ≤ _ := hgrowth coordinate
      _ ≤ (probes : ℕ∞) + 1 := add_le_add (hinv.bound coordinate) (by exact_mod_cast hone coordinate)
      _ = _ := by push_cast; rfl
  total := by
    calc ∑ coordinate, ((debts tg initial state' coordinate).encard : ℝ≥0∞)
        ≤ ∑ coordinate, (((debts tg initial state coordinate).encard : ℝ≥0∞) + (extra coordinate : ℝ≥0∞)) := by
          gcongr with coordinate
          have h := hgrowth coordinate
          calc ((debts tg initial state' coordinate).encard : ℝ≥0∞)
              ≤ (((debts tg initial state coordinate).encard + extra coordinate : ℕ∞) : ℝ≥0∞) :=
                ENat.toENNReal_le.mpr h
            _ = _ := by rw [ENat.toENNReal_add]; rfl
      _ = ∑ coordinate, ((debts tg initial state coordinate).encard : ℝ≥0∞) +
          ((∑ coordinate, extra coordinate : ℕ) : ℝ≥0∞) := by rw [Finset.sum_add_distrib]; push_cast; rfl
      _ ≤ 2 * probes + 2 := add_le_add hinv.total (by exact_mod_cast htwo)
      _ = _ := by push_cast; ring
  prepared := hprepared

/-! ### The monitored lazy run -/

section Monitor

open HiddenCost

variable (model : HiddenRows.Model D R A ι)

/-- One lazy comparison step on the cost interface; ticks change nothing. -/
noncomputable def costStep : (input : (SourceCostSpec D R ι).Domain) → DebtState D R ι →
    ProbComp ((SourceCostSpec D R ι).Range input × DebtState D R ι)
  | .inl input, state => (lazyStep model input).run state
  | .inr _, state => pure ((), state)

/-- A digest query pays the baseline exactly when no hit is decided yet. -/
noncomputable def pays (state : DebtState D R ι) : (SourceCostSpec D R ι).Domain → ℕ
  | .inl (.inr (.inl bytes)) => if tg.digest bytes ∧ ¬Realized tg initial state then 1 else 0
  | _ => 0

/-- The lazy comparison with the number of baseline payments. -/
noncomputable def monitor {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    DebtState D R ι → ProbComp ((α × DebtState D R ι) × ℕ) :=
  OracleComp.construct (fun value state => pure ((value, state), 0))
    (fun input _ next state => costStep model input state >>= fun result =>
      (fun out => (out.1, pays tg initial state input + out.2)) <$> next result.1 result.2) computation

omit [Fintype ι] [SampleableType R] in
theorem erase_query_bind_inl {α : Type} (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    erase (liftM ((SourceCostSpec D R ι).query (.inl input)) >>= next) =
      liftM ((HiddenRows.SourceSpec D R ι).query input) >>= fun value => erase (next value) := by
  simp only [erase, simulateQ_bind, simulateQ_spec_query]
  rfl

omit [Fintype ι] [SampleableType R] in
theorem erase_query_bind_inr {α : Type} (amount : ℕ)
    (next : Unit → OracleComp (SourceCostSpec D R ι) α) :
    erase (liftM ((SourceCostSpec D R ι).query (.inr amount)) >>= next) = erase (next ()) := by
  simp only [erase, simulateQ_bind, simulateQ_spec_query]
  rfl

end Monitor

/-! ### Step facts -/

section Steps

open HiddenCost

variable (model : HiddenRows.Model D R A ι)

/-- Mean survival weight after one step. -/
noncomputable def meanWeight {β : Type} (step : ProbComp (β × DebtState D R ι)) : ℝ≥0∞ :=
  ∑' result, Pr{let x ← step}[x = result] * weight tg initial result.2

omit [Fintype ι] [SampleableType R] in
theorem sampleCoordinate_known (coordinate : ι) (state : DebtState D R ι) (value : Digest)
    (hc : state.known coordinate = some value) : sampleCoordinate coordinate state = pure (value, state) := by
  rw [sampleCoordinate, QueryImpl.withCaching_run_some _ hc, map_pure]

omit [Fintype ι] [SampleableType R] in
theorem sampleCoordinate_unknown (coordinate : ι) (state : DebtState D R ι) (hc : state.known coordinate = none) :
    sampleCoordinate coordinate state =
      (fun value => (value, state.expose coordinate value)) <$> ($ᵗ Digest : ProbComp Digest) := by
  rw [sampleCoordinate, QueryImpl.withCaching_run_none _ hc, Functor.map_map]
  rfl

omit [SampleableType R] in
theorem meanWeight_sample (coordinate : ι) (state : DebtState D R ι)
    (hfinite : (debts tg initial state coordinate).Finite) :
    meanWeight tg initial (sampleCoordinate coordinate state) = weight tg initial state := by
  cases hc : state.known coordinate with
  | none =>
      rw [meanWeight, sampleCoordinate_unknown coordinate state hc, OracleComp.tsum_prEvent_map_mul]
      exact weight_expose_mean tg initial state coordinate hc hfinite
  | some value => rw [meanWeight, sampleCoordinate_known coordinate state value hc, OracleComp.tsum_prEvent_pure_mul]

omit [SampleableType R] in
theorem meanWeight_map {β γ : Type} (f : β → γ) (step : ProbComp (β × DebtState D R ι)) :
    meanWeight tg initial ((fun result => (f result.1, result.2)) <$> step) = meanWeight tg initial step := by
  rw [meanWeight, meanWeight, OracleComp.tsum_prEvent_map_mul]

theorem meanWeight_readOutside_none (bytes : D) (state : DebtState D R ι) (hk : tg.kind bytes = .none)
    (hprepared : Prepared initial state) :
    meanWeight tg initial (readOutside bytes state) = weight tg initial state := by
  cases hc : state.cache bytes with
  | some output => rw [meanWeight, readOutside_cached bytes state output hc, OracleComp.tsum_prEvent_pure_mul]
  | none =>
      rw [meanWeight, readOutside_fresh bytes state hc, OracleComp.tsum_prEvent_map_mul]
      have hinitial := initial_none_of_fresh initial state hprepared bytes hc
      have hsame : ∀ output, weight tg initial (state.store bytes output) = weight tg initial state := by
        intro output
        rw [weight, weight, survival_store_eq tg initial state bytes output hc hinitial
          (fun coordinate h => by rw [hk] at h; cases h)]
        simp only [realized_store tg initial state bytes output hc hinitial, hk, Fatal, or_false]
      simp only [hsame]
      exact tsum_uniform_const _

omit [SampleableType R] in
theorem sum_target_le (input : D) :
    ∑ coordinate, (if tg.kind input = .hidden coordinate then 1 else 0 : ℕ) ≤ 1 := by
  cases tg.kind input with
  | none => simp
  | fixed value => simp
  | hidden target => simp [TargetKind.hidden.injEq]

theorem inv_readOutside (bytes : D) (state : DebtState D R ι) (probes : ℕ) (hinv : Inv tg initial state probes)
    (result : R × DebtState D R ι) (hresult : result ∈ support (readOutside bytes state)) :
    Inv tg initial result.2 (probes + 1) := by
  rcases readOutside_support bytes state result hresult with h | ⟨hc, h⟩
  · rw [h]
    exact hinv.mono tg initial (Nat.le_succ _)
  · rw [h]
    exact hinv.grow tg initial (growth_store tg initial state bytes result.1 hc
      (initial_none_of_fresh initial state hinv.prepared bytes hc))
      (fun coordinate => by split_ifs <;> omega) ((sum_target_le tg bytes).trans (by norm_num))
      (prepared_store initial state hinv.prepared bytes result.1 hc)

theorem inv_readOutside_none (bytes : D) (state : DebtState D R ι) (probes : ℕ)
    (hinv : Inv tg initial state probes) (hk : tg.kind bytes = .none)
    (result : R × DebtState D R ι) (hresult : result ∈ support (readOutside bytes state)) :
    Inv tg initial result.2 probes := by
  rcases readOutside_support bytes state result hresult with h | ⟨hc, h⟩
  · rw [h]
    exact hinv
  · rw [h]
    have hinitial := initial_none_of_fresh initial state hinv.prepared bytes hc
    refine hinv.same tg initial (fun coordinate => ?_) (prepared_store initial state hinv.prepared bytes result.1 hc)
    rw [debts_store tg initial state bytes result.1 hc hinitial, ite_eq_right (by rw [hk]; exact fun h => by cases h)]

theorem inv_guess (bytes : D) (state : DebtState D R ι) (guess : ι × Digest) (probes : ℕ)
    (hinv : Inv tg initial state probes) (hrow : tg.kind bytes ≠ .hidden guess.1)
    (result : R × DebtState D R ι) (hresult : result ∈ support (readOutside bytes (state.record guess))) :
    Inv tg initial result.2 (probes + 1) := by
  have hprepared : Prepared initial (state.record guess) := hinv.prepared
  have hfirst := growth_record tg initial state guess
  have hone : (∑ coordinate, (if coordinate = guess.1 then 1 else 0 : ℕ)) = 1 := by simp
  rcases readOutside_support bytes _ result hresult with h | ⟨hc, h⟩
  · rw [h]
    refine hinv.grow tg initial hfirst (fun coordinate => by split_ifs <;> omega) (by rw [hone]; norm_num)
      hprepared
  · rw [h]
    have hinitial := initial_none_of_fresh initial _ hprepared bytes hc
    refine hinv.grow tg initial (hfirst.trans tg initial (growth_store tg initial _ bytes result.1 hc hinitial))
      (fun coordinate => ?_) ?_ (prepared_store initial _ hprepared bytes result.1 hc)
    · simp only [Pi.add_apply]
      by_cases hcoord : coordinate = guess.1
      · subst hcoord
        rw [ite_eq_left rfl, ite_eq_right hrow]
      · rw [ite_eq_right hcoord, zero_add]
        split_ifs <;> omega
    · simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hone]
      have := sum_target_le tg bytes
      omega

/-! ### Budget inequalities for one step -/

theorem probe_inequality (probes remaining : ℕ) (weightValue mean : ℝ≥0∞)
    (hbudget : (probes + remaining + 1 : ℝ) < spaceReal) (hmean : probeFactor probes ^ 2 * weightValue ≤ mean) :
    budget probes (remaining + 1) * weightValue ≤ budget (probes + 1) remaining * mean := by
  rw [budget_probe probes remaining hbudget, mul_comm (probeFactor probes ^ 2), mul_assoc]
  gcongr

/-- Combining one step with the induction hypothesis. -/
theorem combine {β : Type} (step : ProbComp β) (nextWeight nextPay nextEnd : β → ℝ≥0∞)
    (current payment paid nextBudget : ℝ≥0∞)
    (hstep : current + payment * paid ≤ nextBudget * ∑' x, Pr{let y ← step}[y = x] * nextWeight x)
    (hih : ∀ x ∈ support step, nextBudget * nextWeight x + payment * nextPay x ≤ nextEnd x) :
    current + payment * ∑' x, Pr{let y ← step}[y = x] * (paid + nextPay x) ≤ ∑' x, Pr{let y ← step}[y = x] * nextEnd x := by
  have hmass : ∑' x, Pr{let y ← step}[y = x] = 1 := OracleComp.tsum_prEvent_eq_one _
  calc current + payment * ∑' x, Pr{let y ← step}[y = x] * (paid + nextPay x)
      = (current + payment * paid) + ∑' x, Pr{let y ← step}[y = x] * (payment * nextPay x) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
        rw [← ENNReal.tsum_mul_left]
        simp only [mul_left_comm payment]
        ring
    _ ≤ nextBudget * (∑' x, Pr{let y ← step}[y = x] * nextWeight x) + ∑' x, Pr{let y ← step}[y = x] * (payment * nextPay x) :=
        add_le_add hstep le_rfl
    _ = ∑' x, Pr{let y ← step}[y = x] * (nextBudget * nextWeight x + payment * nextPay x) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun x => ?_
        ring
    _ ≤ ∑' x, Pr{let y ← step}[y = x] * nextEnd x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support step
        · gcongr
          exact hih x hx
        · rw [(prEvent_eq_zero_of_not_mem_support _) hx, zero_mul, zero_mul]

end Steps

/-! ### Compatible targetings and the start state -/

section Main

open HiddenCost

variable (model : HiddenRows.Model D R A ι)

/-- Conditions linking targets to the hidden-row model: a row query never targets its own
incoming coordinate, and digest queries are plain untargeted reads. -/
structure Compatible : Prop where
  row : ∀ bytes query, model.parse bytes = some query → tg.kind bytes ≠ .hidden (model.incoming query.1)
  digestKind : ∀ bytes, tg.digest bytes → tg.kind bytes = .none
  digestParse : ∀ bytes, tg.digest bytes → model.parse bytes = none

omit [Fintype ι] in
theorem costStep_inl (input : (HiddenRows.SourceSpec D R ι).Domain) (state : DebtState D R ι) :
    costStep model (.inl input) state = (lazyStep model input).run state := rfl

theorem probeFactor_sq_le (probes : ℕ) (hprobes : (probes : ℝ) < spaceReal) (weightValue : ℝ≥0∞) :
    probeFactor probes ^ 2 * weightValue ≤ (1 - 1 / space) * weightValue := by
  gcongr
  calc probeFactor probes ^ 2 = probeFactor probes * probeFactor probes := sq _
    _ ≤ 1 * probeFactor probes := by gcongr; exact probeFactor_le_one probes hprobes
    _ ≤ _ := by rw [one_mul]; exact probeFactor_le_fresh probes hprobes

theorem readOutside_step (htrunc : UniformTruncation (R := R) tg) (bytes : D) (state : DebtState D R ι)
    (probes remaining : ℕ) (hinv : Inv tg initial state probes)
    (hbudget : (probes + remaining + 1 : ℝ) < spaceReal) :
    budget probes (remaining + 1) * weight tg initial state ≤
      budget (probes + 1) remaining * meanWeight tg initial (readOutside bytes state) := by
  refine probe_inequality probes remaining _ _ hbudget ?_
  exact (probeFactor_sq_le probes (by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)]) _).trans
    (weight_readOutside_mean tg initial htrunc bytes state hinv.prepared hinv.finite)

/-- The starting state of the comparison: the prepared cache and no guesses. -/
def DebtState.start (known : Knowledge ι) : DebtState D R ι := ⟨known, initial, []⟩

omit [Fintype ι] [SampleableType R] in
theorem debts_start (known : Knowledge ι) (coordinate : ι) :
    debts tg initial (DebtState.start initial known) coordinate = ∅ := by
  ext value
  simp only [debts, DebtState.start, List.not_mem_nil, Set.ofPred_false, Set.empty_union, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro input output hcache hinitial
  rw [hcache] at hinitial
  cases hinitial

omit [SampleableType R] in
theorem inv_start (known : Knowledge ι) : Inv tg initial (DebtState.start initial known) 0 where
  finite coordinate := by rw [debts_start]; exact Set.finite_empty
  bound coordinate := by rw [debts_start]; simp
  total := by simp [debts_start]
  prepared := fun _ _ h => h

omit [SampleableType R] in
theorem weight_start (known : Knowledge ι) : weight tg initial (DebtState.start initial known) = 1 := by
  have hrealized : ¬Realized tg initial (DebtState.start initial known) := by
    rintro (⟨input, output, value, hcache, hinitial, _⟩ | ⟨coordinate, value, _, hv⟩)
    · change initial input = some output at hcache
      rw [hcache] at hinitial
      cases hinitial
    · rw [debts_start] at hv
      exact hv
  rw [weight, ite_eq_right hrealized, survival]
  refine Finset.prod_eq_one fun coordinate _ => ?_
  split_ifs
  · simp [debts_start]
  · rfl

end Main

end Sphincs.Security.HiddenDebt
