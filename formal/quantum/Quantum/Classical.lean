module

public import Common.Model
public import Quantum.Model
public import VCVio.Quantum.Oracle.ClassicalCalls
public import VCVio.OracleComp.EvalDist.Sum

@[expose] public section

/-!
# The QRPM on classical programs is the classical random-permutation model

Two facts tie the quantum random-permutation model (`Quantum.Model`) to the classical one of
`Statement/RandomPermutation.lean`.

* **Lazy sampling is uniform sampling.** For a finite `S`, an algorithm over coins, `π` and `π⁻¹`
  (`unifSpec + permutationOracleSpec S`) run against the lazily sampled permutation
  (`lazyPermOracles`, the statement's `lazyRandomPermutationOracles` at the Keccak state) from no
  edge has the output distribution of the uniform mixture, over all `|S|!` permutations `φ`, of the
  algorithm with `π = φ` and `π⁻¹ = φ⁻¹` (`eagerPermOracles φ`): `evalDist_lazy_eq`. The induction
  is on the algorithm from any edge list `E` that is a partial bijection: the lazy run is the
  average over the `(|S| - |E|)!` permutations extending `E` (`factorial_mul_prEvent_lazy`), since a
  fresh forward answer, uniform outside the range, splits the extensions of `E` into equal fibers
  (`card_permExtensions`), and likewise for an inverse answer.
* **Classical calls of the QRPM are classical queries.** `ClassicalOn R x pa Φ` says the program
  `x` runs against `R` as the sampler `pa`, each branch the probability of its value times the
  fixed map `Φ`; it is closed under sequencing (`ClassicalOn.bind`) and passes through
  `OracleComp.toQuantumAt` (`classicalOn_toQuantumAt`). The classical calls `qrpmImpl e B` (coins,
  then basis calls of `φ` and `φ⁻¹` at `e t`, read back through `e`, as `Xmss.permImpl` makes them)
  run against `permutationRuntime φ` as the fixed permutation `e⁻¹ φ e`
  (`classicalOn_qrpmImpl`). With the first fact, a program that runs classically against every
  `φ` has in the QRPM the distribution of its classical algorithm under the lazily sampled
  permutation (`qrpmEvalDistMap_of_classicalOn`), in particular every classical algorithm run by
  classical calls (`qrpmEvalDistMap_toQuantumAt_qrpmImpl`).
-/

open OracleComp OracleSpec MeasureTheory Common
open scoped ENNReal Kronecker

universe u₁ v₁

namespace Quantum

/-! ## Lazy and eager sampling of a permutation -/

section LazyEager

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The permutations of `S` that extend the edge list `E`. -/
def permExtensions (E : PermutationEdges S) : Finset (Equiv.Perm S) :=
  Finset.univ.filter fun φ ↦ ∀ e ∈ E, φ e.1 = e.2

theorem mem_permExtensions {E : PermutationEdges S} {φ : Equiv.Perm S} :
    φ ∈ permExtensions E ↔ ∀ e ∈ E, φ e.1 = e.2 := by
  simp [permExtensions]

theorem mem_permExtensions_cons {E : PermutationEdges S} {e : S × S} {φ : Equiv.Perm S} :
    φ ∈ permExtensions (e :: E) ↔ φ e.1 = e.2 ∧ φ ∈ permExtensions E := by
  simp [mem_permExtensions]

/-- Splitting the extensions of `E` by the value `pick φ` of a fresh point. -/
theorem sum_permExtensions_fiber {β : Type*} [AddCommMonoid β] {E : PermutationEdges S}
    (l : List S) (pick : Equiv.Perm S → S) (mk : S → S × S)
    (hpick : ∀ φ ∈ permExtensions E, pick φ ∉ l)
    (hmk : ∀ z φ, φ (mk z).1 = (mk z).2 ↔ pick φ = z) (f : Equiv.Perm S → β) :
    ∑ φ ∈ permExtensions E, f φ =
      ∑ z ∈ Finset.univ.filter (· ∉ l), ∑ φ ∈ permExtensions (mk z :: E), f φ := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := pick) (t := Finset.univ.filter (· ∉ l))
    fun φ hφ ↦ by simpa using hpick φ hφ]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext φ
  simp only [Finset.mem_filter, mem_permExtensions_cons, hmk]
  tauto

theorem apply_notMem_snd {E : PermutationEdges S} {φ : Equiv.Perm S}
    (hφ : φ ∈ permExtensions E) {x : S} (hx : x ∉ E.map Prod.fst) :
    φ x ∉ E.map Prod.snd := by
  simp only [List.mem_map] at hx ⊢
  rintro ⟨e, he, hex⟩
  refine hx ⟨e, he, φ.injective ?_⟩
  rw [mem_permExtensions.mp hφ e he, hex]

theorem symm_apply_notMem_fst {E : PermutationEdges S} {φ : Equiv.Perm S}
    (hφ : φ ∈ permExtensions E) {y : S} (hy : y ∉ E.map Prod.snd) :
    φ.symm y ∉ E.map Prod.fst := by
  simp only [List.mem_map] at hy ⊢
  rintro ⟨e, he, hey⟩
  refine hy ⟨e, he, ?_⟩
  rw [← mem_permExtensions.mp hφ e he, hey, Equiv.apply_symm_apply]

theorem card_filter_notMem {l : List S} (hl : l.Nodup) :
    (Finset.univ.filter (· ∉ l)).card = Fintype.card S - l.length := by
  have h : Finset.univ.filter (· ∉ l) = l.toFinsetᶜ := by
    ext
    simp
  rw [h, Finset.card_compl, List.toFinset_card_of_nodup hl]

omit [DecidableEq S] in
theorem length_lt_card {l : List S} (hl : l.Nodup) {x : S} (hx : x ∉ l) :
    l.length < Fintype.card S := by
  have := (List.nodup_cons.mpr ⟨hx, hl⟩).length_le_card
  simpa using this

theorem exists_notMem_of_length_lt {l : List S} (h : l.length < Fintype.card S) :
    ∃ x, x ∉ l := by
  by_contra hne
  push Not at hne
  have h1 : (Finset.univ : Finset S).card ≤ l.toFinset.card :=
    Finset.card_le_card fun x _ ↦ List.mem_toFinset.mpr (hne x)
  have h2 := List.toFinset_card_le l
  rw [Finset.card_univ] at h1
  omega

omit [Fintype S] [DecidableEq S] in
theorem isPartialPerm_cons {E : PermutationEdges S} (hE : IsPartialPerm E) {x y : S}
    (hx : x ∉ E.map Prod.fst) (hy : y ∉ E.map Prod.snd) : IsPartialPerm ((x, y) :: E) :=
  ⟨List.nodup_cons.mpr ⟨hx, hE.1⟩, List.nodup_cons.mpr ⟨hy, hE.2⟩⟩

/-- **The number of permutations extending a partial bijection** `E` is `(|S| - |E|)!`. -/
theorem card_permExtensions {E : PermutationEdges S} (hE : IsPartialPerm E) :
    (permExtensions E).card = (Fintype.card S - E.length).factorial := by
  induction h : Fintype.card S - E.length generalizing E with
  | zero =>
    have hall : ∀ x, x ∈ E.map Prod.fst := by
      by_contra hne
      push Not at hne
      obtain ⟨x, hx⟩ := hne
      have := length_lt_card hE.1 hx
      simp only [List.length_map] at this
      omega
    obtain ⟨π, hπ⟩ := exists_perm_extends hE
    rw [Nat.factorial_zero, Finset.card_eq_one]
    refine ⟨π, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨mem_permExtensions.mpr hπ, fun φ hφ ↦ Equiv.ext fun x ↦ ?_⟩⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hall x)
    rw [mem_permExtensions.mp hφ e he, hπ e he]
  | succ n ih =>
    obtain ⟨x, hx⟩ : ∃ x, x ∉ E.map Prod.fst :=
      exists_notMem_of_length_lt (by simp only [List.length_map]; omega)
    rw [Finset.card_eq_sum_ones, sum_permExtensions_fiber (E.map Prod.snd) (fun φ ↦ φ x)
      (fun z ↦ (x, z)) (fun φ hφ ↦ apply_notMem_snd hφ hx) (fun _ _ ↦ Iff.rfl)]
    have hfib : ∀ z ∈ Finset.univ.filter (· ∉ E.map Prod.snd),
        ∑ φ ∈ permExtensions ((x, z) :: E), (1 : ℕ) = n.factorial := by
      intro z hz
      rw [← Finset.card_eq_sum_ones]
      refine ih (isPartialPerm_cons hE hx (Finset.mem_filter.mp hz).2) ?_
      simp only [List.length_cons]
      omega
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, card_filter_notMem hE.2, smul_eq_mul,
      List.length_map, h, Nat.factorial_succ]

theorem apply_eq_of_mem_permExtensions {E : PermutationEdges S} {φ : Equiv.Perm S}
    (hφ : φ ∈ permExtensions E) {x y : S} (h : (x, y) ∈ E) : φ x = y :=
  mem_permExtensions.mp hφ _ h

theorem apply_eq_of_mem_permExtensions_cons {E : PermutationEdges S} {φ : Equiv.Perm S}
    {x y : S} (hφ : φ ∈ permExtensions ((x, y) :: E)) : φ x = y :=
  (mem_permExtensions_cons.mp hφ).1

omit [Fintype S] [DecidableEq S] in
theorem factorial_succ_mul_inv (m : ℕ) :
    ((m + 1).factorial : ℝ≥0∞) * ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ = m.factorial := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

variable [SampleableType S]

/-- A uniform draw outside a duplicate-free list `l` that misses some point hits each point
outside `l` with probability `1 / (|S| - |l|)`. -/
theorem prEvent_uniformAvoiding_eq {l : List S} (hl : l.Nodup) (h : ∃ y, y ∉ l) (y : S) :
    Pr{let z ← uniformAvoiding l}[z = y] =
      if y ∈ l then 0 else ((Fintype.card S - l.length : ℕ) : ℝ≥0∞)⁻¹ := by
  refine (prEvent_uniformAvoiding h (· = y)).trans ?_
  have hc : (Finset.univ.filter fun z ↦ z ∉ l).card = Fintype.card S - l.length :=
    card_filter_notMem hl
  rw [hc]
  split_ifs with hy
  · have : (Finset.univ.filter fun z ↦ z ∉ l ∧ z = y) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      rintro hz rfl
      exact hz hy
    rw [this, Finset.card_empty, Nat.cast_zero, ENNReal.zero_div]
  · have : (Finset.univ.filter fun z ↦ z ∉ l ∧ z = y) = {y} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h ↦ h.2
      · rintro rfl
        exact ⟨hy, rfl⟩
    rw [this, Finset.card_singleton, Nat.cast_one, one_div]

/-- The model's oracles over any finite `S`: coins forwarded, `π` and `π⁻¹` the lazily sampled
permutation. At `S = KeccakState` it is `lazyRandomPermutationOracles`. -/
noncomputable def lazyPermOracles :
    QueryImpl (unifSpec + permutationOracleSpec S) (StateT (PermutationEdges S) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => lazyRandomPermutation q

omit [SampleableType S] in
/-- The model's oracles answered by a fixed permutation `φ`: coins forwarded, `π = φ` and
`π⁻¹ = φ⁻¹`. -/
noncomputable def eagerPermOracles (φ : Equiv.Perm S) :
    QueryImpl (unifSpec + permutationOracleSpec S) ProbComp
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.forward x) => pure (φ x)
  | .inr (.inverse y) => pure (φ.symm y)

/-- A computation over the coins alone, run against the model's oracles, leaves the edges as
they are. -/
theorem run_simulateQ_lazyPermOracles_liftM {α : Type} (p : ProbComp α) (E : PermutationEdges S) :
    (simulateQ lazyPermOracles (liftM p : OracleComp (unifSpec + permutationOracleSpec S) α)).run
      E = (·, E) <$> p := by
  rw [← liftComp_eq_liftM]
  induction p using OracleComp.inductionOn generalizing E with
  | pure a => simp
  | query_bind n k ih =>
    have hq : simulateQ lazyPermOracles (liftComp (liftM (unifSpec.query n) : ProbComp _)
        (unifSpec + permutationOracleSpec S)) =
          (liftM (unifSpec.query n) : StateT (PermutationEdges S) ProbComp (Fin (n + 1))) := by
      rw [liftComp_liftM_query, OracleComp.liftM_eq_liftM_liftM, OracleQuery.liftM_add_left_query,
        simulateQ_spec_query]
      rfl
    rw [liftComp_bind, simulateQ_bind, hq, StateT.run_bind]
    simp only [ih]
    rfl

/-- **Lazy sampling from a partial bijection is uniform extension.** Run from an edge list `E`
that is a partial bijection, the lazily sampled permutation gives every output the average, over
the `(|S| - |E|)!` permutations extending `E`, of its probability against that permutation. -/
theorem factorial_mul_prEvent_lazy {α : Type}
    (oa : OracleComp (unifSpec + permutationOracleSpec S) α) {E : PermutationEdges S}
    (hE : IsPartialPerm E) (a : α) :
    ((Fintype.card S - E.length).factorial : ℝ≥0∞) *
        Pr{let z ← (simulateQ lazyPermOracles oa).run' E}[z = a] =
      ∑ φ ∈ permExtensions E, Pr{let z ← simulateQ (eagerPermOracles φ) oa}[z = a] := by
  classical
  induction oa using OracleComp.inductionOn generalizing E with
  | pure b =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, Finset.sum_const,
      card_permExtensions hE, nsmul_eq_mul]
  | query_bind t k ih =>
    have hlazy : (simulateQ lazyPermOracles (liftM ((unifSpec + permutationOracleSpec S).query t) >>= k)).run' E =
        (lazyPermOracles t).run E >>= fun p ↦ (simulateQ lazyPermOracles (k p.1)).run' p.2 := by
      simp [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    have heager (φ : Equiv.Perm S) :
        simulateQ (eagerPermOracles φ) (liftM ((unifSpec + permutationOracleSpec S).query t) >>= k) =
          eagerPermOracles φ t >>= fun u ↦ simulateQ (eagerPermOracles φ) (k u) := by
      simp [simulateQ_bind]
    change _ * Pr{let z ← (simulateQ lazyPermOracles (liftM ((unifSpec + permutationOracleSpec S).query t) >>= k)).run' E}[z = a] =
      ∑ φ ∈ permExtensions E,
        Pr{let z ← simulateQ (eagerPermOracles φ) (liftM ((unifSpec + permutationOracleSpec S).query t) >>= k)}[z = a]
    simp only [hlazy, heager]
    rcases t with n | (x | y)
    · have hrun : (lazyPermOracles (S := S) (.inl n)).run E =
          ((liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) >>= fun u ↦ pure (u, E)) := rfl
      have he (φ : Equiv.Perm S) : eagerPermOracles φ (.inl n) =
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl
      simp only [hrun, he, bind_assoc, pure_bind, prEvent_bind_eq_sum_fintype]
      rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [mul_left_comm, ih u hE, Finset.mul_sum]
      rfl
    · cases hx : forwardLookup E x with
      | some y =>
        have hrun : (lazyPermOracles (S := S) (.inr (.forward x))).run E = pure (y, E) := by
          simp [lazyPermOracles, lazyRandomPermutation, hx]
        simp only [hrun, eagerPermOracles, pure_bind]
        rw [ih y hE]
        refine Finset.sum_congr rfl fun φ hφ ↦ ?_
        rw [apply_eq_of_mem_permExtensions hφ (mem_of_fwdLookup_eq_some hx)]
      | none =>
        have hx' : x ∉ E.map Prod.fst := fwdLookup_eq_none_iff.mp hx
        have hlt : E.length < Fintype.card S := by simpa using length_lt_card hE.1 hx'
        obtain ⟨m, hm⟩ : ∃ m, Fintype.card S - E.length = m + 1 :=
          ⟨Fintype.card S - E.length - 1, by omega⟩
        have hfree : ∃ y, y ∉ E.map Prod.snd := exists_notMem_of_length_lt (by simpa using hlt)
        have hrun : (lazyPermOracles (S := S) (.inr (.forward x))).run E =
            (fun y ↦ (y, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.snd) := by
          simp [lazyPermOracles, lazyRandomPermutation, hx]
        simp only [hrun, eagerPermOracles, pure_bind, bind_map_left]
        rw [prEvent_bind_eq_sum_fintype, sum_permExtensions_fiber (E.map Prod.snd)
          (fun φ ↦ φ x) (fun z ↦ (x, z)) (fun φ hφ ↦ apply_notMem_snd hφ hx')
          (fun _ _ ↦ Iff.rfl), Finset.mul_sum,
          ← Finset.sum_filter_of_ne (s := Finset.univ) (p := (· ∉ E.map Prod.snd))]
        · refine Finset.sum_congr rfl fun y hy ↦ ?_
          have hy' := (Finset.mem_filter.mp hy).2
          have hm' : Fintype.card S - ((x, y) :: E).length = m := by
            simp only [List.length_cons]
            omega
          rw [prEvent_uniformAvoiding_eq hE.2 hfree, ite_eq_right hy', List.length_map, hm,
            ← mul_assoc, factorial_succ_mul_inv, ← hm', ih y (isPartialPerm_cons hE hx' hy')]
          refine Finset.sum_congr rfl fun φ hφ ↦ ?_
          rw [apply_eq_of_mem_permExtensions_cons hφ]
        · intro y _ hne
          by_contra hy
          refine hne ?_
          rw [prEvent_uniformAvoiding_eq hE.2 hfree, ite_eq_left hy, zero_mul, mul_zero]
    · cases hy : inverseLookup E y with
      | some x =>
        have hrun : (lazyPermOracles (S := S) (.inr (.inverse y))).run E = pure (x, E) := by
          simp [lazyPermOracles, lazyRandomPermutation, hy]
        simp only [hrun, eagerPermOracles, pure_bind]
        rw [ih x hE]
        refine Finset.sum_congr rfl fun φ hφ ↦ ?_
        rw [(Equiv.symm_apply_eq φ).mpr
          (apply_eq_of_mem_permExtensions hφ (mem_of_invLookup_eq_some hy)).symm]
      | none =>
        have hy' : y ∉ E.map Prod.snd := invLookup_eq_none_iff.mp hy
        have hlt : E.length < Fintype.card S := by simpa using length_lt_card hE.2 hy'
        obtain ⟨m, hm⟩ : ∃ m, Fintype.card S - E.length = m + 1 :=
          ⟨Fintype.card S - E.length - 1, by omega⟩
        have hfree : ∃ x, x ∉ E.map Prod.fst := exists_notMem_of_length_lt (by simpa using hlt)
        have hrun : (lazyPermOracles (S := S) (.inr (.inverse y))).run E =
            (fun x ↦ (x, (x, y) :: E)) <$> uniformAvoiding (E.map Prod.fst) := by
          simp [lazyPermOracles, lazyRandomPermutation, hy]
        simp only [hrun, eagerPermOracles, pure_bind, bind_map_left]
        rw [prEvent_bind_eq_sum_fintype, sum_permExtensions_fiber (E.map Prod.fst)
          (fun φ ↦ φ.symm y) (fun z ↦ (z, y)) (fun φ hφ ↦ symm_apply_notMem_fst hφ hy')
          (fun _ φ ↦ ((Equiv.symm_apply_eq φ).trans eq_comm).symm), Finset.mul_sum,
          ← Finset.sum_filter_of_ne (s := Finset.univ) (p := (· ∉ E.map Prod.fst))]
        · refine Finset.sum_congr rfl fun x hx ↦ ?_
          have hx' := (Finset.mem_filter.mp hx).2
          have hm' : Fintype.card S - ((x, y) :: E).length = m := by
            simp only [List.length_cons]
            omega
          rw [prEvent_uniformAvoiding_eq hE.1 hfree, ite_eq_right hx', List.length_map, hm,
            ← mul_assoc, factorial_succ_mul_inv, ← hm', ih x (isPartialPerm_cons hE hx' hy')]
          refine Finset.sum_congr rfl fun φ hφ ↦ ?_
          rw [(Equiv.symm_apply_eq φ).mpr (apply_eq_of_mem_permExtensions_cons hφ).symm]
        · intro x _ hne
          by_contra hx
          refine hne ?_
          rw [prEvent_uniformAvoiding_eq hE.1 hfree, ite_eq_left hx, zero_mul, mul_zero]

/-- **Lazy sampling is uniform sampling.** The lazily sampled permutation, run from no edge, gives
every output the average, over all `|S|!` permutations `φ`, of its probability when `π` is
answered by `φ` and `π⁻¹` by `φ⁻¹`. -/
theorem prEvent_lazy_eq {α : Type} (oa : OracleComp (unifSpec + permutationOracleSpec S) α)
    (a : α) :
    Pr{let z ← (simulateQ lazyPermOracles oa).run' []}[z = a] =
      ((Fintype.card S).factorial : ℝ≥0∞)⁻¹ *
        ∑ φ : Equiv.Perm S, Pr{let z ← simulateQ (eagerPermOracles φ) oa}[z = a] := by
  have h := factorial_mul_prEvent_lazy oa isPartialPerm_nil a
  have hext : permExtensions ([] : PermutationEdges S) = Finset.univ := by
    ext
    simp [permExtensions]
  rw [hext, List.length_nil, Nat.sub_zero] at h
  rw [← h, ← mul_assoc, ENNReal.inv_mul_cancel (by simp [Nat.factorial_ne_zero])
    (ENNReal.natCast_ne_top _), one_mul]

/-- **Lazy sampling is uniform sampling**, as output measures: the run of the lazily sampled
permutation from no edge is the uniform mixture of the runs against fixed permutations. -/
theorem evalDist_lazy_eq {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + permutationOracleSpec S) α) :
    𝒟[(simulateQ lazyPermOracles oa).run' []] =
      ((Fintype.card S).factorial : ℝ≥0∞)⁻¹ •
        ∑ φ : Equiv.Perm S, 𝒟[simulateQ (eagerPermOracles φ) oa] := by
  classical
  ext s hs
  have hP (m : ProbComp α) :
      𝒟[m] s = ∑' x, if x ∈ s then Pr{let z ← m}[z = x] else 0 := by
    rw [← prEvent_eq_tsum_ite, prEvent_eq_evalDist m (· ∈ s) hs.mem, Set.ofPred_mem_eq]
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  simp only [hP, prEvent_lazy_eq]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a ↦ ?_
  split_ifs <;> simp

end LazyEager

/-! ## Classical programs against a quantum runtime -/

section Runtime

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {A B C : QReg}

/-- **A program that runs as a classical sampler against `R`, through the map `Φ`**: its branch at
each value `a` is the probability that `pa` returns `a` times `Φ`, a map on the program register
and the runtime register that does not depend on `a`. A program on a fixed register that only
reads classical answers has `Φ = id`. -/
def ClassicalOn {α : Type} (x : QComp spec A B α) (pa : ProbComp α)
    (Φ : MatrixMap (A × R.D) (B × R.D)) : Prop :=
  ∀ a, (R.run₂ .instruments x).branch a = ((Pr{let z ← pa}[z = a]).toReal : ℂ) • Φ

variable {R}

/-- A program that returns at once runs as the sampler that returns at once. -/
theorem classicalOn_pure {α : Type} (x : α) :
    ClassicalOn R (QuantumComp₂.pure x : QComp spec B B α) (pure x) LinearMap.id := by
  classical
  intro a
  rw [QuantumRuntime.run₂_pure, prEvent_pure]
  by_cases h : a = x
  · subst h
    simp
  · simp [Ne.symm h, SubInstrument.branch_pure_of_ne h]

/-- A local operation with one outcome runs as the sampler of that outcome, through its unique
branch framed by the runtime register. -/
theorem classicalOn_act (p : SubInstrument A B Unit) :
    ClassicalOn R (QComp.act (spec := spec) p) (pure ()) ((p.frame R.D).branch ()) := by
  intro a
  rw [QuantumRuntime.run₂_act, SubInstrument.bind_pure, prEvent_pure, ite_eq_left (Subsingleton.elim _ _)]
  simp

/-- The sampler and the map of a program that runs classically can be rewritten. -/
theorem ClassicalOn.congr {α : Type} {x : QComp spec A B α} {pa pb : ProbComp α}
    {Φ Ψ : MatrixMap (A × R.D) (B × R.D)} (h : ClassicalOn R x pa Φ) (hpa : pa = pb)
    (hΦ : Φ = Ψ) : ClassicalOn R x pb Ψ :=
  hpa ▸ hΦ ▸ h

/-- Sequencing programs that run as classical samplers runs as the sequenced sampler, through
the composite map. -/
theorem ClassicalOn.bind {α β : Type} {x : QComp spec A B α} {pa : ProbComp α}
    {Φ : MatrixMap (A × R.D) (B × R.D)} {k : α → QComp spec B C β} {pk : α → ProbComp β}
    {Ψ : MatrixMap (B × R.D) (C × R.D)} (hx : ClassicalOn R x pa Φ)
    (hk : ∀ a, ClassicalOn R (k a) (pk a) Ψ) : ClassicalOn R (x.bind k) (pa >>= pk) (Ψ ∘ₗ Φ) := by
  intro c
  have hne (a : α) : Pr{let z ← pa}[z = a] * Pr{let z ← pk a}[z = c] ≠ ∞ :=
    ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _)
  have hsum : ∑' a, Pr{let z ← pa}[z = a] * Pr{let z ← pk a}[z = c] ≠ ∞ := by
    rw [← prEvent_bind_eq_tsum]
    exact prEvent_ne_top _
  refine LinearMap.ext fun ρ ↦ ?_
  rw [QuantumRuntime.run₂_bind, DSubInstrument.branch_bind_apply, prEvent_bind_eq_tsum,
    ENNReal.tsum_toReal_eq hne, Complex.ofReal_tsum, LinearMap.smul_apply,
    ← (Complex.summable_ofReal.mpr (ENNReal.summable_toReal hsum)).tsum_smul_const]
  refine tsum_congr fun a ↦ ?_
  simp only [hx a, hk a c, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul,
    ENNReal.toReal_mul, Complex.ofReal_mul]

/-- Sequencing programs on a fixed register that run classically through the identity. -/
theorem ClassicalOn.bind_id {α β : Type} {x : QComp spec B B α} {pa : ProbComp α}
    {k : α → QComp spec B B β} {pk : α → ProbComp β} (hx : ClassicalOn R x pa LinearMap.id)
    (hk : ∀ a, ClassicalOn R (k a) (pk a) LinearMap.id) :
    ClassicalOn R (x.bind k) (pa >>= pk) LinearMap.id :=
  (hx.bind hk).congr rfl (LinearMap.id_comp _)

/-- Relabelling the value of a program that runs as a classical sampler relabels the sampler. -/
theorem ClassicalOn.map {α β : Type} {x : QComp spec B B α} {pa : ProbComp α}
    (hx : ClassicalOn R x pa LinearMap.id) (g : α → β) :
    ClassicalOn R (x.map g) (g <$> pa) LinearMap.id := by
  rw [QuantumComp₂.map_eq_bind_pure, map_eq_bind_pure_comp]
  exact hx.bind_id fun a ↦ classicalOn_pure (g a)

/-- **A classical algorithm whose queries run as classical samplers**: if every answer program
`q t` runs as `impl t` against `R`, the algorithm `oa` run by these programs runs as
`simulateQ impl oa`. -/
theorem classicalOn_toQuantumAt {ι : Type} {ospec : OracleSpec.{0, 0} ι}
    {q : QueryImpl ospec (QComp spec B B)} {impl : QueryImpl ospec ProbComp}
    (hq : ∀ t, ClassicalOn R (q t) (impl t) LinearMap.id) {α : Type} (oa : OracleComp ospec α) :
    ClassicalOn R (oa.toQuantumAt q) (simulateQ impl oa) LinearMap.id := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    rw [toQuantumAt_pure, simulateQ_pure]
    exact classicalOn_pure x
  | query_bind t k ih =>
    rw [toQuantumAt_query_bind, simulateQ_bind, simulateQ_spec_query]
    exact (hq t).bind_id ih

/-- A program that runs as the sampler `pa` through the identity has as outcome measure the
output measure of `pa` scaled by the trace of the input substate. -/
theorem ClassicalOn.outcomeMeasure {α : Type} [MeasurableSpace α] {x : QComp spec B B α}
    {pa : ProbComp α} (h : ClassicalOn R x pa LinearMap.id) (ρ : SubState (B × R.D)) :
    (R.run₂ .instruments x).outcomeMeasure ρ = ENNReal.ofReal ρ.matrix.trace.re • 𝒟[pa] := by
  classical
  ext s hs
  rw [DSubInstrument.outcomeMeasure_apply _ _ hs, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  unfold ClassicalOn at h
  simp_rw [h, LinearMap.smul_apply, LinearMap.id_apply, Matrix.trace_smul, smul_eq_mul,
    Complex.re_ofReal_mul, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (prEvent_ne_top _)]
  calc
    _ = ENNReal.ofReal ρ.matrix.trace.re *
        ∑' a, if a ∈ s then Pr{let z ← pa}[z = a] else 0 := by
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun a ↦ ?_
      by_cases ha : a ∈ s <;> simp [ha, mul_comm]
    _ = _ := by
      congr 1
      rw [← OracleComp.prEvent_eq_tsum_ite]
      exact prEvent_eq_evalDist pa (· ∈ s) hs.mem

end Runtime

/-! ## Classical calls of the QRPM -/

section Permutation

variable {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]

/-- The permutation a port of the oracle of `φ` adds into the response register. -/
def portPerm (φ : Equiv.Perm S) : PermutationPort → Equiv.Perm S
  | .forward => φ
  | .inverse => φ.symm

/-- The oracle of `φ` as an emulated oracle: the oracle unitary of each port, beside the trivial
private register. -/
noncomputable def permEmulated (φ : Equiv.Perm S) :
    EmulatedOracle PermutationPort fun _ ↦ QReg.of (S × S) where
  S := QReg.of Unit
  init := SubState.basis ()
  U p := oracleUnitary ⇑(portPerm φ p) ⊗ₖ (1 : Matrix Unit Unit ℂ)
  unitary _ := Matrix.kronecker_mem_unitary (oracleUnitary_mem_unitaryGroup _) (one_mem _)

/-- The runtime of the oracle of `φ` is the runtime of its emulated oracle. -/
theorem permutationRuntime_eq_toRuntime (φ : Equiv.Perm S) :
    permutationRuntime φ = (permEmulated φ).toRuntime := by
  refine congrArg (QuantumRuntime.mk _ _) (funext fun p ↦ DSubInstrument.ext <| funext fun r ↦ ?_)
  cases p <;>
  · rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply, MatrixMap.amplify_conj]
    rfl

/-- **A basis call of the QRPM against a fixed permutation**: from the basis input `a`, the call
of port `p` reads `(a.1, a.2 + φ_p a.1)` with certainty and leaves the held register untouched. -/
theorem branch_run₂_callBasis_permutationRuntime (φ : Equiv.Perm S) (p : PermutationPort)
    (B : QReg) (a : S × S) {β : Type} [DecidableEq β] (read : S × S → Unit → β) (c : β) :
    ((permutationRuntime φ).run₂ .instruments
        (QComp.callBasis (spec := qrpmSpec S) p B a read)).branch c =
      if read (a.1, a.2 + portPerm φ p a.1) () = c then LinearMap.id else 0 := by
  rw [permutationRuntime_eq_toRuntime]
  refine ((permEmulated φ).branch_run₂_callBasis p B a read c).trans ?_
  have hblock (o : S × S) : (permEmulated φ).block p o a =
      if o = (a.1, a.2 + portPerm φ p a.1) then 1 else 0 := by
    ext d d'
    obtain ⟨⟩ := d
    obtain ⟨⟩ := d'
    change oracleUnitary ⇑(portPerm φ p) o a * (1 : Matrix Unit Unit ℂ) () () = _
    rw [oracleUnitary_apply, Matrix.one_apply_eq, mul_one]
    split_ifs <;> rfl
  simp only [hblock]
  rw [Finset.sum_eq_single (a.1, a.2 + portPerm φ p a.1)]
  · simp [MatrixMap.conj_one]
  · intro o _ ho
    simp [ho, MatrixMap.conj_zero]
  · simp

variable {T : Type} [DecidableEq T]

/-- **The model's oracles by classical calls of the QRPM** beside a held register `B`, through an
equivalence `e : T ≃ S`: coins by uniform coins, `π t` by a basis call of `φ` at `e t` read back
through `e`, and `π⁻¹` likewise with `φ⁻¹`. At `T = KeccakState` it is `Xmss.permImpl`. -/
noncomputable def qrpmImpl (e : T ≃ S) (B : QReg) :
    QueryImpl (unifSpec + permutationOracleSpec T) (QComp (qrpmSpec S) B B)
  | .inl n => QComp.coinImpl (qrpmSpec S) B n
  | .inr (.forward s) => QComp.callBasis (spec := qrpmSpec S) PermutationPort.forward B
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2
  | .inr (.inverse s) => QComp.callBasis (spec := qrpmSpec S) PermutationPort.inverse B
      ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2

/-- Against the oracle of `φ`, each classical call branches as the fixed permutation
`e⁻¹ φ e` answers it. -/
theorem classicalOn_qrpmImpl (e : T ≃ S) (B : QReg) (φ : Equiv.Perm S)
    (t : (unifSpec + permutationOracleSpec T).Domain) :
    ClassicalOn (permutationRuntime φ) (qrpmImpl e B t) (eagerPermOracles (e.symm.permCongr φ) t)
      LinearMap.id := by
  classical
  intro y
  rcases t with n | (s | s)
  · have hp : Pr{let z ← eagerPermOracles (e.symm.permCongr φ) (.inl n)}[z = y] =
        (Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹ := by
      change Pr{let z ← (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))}[z = y] = _
      simpa [Finset.filter_eq'] using
        (prEvent_liftM_query_eq_card_div (spec := unifSpec) n (fun x ↦ x = y))
    rw [hp, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv,
      Complex.ofReal_natCast]
    change ((permutationRuntime φ).run₂ .instruments (QComp.coinImpl (qrpmSpec S) B n)).branch y = _
    rw [QComp.coinImpl, QuantumRuntime.run₂_act, SubInstrument.bind_pure,
      DSubInstrument.branch_frame_apply]
    refine LinearMap.ext fun ρ ↦ ?_
    ext x x'
    simp [SubInstrument.branch_uniform_apply]
  · change ((permutationRuntime φ).run₂ .instruments (QComp.callBasis (spec := qrpmSpec S)
      PermutationPort.forward B ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2)).branch y = _
    rw [branch_run₂_callBasis_permutationRuntime]
    simp only [eagerPermOracles, prEvent_pure, portPerm, zero_add, Equiv.permCongr_apply,
      Equiv.symm_symm]
    split_ifs <;> simp
  · have hinv : (e.symm.permCongr φ).symm s = e.symm (φ.symm (e s)) := by
      rw [Equiv.symm_apply_eq]
      simp
    change ((permutationRuntime φ).run₂ .instruments (QComp.callBasis (spec := qrpmSpec S)
      PermutationPort.inverse B ((e s, 0) : S × S) fun o _ ↦ e.symm (o : S × S).2)).branch y = _
    rw [branch_run₂_callBasis_permutationRuntime]
    simp only [eagerPermOracles, prEvent_pure, portPerm, zero_add, hinv]
    split_ifs <;> simp

/-- Against the oracle of `φ`, a classical algorithm run by classical calls runs as the
algorithm against the fixed permutation `e⁻¹ φ e`. -/
theorem classicalOn_toQuantumAt_qrpmImpl (e : T ≃ S) (B : QReg) (φ : Equiv.Perm S) {α : Type}
    (oa : OracleComp (unifSpec + permutationOracleSpec T) α) :
    ClassicalOn (permutationRuntime φ) (oa.toQuantumAt (qrpmImpl e B))
      (simulateQ (eagerPermOracles (e.symm.permCongr φ)) oa) LinearMap.id :=
  classicalOn_toQuantumAt (classicalOn_qrpmImpl e B φ) oa

/-- **A program that runs classically against every permutation, in the QRPM.** If against the
oracle of every `φ` the program `x` runs as `oa` against the fixed permutation `e⁻¹ φ e`, its
observed distribution in the QRPM, from the held substate `ρ`, is the output measure of `oa`
against the lazily sampled random permutation of `T`, scaled by the trace of `ρ`. -/
theorem qrpmEvalDistMap_of_classicalOn [Fintype T] [SampleableType T] (e : T ≃ S) {B : QReg} {α β : Type}
    [MeasurableSpace β] {x : QComp (qrpmSpec S) B B α}
    {oa : OracleComp (unifSpec + permutationOracleSpec T) α}
    (hx : ∀ φ, ClassicalOn (permutationRuntime φ) x
      (simulateQ (eagerPermOracles (e.symm.permCongr φ)) oa) LinearMap.id)
    (ρ : SubState B) (g : α → β) :
    qrpmEvalDistMap .instruments x ρ (fun _ p ↦ g p.2.2) =
      ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> (simulateQ lazyPermOracles oa).run' []] := by
  have hφ (φ : Equiv.Perm S) :
      (permutationRuntime φ).evalDistMap .instruments x ρ (fun p ↦ g p.2.2) =
        ENNReal.ofReal ρ.matrix.trace.re •
          𝒟[g <$> simulateQ (eagerPermOracles (e.symm.permCongr φ)) oa] := by
    refine (QuantumRuntime.evalDist₂_map_eq_evalDistMap _ _ g _ ρ).symm.trans ?_
    rw [QuantumRuntime.evalDist₂, ((hx φ).map g).outcomeMeasure, SubState.trace_re_prod,
      trace_re_permutationRuntime_init, mul_one]
  have hlazy : g <$> (simulateQ lazyPermOracles oa).run' [] =
      (simulateQ lazyPermOracles (g <$> oa)).run' [] := by
    simp [StateT.run'_eq, StateT.run_map]
  refine (sampledEvalDistMap_eq_sum _ _ _ _ _).trans ?_
  rw [hlazy, evalDist_lazy_eq]
  simp only [hφ, simulateQ_map]
  rw [Equiv.sum_comp e.symm.permCongr
      (fun ψ ↦ ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> simulateQ (eagerPermOracles ψ) oa]),
    ← Finset.smul_sum, smul_comm, Fintype.card_perm, Fintype.card_congr e]

/-- **A program on the trivial register that runs classically against every permutation**
returns each value in the QRPM, from the trivial state, with the probability that `oa` returns it
against the lazily sampled random permutation of `T`. -/
theorem qrpmEvalDistMap_of_classicalOn_singleton [Fintype T] [SampleableType T] (e : T ≃ S)
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    {x : QComp (qrpmSpec S) (QReg.of Unit) (QReg.of Unit) α}
    {oa : OracleComp (unifSpec + permutationOracleSpec T) α}
    (hx : ∀ φ, ClassicalOn (permutationRuntime φ) x
      (simulateQ (eagerPermOracles (e.symm.permCongr φ)) oa) LinearMap.id) (a : α) :
    qrpmEvalDistMap .instruments x (SubState.basis ()) (fun _ p ↦ p.2.2) {a} =
      Pr{let z ← (simulateQ lazyPermOracles oa).run' []}[z = a] := by
  have h := qrpmEvalDistMap_of_classicalOn e hx (SubState.basis ()) id
  rw [SubState.matrix_basis, Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one,
    one_smul, id_map] at h
  rw [prEvent_eq_evalDist_singleton]
  exact congrArg (· {a}) h

/-- **The QRPM on classical programs is the classical random-permutation model.** A classical
algorithm over coins, `π` and `π⁻¹` on `T`, run in the QRPM on `S ≃ T` by classical calls beside a
held register in the substate `ρ`, has as observed distribution the output measure of the
algorithm against the lazily sampled random permutation of `T`, scaled by the trace of `ρ`. -/
theorem qrpmEvalDistMap_toQuantumAt_qrpmImpl [Fintype T] [SampleableType T] (e : T ≃ S) (B : QReg)
    {α β : Type} [MeasurableSpace β] (oa : OracleComp (unifSpec + permutationOracleSpec T) α)
    (ρ : SubState B) (g : α → β) :
    qrpmEvalDistMap .instruments (oa.toQuantumAt (qrpmImpl e B)) ρ (fun _ p ↦ g p.2.2) =
      ENNReal.ofReal ρ.matrix.trace.re • 𝒟[g <$> (simulateQ lazyPermOracles oa).run' []] :=
  qrpmEvalDistMap_of_classicalOn e (fun φ ↦ classicalOn_toQuantumAt_qrpmImpl e B φ oa) ρ g

end Permutation

end Quantum

end
