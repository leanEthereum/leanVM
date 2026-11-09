module

public import LeanDa.StraightTree
public import Common.Duplex.Vec
public import LeanDa.WithHash

@[expose] public section

/-!
# The straight-line world and its bad events

The world of the straight-line proof of code binding (`LeanDa.Straight`): `H` and the challenges
`G` two lazily sampled random oracles, `G` from roots to vectors `E^2` (`VSpec`, the duplex
lemma's world with the challenges as one oracle of vectors). Its caches are **good**
(`Good`) when `H` is injective on its cached inputs and, for every root `d` with cached
challenges `v`, every matrix whose commitment's inputs are all cached, which commits to `d` and
passes the membership test on `v`, is a codeword.

* **A fresh answer of `H` keeps a cache good** unless it collides with a cached answer, is a
  digest a cached input or the query carries (`chunks`), or is a root with cached challenges
  (`good_insertH`): a matrix whose tree the new entry completes would hash a node to a digest an
  older input already carries. At most `65 N` values for a cache of `N` entries.
* **Fresh challenges keep a cache good** unless the one matrix committed to the root (`H`
  injective: `commit_unique`), fixed before the challenges are drawn, is not a codeword and passes
  the membership test: at most `(2^14 - 1) / 2^192`, the test's soundness (`checker_sound`).
* So a run of `N` queries, `Q_G` of them of `G`, ends in a bad cache with probability at most
  `N · 65 N / 2^256 + Q_G · (2^14 - 1) / 2^192` (`prob_not_good_le`, by the bad-event budget with two
  weights, `prEvent_run_bad_le₂`).
* A coin-free computation's run is read off its final cache (`replay_of_mem_support`): replayed
  against the cache as a partial function, it returns the run's result.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA; the
straight-line proof it serves replaces his forking step and keeps his framework, his games and
his membership test's soundness.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex MeasureTheory PqDas
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace Common

/-! ## The bad-event budget with two weights -/

section Budget2

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {σ α : Type}
  {ι' : Type} {spec' : OracleSpec.{0, 0} ι'} [AnswerMeasure spec']

/-- **The bad-event budget with two weights** (`prEvent_run_bad_le` with a second weight): if
every step `t` from a good state of size at most `N - w₁ t` reaches a bad state with probability
at most `w₁ t · δ₁ + w₂ t · δ₂`, a computation of weights at most `Q₁` and `Q₂` ends in a bad
state with probability at most `[bad s₀] + Q₁ · δ₁ + Q₂ · δ₂`. -/
theorem prEvent_run_bad_le₂
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (bad inv : σ → Prop)
    [DecidablePred bad] (w₁ w₂ : ι → ℕ) (size : σ → ℕ) (N : ℕ) (δ₁ δ₂ : ℝ≥0∞)
    (hinv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (hsize : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), size z.2 ≤ size s + w₁ t)
    (hstep : ∀ t s, inv s → ¬bad s → size s + w₁ t ≤ N →
      Pr{let z ← (impl t).run s}[bad z.2] ≤ w₁ t * δ₁ + w₂ t * δ₂)
    (oa : OracleComp spec α) (Q₁ Q₂ : ℕ) (hQ₁ : QueryCostAtMost oa w₁ Q₁)
    (hQ₂ : QueryCostAtMost oa w₂ Q₂) (s₀ : σ) (hs₀ : inv s₀) (hN : size s₀ + Q₁ ≤ N) :
    Pr{let z ← (simulateQ impl oa).run s₀}[bad z.2] ≤
      (if bad s₀ then 1 else 0) + (Q₁ * δ₁ + Q₂ * δ₂) := by
  induction oa using OracleComp.inductionOn generalizing Q₁ Q₂ s₀ with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    split_ifs <;> simp
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at hQ₁ hQ₂
    obtain ⟨hwt₁, hk₁⟩ := hQ₁
    obtain ⟨hwt₂, hk₂⟩ := hQ₂
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind]
    let : MeasurableSpace (spec.Range t × σ) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete]
    have hbound : ∀ z ∈ support ((impl t).run s₀),
        Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ≤
          (if bad z.2 then 1 else 0) + ((Q₁ - w₁ t : ℕ) * δ₁ + (Q₂ - w₂ t : ℕ) * δ₂) :=
      fun z hz ↦ ih z.1 (Q₁ - w₁ t) (Q₂ - w₂ t) (hk₁ z.1) (hk₂ z.1) z.2 (hinv t s₀ hs₀ z hz)
        (by have := hsize t s₀ hs₀ z hz; omega)
    calc ∫⁻ z, Pr{let y ← (simulateQ impl (k z.1)).run z.2}[bad y.2] ∂𝒟[(impl t).run s₀]
        ≤ ∫⁻ z, ((if bad z.2 then 1 else 0) + ((Q₁ - w₁ t : ℕ) * δ₁ + (Q₂ - w₂ t : ℕ) * δ₂))
            ∂𝒟[(impl t).run s₀] := by
          apply lintegral_mono_ae
          filter_upwards [ae_evalDist_of_forall_mem_support _ hbound] with z hz using hz
      _ ≤ Pr{let z ← (impl t).run s₀}[bad z.2] +
            ((Q₁ - w₁ t : ℕ) * δ₁ + (Q₂ - w₂ t : ℕ) * δ₂) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const]
          refine add_le_add (le_of_eq ?_)
            (mul_le_of_le_one_right' (evalDist_apply_univ_le_one _))
          rw [prEvent_eq_evalDist_of_discrete, ← lintegral_indicator_one MeasurableSet.of_discrete]
          exact lintegral_congr fun z ↦ by by_cases h : bad z.2 <;> simp [h, Set.indicator]
      _ ≤ ((if bad s₀ then 1 else 0) + (w₁ t * δ₁ + w₂ t * δ₂)) +
            ((Q₁ - w₁ t : ℕ) * δ₁ + (Q₂ - w₂ t : ℕ) * δ₂) := by
          gcongr
          by_cases hb : bad s₀
          · simp only [hb, ite_true]
            exact (prEvent_le_one _).trans le_self_add
          · simp only [hb, ite_false, zero_add]
            exact hstep t s₀ hs₀ hb (by omega)
      _ = (if bad s₀ then 1 else 0) + (Q₁ * δ₁ + Q₂ * δ₂) := by
          have e₁ : ((w₁ t : ℕ) : ℝ≥0∞) + (Q₁ - w₁ t : ℕ) = Q₁ := by
            exact_mod_cast Nat.add_sub_cancel' hwt₁
          have e₂ : ((w₂ t : ℕ) : ℝ≥0∞) + (Q₂ - w₂ t : ℕ) = Q₂ := by
            exact_mod_cast Nat.add_sub_cancel' hwt₂
          rw [← e₁, ← e₂]
          ring

/-- **Weights add.** -/
theorem QueryCostAtMost.add {oa : OracleComp spec α} {w₁ w₂ : ι → ℕ} {a b : ℕ}
    (h₁ : QueryCostAtMost oa w₁ a) (h₂ : QueryCostAtMost oa w₂ b) :
    QueryCostAtMost oa (fun t ↦ w₁ t + w₂ t) (a + b) := by
  induction oa using OracleComp.inductionOn generalizing a b with
  | pure x => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h₁ h₂ ⊢
    refine ⟨by omega, fun u ↦ (ih u (h₁.2 u) (h₂.2 u)).mono (by omega)⟩

end Budget2

end Common

namespace LeanDa

/-! ## The world -/

/-- **The straight-line world's oracles**: coins, `H`, and the challenges as one random oracle of
vectors. -/
abbrev VS := VSpec (List UInt8) DigestBytes Common.DigestBytes E 2

/-- Its cache. -/
abbrev VCache := VS.QueryCache

/-- The hash function of a cache: its cached answers, `default` elsewhere. -/
def fOf (c : VCache) (a : List UInt8) : Common.DigestBytes := (c (.inl a)).getD default

/-- The inputs of `H` a cache holds. -/
def domH (c : VCache) : Set (List UInt8) := {a | c (.inl a) ≠ none}

/-- The roots whose challenges a cache holds. -/
def domG (c : VCache) : Set Common.DigestBytes := {d | c (.inr d) ≠ none}

/-- **A good cache**: `H` injective on its cached inputs, and for every root `d` with cached
challenges `v`, every matrix whose commitment's inputs are cached, which commits to `d` and passes
the membership test on `v`, a codeword. -/
def Good (r : ℕ) (c : VCache) : Prop :=
  Set.InjOn (fOf c) (domH c) ∧ ∀ (d : Common.DigestBytes) (v : MembershipChallenge), c (.inr d) =
      some v →
    ∀ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c → commitCellsWithHash (fOf c) w = d →
      membershipCheck (v 1) w = true → w ∈ (leanDaErasureCode r).code

theorem good_empty (r : ℕ) : Good r ∅ :=
  ⟨fun a ha ↦ (ha rfl).elim, fun _ _ h ↦ by simp at h⟩

theorem fOf_of_mem {c : VCache} {a : List UInt8} {u : Common.DigestBytes} (h : c (.inl a) = some u) :
    fOf c a = u := by simp [fOf, h]

theorem cache_inl_eq_fOf {c : VCache} {a : List UInt8} (h : a ∈ domH c) :
    c (.inl a) = some (fOf c a) := by
  rcases hc : c (.inl a) with _ | u
  · exact absurd hc h
  · simp [fOf, hc]

section Insert

variable (c : VCache)

theorem vcache_inl_inl (a b : List UInt8) (u : Common.DigestBytes) :
    (c.cacheQuery (.inl a) u) (.inl b) = if b = a then some u else c (.inl b) := by
  by_cases h : b = a
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]; simp [h]

theorem vcache_inl_inr (a : List UInt8) (u : Common.DigestBytes) (d : Common.DigestBytes) :
    (c.cacheQuery (.inl a) u) (.inr d) = c (.inr d) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem vcache_inr_inl (d : Common.DigestBytes) (v : MembershipChallenge) (a : List UInt8) :
    (c.cacheQuery (.inr d) v) (.inl a) = c (.inl a) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem vcache_inr_inr (d e : Common.DigestBytes) (v : MembershipChallenge) :
    (c.cacheQuery (.inr d) v) (.inr e) = if e = d then some v else c (.inr e) := by
  by_cases h : e = d
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]; simp [h]

theorem fOf_insertH (a : List UInt8) (u : Common.DigestBytes) (b : List UInt8) :
    fOf (c.cacheQuery (.inl a) u) b = if b = a then u else fOf c b := by
  simp only [fOf, vcache_inl_inl]
  split_ifs <;> rfl

theorem domH_insertH (a : List UInt8) (u : Common.DigestBytes) :
    domH (c.cacheQuery (.inl a) u) = insert a (domH c) := by
  ext b
  simp only [domH, Set.mem_ofPred_eq, Set.mem_insert_iff, vcache_inl_inl]
  by_cases h : b = a <;> simp [h]

theorem domG_insertH (a : List UInt8) (u : Common.DigestBytes) : domG (c.cacheQuery (.inl a) u) = domG c := by
  ext d; simp [domG]

theorem fOf_insertG (d : Common.DigestBytes) (v : MembershipChallenge) : fOf (c.cacheQuery (.inr d) v) = fOf c := by
  funext a; simp [fOf]

theorem domH_insertG (d : Common.DigestBytes) (v : MembershipChallenge) : domH (c.cacheQuery (.inr d) v) = domH c := by
  ext a; simp [domH]

theorem domG_insertG (d : Common.DigestBytes) (v : MembershipChallenge) :
    domG (c.cacheQuery (.inr d) v) = insert d (domG c) := by
  ext e
  simp only [domG, Set.mem_ofPred_eq, Set.mem_insert_iff, vcache_inr_inr]
  by_cases h : e = d <;> simp [h]

end Insert

/-- **A fresh answer of `H` keeps a cache good** unless it collides with a cached answer, is a
digest the query or a cached input carries, or is a root with cached challenges. -/
theorem good_insertH {r : ℕ} {c : VCache} (hc : Good r c) {a : List UInt8} (ha : c (.inl a) = none)
    {u : Common.DigestBytes} (hran : ∀ b ∈ domH c, fOf c b ≠ u)
    (hch : ∀ b, (b = a ∨ b ∈ domH c) → u ∉ chunks b) (hG : c (.inr u) = none) :
    Good r (c.cacheQuery (.inl a) u) := by
  have haD : a ∉ domH c := fun h ↦ h ha
  refine ⟨?_, ?_⟩
  · rw [domH_insertH]
    intro b₁ hb₁ b₂ hb₂ he
    simp only [fOf_insertH] at he
    have m₁ := Set.mem_insert_iff.mp hb₁
    have m₂ := Set.mem_insert_iff.mp hb₂
    by_cases h1 : b₁ = a <;> by_cases h2 : b₂ = a
    · rw [h1, h2]
    · rw [ite_eq_left h1, ite_eq_right h2] at he
      exact absurd he.symm (hran b₂ (m₂.resolve_left h2))
    · rw [ite_eq_right h1, ite_eq_left h2] at he
      exact absurd he (hran b₁ (m₁.resolve_left h1))
    · rw [ite_eq_right h1, ite_eq_right h2] at he
      exact hc.1 (m₁.resolve_left h1) (m₂.resolve_left h2) he
  · intro d v hd w hw hroot hcheck
    rw [vcache_inl_inr] at hd
    set f' := fOf (c.cacheQuery (.inl a) u)
    have hnot : a ∉ commitIn f' w := by
      intro hmem
      have hfa : f' a = u := by simp [f', fOf_insertH]
      rcases commitIn_parent f' w a hmem with h | ⟨b, hb, h⟩
      · rw [hfa, hroot] at h
        rw [← h] at hd
        rw [hd] at hG
        cases hG
      · have hb' := hw hb
        rw [domH_insertH] at hb'
        exact hch b (Set.mem_insert_iff.mp hb') (by rw [← hfa]; exact h)
    have hsub : commitIn f' w ⊆ domH c := fun b hb ↦ by
      have := hw hb
      rw [domH_insertH] at this
      rcases Set.mem_insert_iff.mp this with rfl | h
      · exact absurd hb hnot
      · exact h
    have hagree : ∀ b ∈ commitIn f' w, f' b = fOf c b := fun b hb ↦ by
      have hba : b ≠ a := fun h ↦ hnot (h ▸ hb)
      simp [f', fOf_insertH, hba]
    obtain ⟨hin, hcom⟩ := commitIn_congr f' (fOf c) w hagree
    have hsub' : commitIn (fOf c) w ⊆ domH c := by rw [hin]; exact hsub
    exact hc.2 d v hd w hsub' (hcom.trans hroot) hcheck

/-- **Fresh challenges keep a cache good** when every matrix whose commitment's inputs are cached
and which commits to the root passes the test on them only if it is a codeword. -/
theorem good_insertG {r : ℕ} {c : VCache} (hc : Good r c) {d : Common.DigestBytes} {v :
    MembershipChallenge}
    (hv : ∀ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c → commitCellsWithHash (fOf c) w = d →
      membershipCheck (v 1) w = true → w ∈ (leanDaErasureCode r).code) :
    Good r (c.cacheQuery (.inr d) v) := by
  rw [Good, fOf_insertG, domH_insertG]
  refine ⟨hc.1, fun e v' he ↦ ?_⟩
  rw [vcache_inr_inr] at he
  split_ifs at he with hed
  · cases he; subst hed; exact hv
  · exact hc.2 e v' he

/-! ## One step -/

/-- The caches one step of the world can reach. -/
theorem vStep (t : (unifSpec + VS).Domain) (c : VCache) {z} (hz : z ∈ support
    ((VS.romImpl t).run c)) :
    z.2 = c ∨ (∃ a u, t = .inr (.inl a) ∧ c (.inl a) = none ∧ z.2 = c.cacheQuery (.inl a) u) ∨
      (∃ d v, t = .inr (.inr d) ∧ c (.inr d) = none ∧ z.2 = c.cacheQuery (.inr d) v) := by
  rcases t with n | t
  · rw [roSim.run_apply_inl] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Or.inl rfl
  · rw [romImpl_inr_run] at hz
    rcases h : c t with _ | v
    · rw [roStep_of_none h] at hz
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rcases t with a | d
      · exact Or.inr (Or.inl ⟨a, u, rfl, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨d, u, rfl, h, rfl⟩)
    · rw [roStep_of_some h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl rfl

/-- Queries of the world's oracles, one each. -/
def vCalls : (unifSpec + VS).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Queries of the challenges, one each. -/
def gvCalls : (unifSpec + VS).Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

/-- The world's side invariant: finitely many cached entries. -/
def VFin (c : VCache) : Prop := (domH c).Finite ∧ (domG c).Finite

/-- The cached entries. -/
noncomputable def vSize (c : VCache) : ℕ := (domH c).ncard + (domG c).ncard

/-- **The probability that a fresh answer of `H` spoils a good cache** is at most `65 N / 2^256`
for a cache of fewer than `N` entries. -/
theorem prob_insertH_le {r : ℕ} {c : VCache} (hc : Good r c) (hfin : VFin c) {a : List UInt8}
    (ha : c (.inl a) = none) (N : ℕ) (hN : vSize c + 1 ≤ N) :
    Pr{let u ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[¬ Good r (c.cacheQuery (.inl a) u)] ≤
      65 * N / 2 ^ 256 := by
  classical
  let V : Finset Common.DigestBytes := hfin.1.toFinset.image (fOf c) ∪
    (insert a hfin.1.toFinset).biUnion chunks ∪ hfin.2.toFinset
  have hmem : ∀ u : Common.DigestBytes, ¬ Good r (c.cacheQuery (.inl a) u) → u ∈ V := by
    intro u hu
    by_contra hV
    refine hu (good_insertH hc ha (fun b hb he ↦ hV ?_) (fun b hb hch ↦ hV ?_) ?_)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨b, hfin.1.mem_toFinset.mpr hb, he⟩))
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, ?_, hch⟩))
      rcases hb with rfl | hb
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hfin.1.mem_toFinset.mpr hb)
    · by_contra hG
      exact hV (Finset.mem_union_right _ (hfin.2.mem_toFinset.mpr hG))
  have hV : (V.card : ℝ≥0∞) ≤ 65 * N := by
    have h1 : (hfin.1.toFinset.image (fOf c)).card ≤ (domH c).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfin.1]; exact Finset.card_image_le
    have h2 : ((insert a hfin.1.toFinset).biUnion chunks).card ≤ 64 * ((domH c).ncard + 1) := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun b _ ↦ card_chunks_le b).trans ?_
      rw [Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card _ hfin.1]
      have := Finset.card_insert_le a hfin.1.toFinset
      nlinarith
    have h3 : hfin.2.toFinset.card = (domG c).ncard := (Set.ncard_eq_toFinset_card _ hfin.2).symm
    have hcard : V.card ≤ 65 * N := by
      refine (Finset.card_union_le _ _).trans ?_
      refine (add_le_add (Finset.card_union_le _ _) le_rfl).trans ?_
      unfold vSize at hN
      omega
    exact_mod_cast hcard
  calc Pr{let u ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[¬ Good r (c.cacheQuery (.inl a) u)]
      ≤ Pr{let u ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[u ∈ V] := prEvent_mono _ _ _ fun u hu ↦ hmem u hu
    _ = V.card / 2 ^ 256 := by
        rw [SampleableType.prEvent_uniformSample, card_digest, Finset.filter_mem_eq_inter,
          Finset.univ_inter]
        norm_num
    _ ≤ 65 * N / 2 ^ 256 := by gcongr

/-- **The probability that fresh challenges spoil a good cache** is at most `(2^14 - 1) / 2^192`: the one
matrix committed to the root is fixed before they are drawn. -/
theorem prob_insertG_le {r : ℕ} {c : VCache} (hc : Good r c) (d : Common.DigestBytes) :
    Pr{let v ← ($ᵗ MembershipChallenge : ProbComp MembershipChallenge)}[¬ Good r (c.cacheQuery
        (.inr d) v)] ≤
      (2 ^ 14 - 1) / 2 ^ 192 := by
  classical
  by_cases hS : ∃ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c ∧
      commitCellsWithHash (fOf c) w = d ∧ w ∉ (leanDaErasureCode r).code
  · obtain ⟨w₀, hw₀, hd₀, hn₀⟩ := hS
    calc Pr{let v ← ($ᵗ MembershipChallenge : ProbComp MembershipChallenge)}[¬ Good r
          (c.cacheQuery (.inr d) v)]
        ≤ Pr{let v ← ($ᵗ MembershipChallenge : ProbComp MembershipChallenge)}[(checker r).check v w₀ = true] := by
          refine prEvent_mono _ _ _ fun v hv ↦ ?_
          by_contra hck
          refine hv (good_insertG hc fun w hw hd hm ↦ ?_)
          have := commit_unique hc.1 hw hw₀ (hd.trans hd₀.symm)
          subst this
          exact absurd hm hck
      _ = Pr{let x ← (fun l ↦ (checker r).check l w₀) <$> ($ᵗ MembershipChallenge)}[x = true] :=
          (prEvent_map ($ᵗ MembershipChallenge) (fun l ↦ (checker r).check l w₀) (· = true)).symm
      _ ≤ (2 ^ 14 - 1) / 2 ^ 192 := checker_sound r w₀ hn₀
  · push Not at hS
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun v _ hv ↦
      hv (good_insertG hc fun w hw hd hm ↦ hS w hw hd)) zero_le

/-- **A run of the world ends in a bad cache** with probability at most
`N · 65 N / 2^256 + Q_G · (2^14 - 1) / 2^192`, for at most `N` queries, `Q_G` of them of the challenges. -/
theorem prob_not_good_le (r : ℕ) {α : Type} (Y : OracleComp (unifSpec + VS) α) (N QG : ℕ)
    (h1 : QueryCostAtMost Y vCalls N) (h2 : QueryCostAtMost Y gvCalls QG) :
    Pr{let z ← (simulateQ VS.romImpl Y).run ∅}[¬ Good r z.2] ≤
      N * (65 * N / 2 ^ 256) + QG * ((2 ^ 14 - 1) / 2 ^ 192) := by
  classical
  have hfin0 : VFin ∅ := ⟨by simp [domH], by simp [domG]⟩
  have hsize0 : vSize ∅ = 0 := by simp [vSize, domH, domG]
  have h := prEvent_run_bad_le₂ VS.romImpl (fun c ↦ ¬ Good r c) VFin vCalls gvCalls vSize N
    (65 * N / 2 ^ 256) ((2 ^ 14 - 1) / 2 ^ 192) ?_ ?_ ?_ Y N QG h1 h2 ∅ hfin0 (by rw [hsize0]; omega)
  · refine h.trans (le_of_eq ?_)
    simp [good_empty r]
  · intro t c hc z hz
    rcases vStep t c hz with h | ⟨a, u, -, -, h⟩ | ⟨d, v, -, -, h⟩
    · rw [h]; exact hc
    · rw [h]
      exact ⟨by rw [domH_insertH]; exact hc.1.insert a, by rw [domG_insertH]; exact hc.2⟩
    · rw [h]
      exact ⟨by rw [domH_insertG]; exact hc.1, by rw [domG_insertG]; exact hc.2.insert d⟩
  · intro t c hc z hz
    rcases vStep t c hz with h | ⟨a, u, rfl, -, h⟩ | ⟨d, v, rfl, -, h⟩
    · rw [h]; omega
    · rw [h]
      have := Set.ncard_insert_le a (domH c)
      simp only [vSize, vCalls, domH_insertH, domG_insertH]
      omega
    · rw [h]
      have := Set.ncard_insert_le d (domG c)
      simp only [vSize, vCalls, domH_insertG, domG_insertG]
      omega
  · intro t c hfin hgood hN
    simp only [not_not] at hgood
    have hkeep : ∀ {β : Type} (X : ProbComp (β × VCache)), (∀ z ∈ support X, z.2 = c) →
        Pr{let z ← X}[¬ Good r z.2] = 0 := fun X hX ↦
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hb ↦ hb ((hX z hz).symm ▸ hgood)
    rcases t with n | a | d
    · refine le_of_eq_of_le (hkeep _ fun z hz ↦ ?_) zero_le
      rcases vStep _ c hz with h | ⟨a, u, h, -, -⟩ | ⟨d, v, h, -, -⟩
      · exact h
      · cases h
      · cases h
    · rw [romImpl_inr_run]
      rcases h : c (.inl a) with _ | u
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        refine (prob_insertH_le hgood hfin h N (by simpa [vCalls] using hN)).trans ?_
        simp [vCalls, gvCalls]
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hgood]
    · rw [romImpl_inr_run]
      rcases h : c (.inr d) with _ | v
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        refine (prob_insertG_le hgood d).trans ?_
        simp [vCalls, gvCalls]
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hgood]

/-! ## Replaying a coin-free run against its final cache -/

/-- **A cache as a partial function**: the oracles answered by its entries, coins by none. -/
def replayImpl (c : VCache) : QueryImpl (unifSpec + VS) Option
  | .inl _ => none
  | .inr t => c t

/-- **A coin-free run is read off its final cache**: replayed against it, the computation
returns the run's result. -/
theorem replay_of_mem_support {α : Type} (X : OracleComp (unifSpec + VS) α) (hX : NoCoins X)
    (c : VCache) {z : α × VCache} (hz : z ∈ support ((simulateQ VS.romImpl X).run c)) :
    c ≤ z.2 ∧ simulateQ (replayImpl z.2) X = some z.1 := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, rfl⟩
  | query_bind t k ih =>
    rcases t with n | t
    · exact hX.elim
    have hk : ∀ u, NoCoins (k u) := hX
    change z ∈ support ((simulateQ VS.romImpl (hq t >>= k)).run c) at hz
    rw [simulateQ_bind, StateT.run_bind, run_hq, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨hcw, hwt⟩ := le_of_mem_support_roStep t c hw
    obtain ⟨hwz, hrep⟩ := ih w.1 (hk w.1) w.2 hz
    refine ⟨hcw.trans hwz, ?_⟩
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map]
    change (z.2 t >>= fun u ↦ simulateQ (replayImpl z.2) (k u)) = some z.1
    rw [hwz hwt]
    exact hrep

end LeanDa
