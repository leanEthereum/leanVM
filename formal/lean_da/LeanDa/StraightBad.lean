module

public import LeanDa.StraightTree
public import Common.Duplex.Vec
public import LeanDa.WithHash

@[expose] public section

/-!
# The straight-line world and its bad events

The world of the straight-line proof of code binding (`LeanDa.Straight`): `H` and the draws `G`
two lazily sampled random oracles, `G` on a root and a label (`GSpec`, the duplex lemma's world).
Its caches are **good** (`Good`) when `H` is injective on its cached inputs and, for every root
`d` and the draw the nonce search would select so far (`FirstValid`: the first cached nonce's draw
with a valid proof of work), every matrix whose commitment's inputs are all cached, which commits
to `d` and passes the membership test on its challenge, is a codeword.

* **A fresh answer of `H` keeps a cache good** unless it collides with a cached answer, is a
  digest a cached input or the query carries (`chunks`), or is a root a draw is cached for
  (`good_insertH`): a matrix whose tree the new entry completes would hash a node to a digest an
  older input already carries. At most `65 N` values for a cache of `N` inputs and roots.
* **A fresh draw keeps a cache good** unless the search would select it, a valid proof of work
  after no valid cached one, and its challenge accepts the one matrix committed to the root (`H`
  injective: `commit_unique`), fixed before, which is not a codeword: a valid proof of work and an
  accepting challenge are independent, at most `2^-10 · (2^13 - 1) / 2^128` (`prob_insertG_le`).
* So a run of `Q₁` queries, `Q₂` of them of draws, ends in a bad cache with probability at most
  `Q₁ · 65 N / 2^256 + Q₂ · 2^-10 · (2^13 - 1) / 2^128` (`prob_run_not_good_le`, by the bad-event
  budget with two weights, `prEvent_run_bad_le₂`).
* **The verifier's reading of a root's draws**, label by label as the nonce search tries the
  nonces, spoils a good cache with probability at most `(2^13 - 1) / 2^128` in all
  (`prob_readVec_not_good_le`): it stops selecting at its first valid draw, whose challenge is
  uniform whatever the proofs of work.
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

/-- **The straight-line world's oracles**: coins, `H`, and the challenges as a random oracle of
the draws, one per root and label (`GSpec`, the duplex lemma's world). -/
abbrev GW := GSpec (List UInt8) DigestBytes Common.DigestBytes Draw nLabels

/-- Its cache. -/
abbrev GCache := GW.QueryCache

/-- The hash function of a cache: its cached answers, `default` elsewhere. -/
def fOf (c : GCache) (a : List UInt8) : Common.DigestBytes := (c (.inl a)).getD default

/-- The inputs of `H` a cache holds. -/
def domH (c : GCache) : Set (List UInt8) := {a | c (.inl a) ≠ none}

/-- The roots a cache holds a draw of. -/
def domG (c : GCache) : Set Common.DigestBytes := {d | ∃ j, c (.inr (d, j)) ≠ none}

/-- **The draw the nonce search would select so far**: label `j` of root `d`, a nonce's, is
cached with a valid proof of work, and no earlier nonce's cached draw has one. -/
def FirstValid (c : GCache) (d : Common.DigestBytes) (j : Fin nLabels) (x : Draw) : Prop :=
  j.val ≠ 0 ∧ c (.inr (d, j)) = some x ∧ powValid x.2.lane = true ∧
    ∀ i : Fin nLabels, i.val ≠ 0 → i.val < j.val → ∀ y, c (.inr (d, i)) = some y →
      powValid y.2.lane = false

/-- **A good cache**: `H` injective on its cached inputs, and for every root and the draw the
nonce search would select so far, every matrix whose commitment's inputs are cached, which
commits to the root and passes the membership test on that draw's challenge, a codeword. -/
def Good (r : ℕ) (c : GCache) : Prop :=
  Set.InjOn (fOf c) (domH c) ∧ ∀ d j x, FirstValid c d j x →
    ∀ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c → commitCellsWithHash (fOf c) w = d →
      membershipCheck x.1 w = true → w ∈ (leanDaErasureCode r).code

theorem good_empty (r : ℕ) : Good r ∅ :=
  ⟨fun a ha ↦ (ha rfl).elim, fun _ _ _ h ↦ absurd h.2.1 (by simp)⟩

theorem fOf_of_mem {c : GCache} {a : List UInt8} {u : Common.DigestBytes} (h : c (.inl a) = some u) :
    fOf c a = u := by simp [fOf, h]

theorem cache_inl_eq_fOf {c : GCache} {a : List UInt8} (h : a ∈ domH c) :
    c (.inl a) = some (fOf c a) := by
  rcases hc : c (.inl a) with _ | u
  · exact absurd hc h
  · simp [fOf, hc]

section Insert

variable (c : GCache)

theorem gcache_inl_inl (a b : List UInt8) (u : Common.DigestBytes) :
    (c.cacheQuery (.inl a) u) (.inl b) = if b = a then some u else c (.inl b) := by
  by_cases h : b = a
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]; simp [h]

theorem gcache_inl_inr (a : List UInt8) (u : Common.DigestBytes) (e : Common.DigestBytes × Fin nLabels) :
    (c.cacheQuery (.inl a) u) (.inr e) = c (.inr e) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem gcache_inr_inl (e : Common.DigestBytes × Fin nLabels) (x : Draw) (a : List UInt8) :
    (c.cacheQuery (.inr e) x) (.inl a) = c (.inl a) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem gcache_inr_inr (e e' : Common.DigestBytes × Fin nLabels) (x : Draw) :
    (c.cacheQuery (.inr e) x) (.inr e') = if e' = e then some x else c (.inr e') := by
  by_cases h : e' = e
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]; simp [h]

theorem fOf_insertH (a : List UInt8) (u : Common.DigestBytes) (b : List UInt8) :
    fOf (c.cacheQuery (.inl a) u) b = if b = a then u else fOf c b := by
  simp only [fOf, gcache_inl_inl]
  split_ifs <;> rfl

theorem domH_insertH (a : List UInt8) (u : Common.DigestBytes) :
    domH (c.cacheQuery (.inl a) u) = insert a (domH c) := by
  ext b
  simp only [domH, Set.mem_ofPred_eq, Set.mem_insert_iff, gcache_inl_inl]
  by_cases h : b = a <;> simp [h]

theorem domG_insertH (a : List UInt8) (u : Common.DigestBytes) :
    domG (c.cacheQuery (.inl a) u) = domG c := by
  ext d; simp [domG]

theorem firstValid_insertH (a : List UInt8) (u : Common.DigestBytes) (d : Common.DigestBytes)
    (j : Fin nLabels) (x : Draw) :
    FirstValid (c.cacheQuery (.inl a) u) d j x ↔ FirstValid c d j x := by
  simp only [FirstValid, gcache_inl_inr]

theorem fOf_insertG (e : Common.DigestBytes × Fin nLabels) (x : Draw) :
    fOf (c.cacheQuery (.inr e) x) = fOf c := by
  funext a; simp [fOf]

theorem domH_insertG (e : Common.DigestBytes × Fin nLabels) (x : Draw) :
    domH (c.cacheQuery (.inr e) x) = domH c := by
  ext a; simp [domH]

theorem domG_insertG (e : Common.DigestBytes × Fin nLabels) (x : Draw) :
    domG (c.cacheQuery (.inr e) x) = insert e.1 (domG c) := by
  ext d
  simp only [domG, Set.mem_ofPred_eq, Set.mem_insert_iff, gcache_inr_inr]
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : (d, j) = e
    · exact Or.inl (by rw [← h])
    · exact Or.inr ⟨j, by simpa [h] using hj⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨e.2, by simp⟩
    · by_cases h : (d, j) = e
      · exact ⟨j, by simp [h]⟩
      · exact ⟨j, by simpa [h] using hj⟩

end Insert

/-- **A fresh answer of `H` keeps a cache good** unless it collides with a cached answer, is a
digest the query or a cached input carries, or is a root a draw is cached for. -/
theorem good_insertH {r : ℕ} {c : GCache} (hc : Good r c) {a : List UInt8} (ha : c (.inl a) = none)
    {u : Common.DigestBytes} (hran : ∀ b ∈ domH c, fOf c b ≠ u)
    (hch : ∀ b, (b = a ∨ b ∈ domH c) → u ∉ chunks b) (hG : u ∉ domG c) :
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
  · intro d j x hd w hw hroot hcheck
    rw [firstValid_insertH] at hd
    set f' := fOf (c.cacheQuery (.inl a) u)
    have hnot : a ∉ commitIn f' w := by
      intro hmem
      have hfa : f' a = u := by simp [f', fOf_insertH]
      rcases commitIn_parent f' w a hmem with h | ⟨b, hb, h⟩
      · rw [hfa, hroot] at h
        subst h
        exact hG ⟨j, by rw [hd.2.1]; simp⟩
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
    exact hc.2 d j x hd w hsub' (hcom.trans hroot) hcheck

/-- The condition under which a fresh draw is the one the nonce search would select so far: a
nonce's, with a valid proof of work, and no earlier nonce's cached draw valid. -/
def NewFirst (c : GCache) (d : Common.DigestBytes) (j : Fin nLabels) (x : Draw) : Prop :=
  j.val ≠ 0 ∧ powValid x.2.lane = true ∧
    ∀ i : Fin nLabels, i.val ≠ 0 → i.val < j.val → ∀ y, c (.inr (d, i)) = some y →
      powValid y.2.lane = false

/-- **A fresh draw keeps a cache good** when, if the nonce search would select it, every matrix
whose commitment's inputs are cached and which commits to the root passes the test on its
challenge only if it is a codeword. -/
theorem good_insertG {r : ℕ} {c : GCache} (hc : Good r c) {d : Common.DigestBytes} {j : Fin nLabels}
    (hfresh : c (.inr (d, j)) = none) {x : Draw}
    (hv : NewFirst c d j x → ∀ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c →
      commitCellsWithHash (fOf c) w = d → membershipCheck x.1 w = true →
        w ∈ (leanDaErasureCode r).code) :
    Good r (c.cacheQuery (.inr (d, j)) x) := by
  rw [Good, fOf_insertG, domH_insertG]
  refine ⟨hc.1, fun e k y hk ↦ ?_⟩
  obtain ⟨hk0, hky, hkv, hkpre⟩ := hk
  rw [gcache_inr_inr] at hky
  by_cases hek : (e, k) = (d, j)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hek
    simp only [↓reduceIte, Option.some.injEq] at hky
    subst hky
    refine hv ⟨hk0, hkv, fun i hi0 hik y' hy' ↦ hkpre i hi0 hik y' ?_⟩
    have hne : (e, i) ≠ (e, k) := fun h ↦ by
      have := congrArg Prod.snd h
      simp only at this
      omega
    rw [gcache_inr_inr]
    simp only [hne, ↓reduceIte]
    exact hy'
  · simp only [hek, ↓reduceIte] at hky
    refine hc.2 e k y ⟨hk0, hky, hkv, fun i hi0 hik y' hy' ↦ hkpre i hi0 hik y' ?_⟩
    rw [gcache_inr_inr]
    split_ifs with hei
    · rw [hei] at hy'; rw [hy'] at hfresh; cases hfresh
    · exact hy'

/-! ## One step -/

/-- The caches one step of the world can reach. -/
theorem gStep (t : (unifSpec + GW).Domain) (c : GCache) {z} (hz : z ∈ support
    ((GW.romImpl t).run c)) :
    z.2 = c ∨ (∃ a u, t = .inr (.inl a) ∧ c (.inl a) = none ∧ z.2 = c.cacheQuery (.inl a) u) ∨
      (∃ e x, t = .inr (.inr e) ∧ c (.inr e) = none ∧ z.2 = c.cacheQuery (.inr e) x) := by
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
      rcases t with a | e
      · exact Or.inr (Or.inl ⟨a, u, rfl, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨e, u, rfl, h, rfl⟩)
    · rw [roStep_of_some h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl rfl

/-- Queries of the world's oracles, one each. -/
def hgCalls : (unifSpec + GW).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Queries of the draws, one each. -/
abbrev gwCalls : (unifSpec + GW).Domain → ℕ :=
  gCalls (Msg := List UInt8) (Dg := DigestBytes) (Root := Common.DigestBytes) (Z := Draw) (n := nLabels)

/-- The world's side invariant: finitely many cached inputs of `H` and roots of draws. -/
def GFin (c : GCache) : Prop := (domH c).Finite ∧ (domG c).Finite

/-- The cached inputs of `H` and roots of draws. -/
noncomputable def gSize (c : GCache) : ℕ := (domH c).ncard + (domG c).ncard

theorem gFin_step (t : (unifSpec + GW).Domain) (c : GCache) (hc : GFin c) {z}
    (hz : z ∈ support ((GW.romImpl t).run c)) : GFin z.2 := by
  rcases gStep t c hz with h | ⟨a, u, -, -, h⟩ | ⟨e, x, -, -, h⟩
  · rw [h]; exact hc
  · rw [h]
    exact ⟨by rw [domH_insertH]; exact hc.1.insert a, by rw [domG_insertH]; exact hc.2⟩
  · rw [h]
    exact ⟨by rw [domH_insertG]; exact hc.1, by rw [domG_insertG]; exact hc.2.insert e.1⟩

theorem gSize_step (t : (unifSpec + GW).Domain) (c : GCache) (_hc : GFin c) {z}
    (hz : z ∈ support ((GW.romImpl t).run c)) : gSize z.2 ≤ gSize c + hgCalls t := by
  rcases gStep t c hz with h | ⟨a, u, rfl, -, h⟩ | ⟨e, x, rfl, -, h⟩
  · rw [h]; omega
  · rw [h]
    have := Set.ncard_insert_le a (domH c)
    simp only [gSize, hgCalls, domH_insertH, domG_insertH]
    omega
  · rw [h]
    have := Set.ncard_insert_le e.1 (domG c)
    simp only [gSize, hgCalls, domH_insertG, domG_insertG]
    omega

/-- **The probability that a fresh answer of `H` spoils a good cache** is at most `65 N / 2^256`
for a cache of fewer than `N` cached inputs and roots. -/
theorem prob_insertH_le {r : ℕ} {c : GCache} (hc : Good r c) (hfin : GFin c) {a : List UInt8}
    (ha : c (.inl a) = none) (N : ℕ) (hN : gSize c + 1 ≤ N) :
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
    · intro hG
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
      unfold gSize at hN
      omega
    exact_mod_cast hcard
  calc Pr{let u ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[¬ Good r (c.cacheQuery (.inl a) u)]
      ≤ Pr{let u ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[u ∈ V] := prEvent_mono _ _ _ fun u hu ↦ hmem u hu
    _ = V.card / 2 ^ 256 := by
        rw [SampleableType.prEvent_uniformSample, card_digest, Finset.filter_mem_eq_inter,
          Finset.univ_inter]
        norm_num
    _ ≤ 65 * N / 2 ^ 256 := by gcongr

/-- **A fresh draw spoils a good cache** only if the nonce search would select it and its
challenge accepts the one non-codeword matrix committed to the root: a valid proof of work and an
accepting challenge, at most `2^-10 · (2^13 - 1) / 2^128` (`prob_valid_accept_le`). -/
theorem prob_insertG_le {r : ℕ} {c : GCache} (hc : Good r c) {d : Common.DigestBytes}
    {j : Fin nLabels} (hfresh : c (.inr (d, j)) = none) :
    Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ Good r (c.cacheQuery (.inr (d, j)) x)] ≤
      (2 ^ 13 - 1) / 2 ^ 138 := by
  classical
  by_cases hS : ∃ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c ∧
      commitCellsWithHash (fOf c) w = d ∧ w ∉ (leanDaErasureCode r).code
  · obtain ⟨w₀, hw₀, hd₀, hn₀⟩ := hS
    obtain ⟨i, hi⟩ := not_mem_code_row hn₀
    calc Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ Good r (c.cacheQuery (.inr (d, j)) x)]
        ≤ Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[
            powValid x.2.lane = true ∧ x.1 ∈ acceptSet (matrixRow w₀ i)] := by
          refine prEvent_mono _ _ _ fun x hx ↦ ?_
          by_contra hck
          refine hx (good_insertG hc hfresh fun hnew w hw hd hm ↦ ?_)
          have hw0 : w = w₀ := commit_unique hc.1 hw hw₀ (hd.trans hd₀.symm)
          rw [hw0] at hm
          exfalso
          apply hck
          refine ⟨hnew.2.1, ?_⟩
          rw [mem_acceptSet]
          exact (membershipCheck_iff x.1 w₀).mp hm i
      _ ≤ (2 ^ 13 - 1) / 2 ^ 138 := prob_valid_accept_le (card_acceptSet_le hi)
  · push Not at hS
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun x _ hx ↦
      hx (good_insertG hc hfresh fun _ w hw hd _ ↦ hS w hw hd)) zero_le

/-- **The budget of a run of the world**: from a good cache of at most `N - Q₁` cached inputs and
roots, a run of at most `Q₁` queries, `Q₂` of them of draws, ends in a bad cache with probability
at most `Q₁ · 65 N / 2^256 + Q₂ · 2^-10 · (2^13 - 1) / 2^128`. -/
theorem prob_run_not_good_le (r : ℕ) {α : Type} (Y : OracleComp (unifSpec + GW) α) (c₀ : GCache)
    (hg : Good r c₀) (hf : GFin c₀) (N Q₁ Q₂ : ℕ) (h1 : QueryCostAtMost Y hgCalls Q₁)
    (h2 : QueryCostAtMost Y gwCalls Q₂) (hN : gSize c₀ + Q₁ ≤ N) :
    Pr{let z ← (simulateQ GW.romImpl Y).run c₀}[¬ Good r z.2] ≤
      Q₁ * (65 * N / 2 ^ 256) + Q₂ * ((2 ^ 13 - 1) / 2 ^ 138) := by
  classical
  have h := prEvent_run_bad_le₂ GW.romImpl (fun c ↦ ¬ Good r c) GFin hgCalls gwCalls gSize N
    (65 * N / 2 ^ 256) ((2 ^ 13 - 1) / 2 ^ 138) (fun t c hc z hz ↦ gFin_step t c hc hz)
    (fun t c hc z hz ↦ gSize_step t c hc hz) ?_ Y Q₁ Q₂ h1 h2 c₀ hf hN
  · refine h.trans (le_of_eq ?_)
    simp [hg]
  · intro t c hfin hgood hN
    simp only [not_not] at hgood
    have hkeep : ∀ {β : Type} (X : ProbComp (β × GCache)), (∀ z ∈ support X, z.2 = c) →
        Pr{let z ← X}[¬ Good r z.2] = 0 := fun X hX ↦
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz hb ↦ hb ((hX z hz).symm ▸ hgood)
    rcases t with n | a | e
    · refine le_of_eq_of_le (hkeep _ fun z hz ↦ ?_) zero_le
      rcases gStep _ c hz with h | ⟨a, u, h, -, -⟩ | ⟨e, x, h, -, -⟩
      · exact h
      · cases h
      · cases h
    · rw [romImpl_inr_run]
      rcases h : c (.inl a) with _ | u
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        refine (prob_insertH_le hgood hfin h N (by simpa [hgCalls] using hN)).trans ?_
        simp [hgCalls, gwCalls, gCalls]
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hgood]
    · rw [romImpl_inr_run]
      rcases h : c (.inr e) with _ | x
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        obtain ⟨d, j⟩ := e
        refine (prob_insertG_le hgood h).trans ?_
        simp [hgCalls, gwCalls, gCalls]
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hgood]

/-- **A run of the world keeps the side invariant and grows by at most its queries.** -/
theorem run_gFin_gSize {α : Type} (Y : OracleComp (unifSpec + GW) α) (Q₁ : ℕ)
    (h1 : QueryCostAtMost Y hgCalls Q₁) (c₀ : GCache) (hf : GFin c₀) :
    ∀ z ∈ support ((simulateQ GW.romImpl Y).run c₀), GFin z.2 ∧ gSize z.2 ≤ gSize c₀ + Q₁ := by
  induction Y using OracleComp.inductionOn generalizing Q₁ c₀ with
  | pure a =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨hf, Nat.le_add_right _ _⟩
  | query_bind t k ih =>
    intro z hz
    rw [isWeightBound_query_bind_iff] at h1
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have hfw := gFin_step t c₀ hf hw
    have hsw := gSize_step t c₀ hf hw
    obtain ⟨hfz, hsz⟩ := ih w.1 (Q₁ - hgCalls t) (h1.2 w.1) w.2 hfw z hz
    exact ⟨hfz, by omega⟩

/-! ## The verifier's nonce search: one fresh try

The challenges of the adversary's root are read label by label (`readVec`), as the nonce search
tries the nonces. A fresh draw spoils a good cache only if it is the one the search selects, a
valid proof of work after invalid ones, and its challenge accepts the one non-codeword matrix
committed to the root; the search stops at its first valid draw, so along the reading at most one
fresh draw is selected, and its challenge is uniform whatever the proofs of work: the reading
spoils a good cache with probability at most `(2^13 - 1) / 2^128` (`prob_readVec_not_good_le`),
however many draws it samples. -/

/-- **The draws that can spoil a good cache**: if a fresh draw spoils it, the search would select
it and its challenge lies in a set of at most `2^13 - 1` challenges. -/
theorem not_good_insertG_sub {r : ℕ} {c : GCache} (hc : Good r c) {d : Common.DigestBytes}
    {j : Fin nLabels} (hfresh : c (.inr (d, j)) = none) :
    ∃ A : Finset E, A.card ≤ 2 ^ 13 - 1 ∧ ∀ x : Draw,
      ¬ Good r (c.cacheQuery (.inr (d, j)) x) → NewFirst c d j x ∧ x.1 ∈ A := by
  classical
  by_cases hS : ∃ w : Fin (r * 128) → Cell, commitIn (fOf c) w ⊆ domH c ∧
      commitCellsWithHash (fOf c) w = d ∧ w ∉ (leanDaErasureCode r).code
  · obtain ⟨w₀, hw₀, hd₀, hn₀⟩ := hS
    obtain ⟨i, hi⟩ := not_mem_code_row hn₀
    refine ⟨acceptSet (matrixRow w₀ i), card_acceptSet_le hi, fun x hx ↦ ?_⟩
    by_contra hck
    refine hx (good_insertG hc hfresh fun hnew w hw hd hm ↦ ?_)
    have hw0 : w = w₀ := commit_unique hc.1 hw hw₀ (hd.trans hd₀.symm)
    rw [hw0] at hm
    exfalso
    apply hck
    refine ⟨hnew, ?_⟩
    rw [mem_acceptSet]
    exact (membershipCheck_iff x.1 w₀).mp hm i
  · push Not at hS
    refine ⟨∅, by simp, fun x hx ↦ absurd (good_insertG hc hfresh fun _ w hw hd _ ↦ hS w hw hd) hx⟩

/-- No cached nonce's draw of root `d` below label `k` has a valid proof of work. -/
def OpenBelow (c : GCache) (d : Common.DigestBytes) (k : ℕ) : Prop :=
  ∀ i : Fin nLabels, i.val ≠ 0 → i.val < k → ∀ y, c (.inr (d, i)) = some y →
    powValid y.2.lane = false

noncomputable instance (c : GCache) (d : Common.DigestBytes) (k : ℕ) :
    Decidable (OpenBelow c d k) := Classical.propDecidable _

/-- The labels of root `d` below `k` are cached. -/
def CoveredBelow (c : GCache) (d : Common.DigestBytes) (k : ℕ) : Prop :=
  ∀ i : Fin nLabels, i.val < k → c (.inr (d, i)) ≠ none

theorem openBelow_mono {c : GCache} {d : Common.DigestBytes} {k k' : ℕ} (hk : k' ≤ k)
    (h : OpenBelow c d k) : OpenBelow c d k' :=
  fun i hi0 hik ↦ h i hi0 (by omega)

/-- A bad final cache ignores a pure last step. -/
theorem prEvent_run_bind_pure {α β : Type} (r : ℕ) (X : OracleComp (unifSpec + GW) α) (f : α → β)
    (c : GCache) :
    Pr{let z ← (simulateQ GW.romImpl (X >>= fun a ↦ pure (f a))).run c}[¬ Good r z.2] =
      Pr{let z ← (simulateQ GW.romImpl X).run c}[¬ Good r z.2] := by
  rw [simulateQ_bind, StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure]
  rw [bind_pure_comp, prEvent_map]

/-- An event after a bind is at most the prefix-weighted sum of bounds of the continuation's. -/
theorem prEvent_bind_le_tsum {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (P : β → Prop)
    (g : α → ℝ≥0∞) (hg : ∀ x ∈ support mx, Pr{let y ← f x}[P y] ≤ g x) :
    Pr{let y ← mx >>= f}[P y] ≤ ∑' x, Pr{let z ← mx}[z = x] * g x := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : x ∈ support mx
  · gcongr; exact hg x hx
  · simp [prEvent_eq_zero_of_not_mem_support mx hx]

/-- **A fresh draw at label `k`, then the rest of the reading**: at most `(2^13 - 1) / 2^128` when
no earlier nonce's draw is valid, nothing otherwise. -/
theorem prob_fresh_step_le {β : Type} {r : ℕ} {c : GCache} (hc : Good r c) {d : Common.DigestBytes}
    {j : Fin nLabels} (hfresh : c (.inr (d, j)) = none) (F : Draw → ProbComp (β × GCache))
    (hF : ∀ x, Good r (c.cacheQuery (.inr (d, j)) x) →
      Pr{let z ← F x}[¬ Good r z.2] ≤
        if OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1) then (2 ^ 13 - 1) / 2 ^ 128 else 0) :
    Pr{let z ← ($ᵗ Draw : ProbComp Draw) >>= F}[¬ Good r z.2] ≤
      if OpenBelow c d j.val then (2 ^ 13 - 1) / 2 ^ 128 else 0 := by
  classical
  obtain ⟨A, hA, hsub⟩ := not_good_insertG_sub hc hfresh
  set ε : ℝ≥0∞ := (2 ^ 13 - 1) / 2 ^ 128
  -- the continuation's bound
  let g : Draw → ℝ≥0∞ := fun x ↦
    (if NewFirst c d j x ∧ x.1 ∈ A then 1 else 0) +
      (if OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1) then ε else 0)
  have hFg : ∀ x ∈ support ($ᵗ Draw : ProbComp Draw), Pr{let z ← F x}[¬ Good r z.2] ≤ g x := by
    intro x _
    by_cases hg : Good r (c.cacheQuery (.inr (d, j)) x)
    · exact (hF x hg).trans le_add_self
    · refine (prEvent_le_one _).trans (le_add_right ?_)
      rw [ite_eq_left (hsub x hg)]
  refine (prEvent_bind_le_tsum _ F _ g hFg).trans ?_
  -- the weighted sum
  have hsplit : ∑' x, Pr{let z ← ($ᵗ Draw : ProbComp Draw)}[z = x] * g x =
      Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[NewFirst c d j x ∧ x.1 ∈ A] +
        ε * Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[
          OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1)] := by
    rw [prEvent_eq_tsum_ite _ (fun x : Draw ↦ NewFirst c d j x ∧ x.1 ∈ A),
      prEvent_eq_tsum_ite _ (fun x : Draw ↦ OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1)),
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun x ↦ ?_
    simp only [g]
    split_ifs <;> ring
  rw [hsplit]
  -- an open prefix and a new invalid draw keep it open
  have hopen : ∀ x, OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1) →
      OpenBelow c d j.val ∧ (j.val ≠ 0 → powValid x.2.lane = false) := by
    intro x hx
    refine ⟨fun i hi0 hik y hy ↦ hx i hi0 (by omega) y ?_, fun hj0 ↦ hx j hj0 (by omega) x
      (by simp)⟩
    have hne : (d, i) ≠ (d, j) := fun h ↦ by
      have := congrArg Prod.snd h
      simp only at this
      omega
    rw [gcache_inr_inr]
    simp only [hne, ↓reduceIte]
    exact hy
  by_cases hO : OpenBelow c d j.val
  · simp only [hO, ↓reduceIte]
    by_cases hj0 : j.val = 0
    · -- the seed's draw is never selected
      have h0 : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[NewFirst c d j x ∧ x.1 ∈ A] = 0 :=
        prEvent_eq_zero_of_forall_mem_support _ _ fun x _ hx ↦ hx.1.1 hj0
      rw [h0, zero_add]
      exact mul_le_of_le_one_right' (prEvent_le_one _)
    · -- a selected draw needs a valid proof of work; otherwise the prefix stays open
      have h1 : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[NewFirst c d j x ∧ x.1 ∈ A] ≤
          Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true ∧ x.1 ∈ A] :=
        prEvent_mono _ _ _ fun x hx ↦ ⟨hx.1.2.1, hx.2⟩
      have h2 : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[
          OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1)] ≤
          Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ powValid x.2.lane = true] :=
        prEvent_mono _ _ _ fun x hx h ↦ by rw [(hopen x hx).2 hj0] at h; cases h
      have hAε : (A.card : ℝ≥0∞) / Fintype.card E ≤ ε := by
        rw [card_E, Nat.cast_pow, Nat.cast_ofNat]
        refine ENNReal.div_le_div_right ?_ _
        calc (A.card : ℝ≥0∞) ≤ ((2 ^ 13 - 1 : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hA
          _ = 2 ^ 13 - 1 := by rw [ENNReal.natCast_sub]; norm_num
      have hone : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true] +
          Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ powValid x.2.lane = true] ≤ 1 := by
        rw [OracleComp.prEvent_not_eq_one_sub, add_tsub_cancel_of_le (prEvent_le_one _)]
      calc Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[NewFirst c d j x ∧ x.1 ∈ A] +
            ε * Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[
              OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1)]
          ≤ Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true] * ε +
            ε * Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ powValid x.2.lane = true] := by
            refine add_le_add (h1.trans ?_) (by gcongr)
            rw [prob_valid_accept_eq]
            gcongr
        _ = ε * (Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[powValid x.2.lane = true] +
            Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[¬ powValid x.2.lane = true]) := by ring
        _ ≤ ε * 1 := by gcongr
        _ = ε := mul_one ε
  · simp only [hO, ↓reduceIte]
    have h0 : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[NewFirst c d j x ∧ x.1 ∈ A] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun x _ hx ↦ hO fun i hi0 hik y hy ↦
        hx.1.2.2 i hi0 hik y hy
    have h1 : Pr{let x ← ($ᵗ Draw : ProbComp Draw)}[
        OpenBelow (c.cacheQuery (.inr (d, j)) x) d (j.val + 1)] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun x _ hx ↦ hO (hopen x hx).1
    rw [h0, h1, mul_zero, add_zero]


theorem run_gaP (d : Common.DigestBytes) (j : Fin nLabels) (c : GCache) :
    (simulateQ GW.romImpl (gaP (Msg := List UInt8) (Dg := DigestBytes) d j)).run c =
      roStep (hs := GW) (.inr (d, j)) c :=
  run_hq (hs := GW) (.inr (d, j)) c

/-- **Reading root `d`'s draws from label `k` on** spoils a good cache whose labels below `k` are
cached with probability at most `(2^13 - 1) / 2^128` if no earlier nonce's draw is valid, and
not at all otherwise. -/
theorem prob_readFrom_le (r : ℕ) (d : Common.DigestBytes) : ∀ (m k : ℕ), k + m = nLabels →
    ∀ c : GCache, Good r c → CoveredBelow c d k →
      Pr{let z ← (simulateQ GW.romImpl (((List.finRange nLabels).drop k).mapM
          (gaP (Msg := List UInt8) (Dg := DigestBytes) d))).run c}[¬ Good r z.2] ≤
        if OpenBelow c d k then (2 ^ 13 - 1) / 2 ^ 128 else 0
  | 0, k, hk, c, hc, _ => by
    classical
    rw [List.drop_of_length_le (by simp only [List.length_finRange]; omega), List.mapM_nil,
      simulateQ_pure, StateT.run_pure, prEvent_pure]
    simp [hc]
  | m + 1, k, hk, c, hc, hcov => by
    classical
    have hlt : k < nLabels := by omega
    have hdrop : (List.finRange nLabels).drop k =
        (⟨k, hlt⟩ : Fin nLabels) :: (List.finRange nLabels).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp only [List.length_finRange]; exact hlt),
        List.getElem_finRange]
      rfl
    rw [hdrop, List.mapM_cons, simulateQ_bind, StateT.run_bind, run_gaP]
    set j : Fin nLabels := ⟨k, hlt⟩ with hj
    rcases hcj : c (.inr (d, j)) with _ | y
    · -- a fresh draw
      rw [roStep_of_none hcj, bind_assoc]
      simp only [pure_bind]
      refine prob_fresh_step_le hc hcj _ fun x hgx ↦ ?_
      rw [prEvent_run_bind_pure]
      refine prob_readFrom_le r d m (k + 1) (by omega) _ hgx fun i hi ↦ ?_
      rw [gcache_inr_inr]
      split_ifs
      · simp
      · exact hcov i (by
          have : i ≠ j := fun h ↦ by simp_all
          have : i.val ≠ k := fun h ↦ this (Fin.ext h)
          omega)
    · -- a cached draw
      rw [roStep_of_some hcj, pure_bind, prEvent_run_bind_pure]
      refine (prob_readFrom_le r d m (k + 1) (by omega) c hc fun i hi ↦ ?_).trans ?_
      · by_cases hik : i.val = k
        · rw [show i = j from Fin.ext hik, hcj]; simp
        · exact hcov i (by omega)
      · by_cases h1 : OpenBelow c d (k + 1)
        · simp [h1, openBelow_mono (Nat.le_succ k) h1]
        · simp [h1]

/-- **The verifier's reading of the root's draws spoils a good cache** with probability at most
`(2^13 - 1) / 2^128`: one fresh try, however many nonces it tries. -/
theorem prob_readVec_not_good_le (r : ℕ) (d : Common.DigestBytes) (c : GCache) (hc : Good r c) :
    Pr{let z ← (simulateQ GW.romImpl (readVec (Msg := List UInt8) (Dg := DigestBytes)
        (n := nLabels) d)).run c}[¬ Good r z.2] ≤ (2 ^ 13 - 1) / 2 ^ 128 := by
  rw [readVec, simulateQ_map, StateT.run_map, prEvent_map]
  have h := prob_readFrom_le r d nLabels 0 (by omega) c hc fun i hi ↦ absurd hi (Nat.not_lt_zero _)
  rw [List.drop_zero] at h
  refine h.trans ?_
  split_ifs <;> simp

/-- **Reading a root's draws** caches draws of that root alone. -/
theorem mapM_gaP_support (d : Common.DigestBytes) : ∀ (L : List (Fin nLabels)) (c : GCache) {z},
    z ∈ support ((simulateQ GW.romImpl (L.mapM (gaP (Msg := List UInt8) (Dg := DigestBytes) d))).run c) →
      domH z.2 = domH c ∧ fOf z.2 = fOf c ∧ domG z.2 ⊆ insert d (domG c)
  | [], c, z, hz => by
    simp only [List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨rfl, rfl, Set.subset_insert _ _⟩
  | j :: L, c, z, hz => by
    rw [List.mapM_cons, simulateQ_bind, StateT.run_bind, run_gaP, mem_support_bind_iff] at hz
    obtain ⟨p, hp, hz⟩ := hz
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨q, hq, hz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    obtain ⟨h1, h2, h3⟩ := mapM_gaP_support d L p.2 hq
    have hp' : domH p.2 = domH c ∧ fOf p.2 = fOf c ∧ domG p.2 ⊆ insert d (domG c) := by
      rcases hcj : c (.inr (d, j)) with _ | y
      · rw [roStep_of_none hcj, mem_support_bind_iff] at hp
        obtain ⟨x, -, hp⟩ := hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨domH_insertG _ _ _, fOf_insertG _ _ _, by rw [domG_insertG]⟩
      · rw [roStep_of_some hcj] at hp
        simp only [support_pure, Set.mem_singleton_iff] at hp
        subst hp
        exact ⟨rfl, rfl, Set.subset_insert _ _⟩
    refine ⟨h1.trans hp'.1, h2.trans hp'.2.1, h3.trans ?_⟩
    rw [Set.insert_subset_iff]
    exact ⟨Set.mem_insert _ _, hp'.2.2⟩

/-- The draws of root `d` at the labels `L`, as `readVec` reads them at all labels. -/
noncomputable def readL (L : List (Fin nLabels)) (d : Common.DigestBytes) :
    OracleComp (unifSpec + GW) MembershipChallenge :=
  (fun l j ↦ l.getD j default) <$> L.mapM (gaP (Msg := List UInt8) (Dg := DigestBytes) d)

theorem readVec_eq_readL (d : Common.DigestBytes) :
    readVec (Msg := List UInt8) (Dg := DigestBytes) (n := nLabels) d =
      readL (List.finRange nLabels) d := rfl

/-- After reading a root's draws, the side invariant holds and the cache grew by one root. -/
theorem readL_gFin_gSize (L : List (Fin nLabels)) (d : Common.DigestBytes) (c : GCache)
    (hf : GFin c) {z} (hz : z ∈ support ((simulateQ GW.romImpl (readL L d)).run c)) :
    GFin z.2 ∧ gSize z.2 ≤ gSize c + 1 := by
  rw [readL, simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  obtain ⟨h1, -, h3⟩ := mapM_gaP_support d L c hp
  have hfin : (domG p.2).Finite := (hf.2.insert d).subset h3
  refine ⟨⟨by simp only [h1]; exact hf.1, hfin⟩, ?_⟩
  have := Set.ncard_le_ncard h3 (hf.2.insert d)
  have := Set.ncard_insert_le d (domG c)
  simp only [gSize, h1]
  omega

/-! ## Replaying a coin-free run against its final cache -/

/-- **A cache as a partial function**: the oracles answered by its entries, coins by none. -/
def replayImpl (c : GCache) : QueryImpl (unifSpec + GW) Option
  | .inl _ => none
  | .inr t => c t

/-- **A coin-free run is read off its final cache**: replayed against it, the computation
returns the run's result. -/
theorem replay_of_mem_support {α : Type} (X : OracleComp (unifSpec + GW) α) (hX : NoCoins X)
    (c : GCache) {z : α × GCache} (hz : z ∈ support ((simulateQ GW.romImpl X).run c)) :
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
    change z ∈ support ((simulateQ GW.romImpl (hq t >>= k)).run c) at hz
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
