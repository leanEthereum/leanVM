module

public import LeanDa.Collapse
public import LeanDa.MerkleM
public import LeanDa.RpmWagner
public import Common.Eager

@[expose] public section

/-!
# A collision of a uniformly random table of `H`, found by a bounded search

Benedikt Wagner's collision terms are experiments over a uniformly random table `h` of `H` on
the strings of at most `2048` bytes (`HTab`). When a collision finder reaches `h` only through
queries of an oracle `XS` (`H` on short strings, `hS`), its experiment is `col h` of a computation
querying `XS`, and a collision among `N` queries and the two final ones has probability at most
`(N + 2)² / 2^256` (`prob_collision_le`): sampling `h` in advance is sampling it lazily
(`Common.run'_romImpl_evalDistEq_eager`), and a fresh answer collides with one of at most `N + 2`
cached ones with probability at most `(N + 2) / 2^256`.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA: it bounds his
collision terms.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common LeanDa.Fork PFunctor
open scoped ENNReal

namespace LeanDa

/-- The short strings, the domain of a table of `H`. -/
abbrev HDom := {a : List UInt8 // shortP a}

/-- `H` on the short strings, as an oracle. -/
abbrev XS := HDom →ₒ DigestBytes

section Hash

variable {ι : Type} {Ψ : OracleSpec ι}

/-- **`H` as an oracle** among `Ψ + XS`: a query on a short string, `default` on a long one (the
value `Hh h` gives it). Irreducible: unification never decides `shortP` of a concrete string (a
cell's `2048` bytes would be computed). -/
@[irreducible] def hS (a : List UInt8) : OracleComp (Ψ + XS) Common.DigestBytes :=
  if ha : shortP a then FreeM.lift (P := (Ψ + XS).toPFunctor) (.inr ⟨a, ha⟩) else pure default

theorem simulateQ_col_hS (h : HTab) (a : List UInt8) :
    simulateQ (col (Ψ := Ψ) h) (hS a) = pure (Hh h a) := by
  unfold hS Hh
  split <;> rfl

/-- Queries of `XS`, one each. -/
def xCalls : ι ⊕ HDom → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem isWeightBound_hS (a : List UInt8) :
    QueryCostAtMost (hS (Ψ := Ψ) a) xCalls 1 := by
  unfold hS
  split
  · exact isWeightBound_query (spec := Ψ + XS) xCalls (.inr _)
  · exact isWeightBound_pure _ _ _

theorem isWeightBound_liftL {α : Type} (z : OracleComp Ψ α) :
    QueryCostAtMost (liftL (X := XS) z) xCalls 0 := by
  induction z using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    change QueryCostAtMost ((liftM ((Ψ + XS).query (.inl t)) : OracleComp (Ψ + XS) _) >>= fun u ↦
      liftL (k u)) xCalls 0
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨le_rfl, fun u ↦ ih u⟩

end Hash

/-- **The final check of a collision finder**: two different short strings with equal answers. -/
def finalCheck (ab : List UInt8 × List UInt8) : OracleComp (unifSpec + XS) Bool :=
  if hab : shortP ab.1 ∧ shortP ab.2 then do
    let x ← FreeM.lift (P := (unifSpec + XS).toPFunctor) (.inr ⟨ab.1, hab.1⟩)
    let y ← FreeM.lift (P := (unifSpec + XS).toPFunctor) (.inr ⟨ab.2, hab.2⟩)
    pure (decide (ab.1 ≠ ab.2) && decide (x = y))
  else pure false

theorem simulateQ_col_finalCheck (h : HTab) (ab : List UInt8 × List UInt8) :
    simulateQ (col h) (finalCheck ab) =
      pure (decide (shortP ab.1 ∧ shortP ab.2) && (decide (ab.1 ≠ ab.2) &&
        decide (Hh h ab.1 = Hh h ab.2))) := by
  unfold finalCheck
  split
  · next hab =>
    change (pure (decide (ab.1 ≠ ab.2) && decide (h ⟨ab.1, hab.1⟩ = h ⟨ab.2, hab.2⟩)) :
      ProbComp Bool) = _
    simp only [Hh, hab.1, hab.2, ↓reduceDIte, and_self, decide_true, Bool.true_and]
  · next hab => simp [hab]

theorem isWeightBound_finalCheck (ab : List UInt8 × List UInt8) :
    QueryCostAtMost (finalCheck ab) xCalls 2 := by
  unfold finalCheck
  split
  · exact ((isWeightBound_query (spec := unifSpec + XS) xCalls (.inr _)).bind fun _ ↦
      (isWeightBound_query (spec := unifSpec + XS) xCalls (.inr _)).bind fun _ ↦
        isWeightBound_pure _ _ 0)
  · exact isWeightBound_pure _ _ _

/-! ## Sampling the table lazily -/

/-- The lazy world's oracles: coins, a random oracle of the roots (unused), and `H`. -/
abbrev ESpec := EagerSpec (Common.DigestBytes →ₒ MembershipChallenge) (List UInt8) DigestBytes

/-- Its cache. -/
abbrev ECache := ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ
    DigestBytes)).QueryCache

/-- The queries of `XS` as queries of `H`. -/
def embE : QueryImpl (unifSpec + XS) (OracleComp ESpec)
  | .inl n => liftM (ESpec.query (.inl n))
  | .inr d => liftM (ESpec.query (.inr (.inr d.1)))

/-- A cache with no short string. -/
def NoShortE (c : ECache) : Prop := ∀ a, shortP a → c (.inr a) = none

theorem run_eagerImpl_embE (g : HTab) {α : Type} (Y : OracleComp (unifSpec + XS) α) (c : ECache)
    (hc : NoShortE c) :
    (simulateQ (eagerImpl shortP g) (simulateQ embE Y)).run c = (·, c) <$> simulateQ (col g) Y := by
  induction Y using OracleComp.inductionOn generalizing c with
  | pure a => rfl
  | query_bind t k ih =>
    rcases t with n | d
    · change (simulateQ (eagerImpl shortP g) (liftM (ESpec.query (.inl n)) >>= fun u ↦
          simulateQ embE (k u))).run c =
        (·, c) <$> (FreeM.lift (P := unifSpec.toPFunctor) n >>= fun u ↦ simulateQ (col g) (k u))
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      change (unifFwdImpl _ n).run c >>= _ = _
      rw [unifFwd_run]
      simp only [map_bind]
      change FreeM.lift (P := unifSpec.toPFunctor) n >>= _ = FreeM.lift n >>= _
      congr 1
      funext u
      exact ih u c hc
    · change (simulateQ (eagerImpl shortP g) (liftM (ESpec.query (.inr (.inr d.1))) >>= fun u ↦
          simulateQ embE (k u))).run c = (·, c) <$> simulateQ (col g) (k (g d))
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      have e : (eagerImpl shortP g (.inr (.inr d.1))).run c = pure (g d, c) := by
        simp only [eagerImpl, d.2, ↓reduceDIte, StateT.run_mk, hc d.1 d.2, Option.getD_none]
      rw [e, pure_bind]
      exact ih (g d) c hc

/-- **Sampling the table in advance is sampling `H` lazily**, for a computation querying `XS`. -/
theorem uniform_col_evalDistEq {α : Type} (Y : OracleComp (unifSpec + XS) α) :
    (($ᵗ HTab : ProbComp HTab) >>= fun h ↦ simulateQ (col h) Y) =ᵈ
      (simulateQ ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ
          DigestBytes)).romImpl
        (simulateQ embE Y)).run' ∅ := by
  refine EvalDistEq.symm ((run'_romImpl_evalDistEq_eager shortP _ ∅).trans ?_)
  refine EvalDistEq.bind_right _ fun g ↦ ?_
  rw [StateT.run'_eq, run_eagerImpl_embE g Y ∅ (fun _ _ ↦ rfl), Functor.map_map]
  simp only [id_map']
  exact EvalDistEq.rfl

/-! ## The birthday bound -/

/-- Queries of `H` in the lazy world, one each. -/
def eCalls : ESpec.Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

theorem isWeightBound_embE {α : Type} {Y : OracleComp (unifSpec + XS) α} {N : ℕ}
    (hY : QueryCostAtMost Y xCalls N) : QueryCostAtMost (simulateQ embE Y) eCalls N :=
  isWeightBound_simulateQ embE xCalls eCalls (fun t ↦ by
    rcases t with n | d
    · exact isWeightBound_query (spec := ESpec) eCalls (.inl n)
    · exact isWeightBound_query (spec := ESpec) eCalls (.inr (.inr d.1))) hY

/-- The inputs of `H` a cache holds. -/
def eDom (c : ECache) : Set (List UInt8) := {a | c (.inr a) ≠ none}

/-- A collision of `H` in a cache. -/
def HColE (c : ECache) : Prop :=
  ∃ a b, a ≠ b ∧ c (.inr a) ≠ none ∧ c (.inr a) = c (.inr b)

/-- The `H` part of a cache, as a function. -/
def eOf (c : ECache) (a : List UInt8) : DigestBytes := (c (.inr a)).getD default

theorem romE_step (t : ESpec.Domain) (c : ECache) {z} (hz : z ∈ support
    ((((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl
        t).run c)) :
    z.2 = c ∨ (∃ d u, z.2 = c.cacheQuery (.inl d) u) ∨
      (∃ a u, t = .inr (.inr a) ∧ c (.inr a) = none ∧ z.2 = c.cacheQuery (.inr a) u) := by
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
      rcases t with d | a
      · exact Or.inr (Or.inl ⟨d, u, rfl⟩)
      · exact Or.inr (Or.inr ⟨a, u, rfl, h, rfl⟩)
    · rw [roStep_of_some h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl rfl

theorem cacheQuery_inl_inrE (c : ECache) (d : Common.DigestBytes) (u : MembershipChallenge) (a : List UInt8) :
    (c.cacheQuery (.inl d) u) (.inr a) = c (.inr a) :=
  QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem cacheQuery_inr_inrE (c : ECache) (a b : List UInt8) (u : DigestBytes) :
    (c.cacheQuery (.inr a) u) (.inr b) = if b = a then some u else c (.inr b) := by
  by_cases h : b = a
  · subst h; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
    simp [h]

/-- **The birthday bound in the lazy world**: at most `N` queries of `H` end with a collision in
the cache with probability at most `N · N / 2^256`. -/
theorem prob_hColE_le {α : Type} (Y : OracleComp ESpec α) (N : ℕ) (hY : QueryCostAtMost Y eCalls N) :
    Pr{let z ← (simulateQ ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl Y).run ∅}[
      HColE z.2] ≤ N * ((N : ℝ≥0∞) / 2 ^ 256) := by
  classical
  have h := prEvent_run_bad_le ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl HColE
    (fun c ↦ (eDom c).Finite) eCalls (fun c ↦ (eDom c).ncard) N ((N : ℝ≥0∞) / 2 ^ 256)
    ?_ ?_ ?_ Y N hY ∅ (by simp [eDom]) (by simp [eDom])
  · refine h.trans (le_of_eq ?_)
    have : ¬ HColE (∅ : ECache) := fun ⟨a, _, _, ha, _⟩ ↦ ha rfl
    simp [this]
  · intro t c hc z hz
    rcases romE_step t c hz with h | ⟨d, u, h⟩ | ⟨a, u, -, -, h⟩
    · rw [h]; exact hc
    · rw [h]; simpa [eDom, cacheQuery_inl_inrE] using hc
    · rw [h]
      refine (hc.insert a).subset fun b hb ↦ ?_
      simp only [eDom, Set.mem_ofPred_eq, cacheQuery_inr_inrE] at hb
      by_cases hba : b = a
      · exact Or.inl hba
      · exact Or.inr (by simpa [eDom, hba] using hb)
  · intro t c hc z hz
    rcases romE_step t c hz with h | ⟨d, u, h⟩ | ⟨a, u, rfl, -, h⟩
    · rw [h]; omega
    · rw [h]; simp [eDom]
    · rw [h]
      have : eDom (c.cacheQuery (.inr a) u) = insert a (eDom c) := by
        ext b
        by_cases hba : b = a
        · subst hba; simp [eDom]
        · simp [eDom, cacheQuery_inr_inrE, hba]
      rw [this]
      exact (Set.ncard_insert_le a _).trans (by simp [eCalls])
  · intro t c hc hbad hN
    have hkeep : ∀ c' : ECache, (∀ b, c' (.inr b) = c (.inr b)) → ¬ HColE c' := by
      rintro c' hc' ⟨a, b, hab, ha, he⟩
      exact hbad ⟨a, b, hab, by rwa [← hc'], by rwa [← hc', ← hc']⟩
    rcases t with n | d | a
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      rcases romE_step _ c hz with h | ⟨d, u, h⟩ | ⟨a, u, h, -, -⟩
      · exact hkeep _ fun b ↦ by rw [h]
      · exact hkeep _ fun b ↦ by rw [h, cacheQuery_inl_inrE]
      · cases h
    · refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ↦ ?_) zero_le
      rcases romE_step _ c hz with h | ⟨d, u, h⟩ | ⟨a, u, h, -, -⟩
      · exact hkeep _ fun b ↦ by rw [h]
      · exact hkeep _ fun b ↦ by rw [h, cacheQuery_inl_inrE]
      · cases h
    · rw [romImpl_inr_run]
      rcases h : c (.inr a) with _ | v
      · rw [roStep_of_none h, bind_pure_comp, prEvent_map]
        let V : Finset DigestBytes := hc.toFinset.image (eOf c)
        have hmem : ∀ u : DigestBytes, HColE (c.cacheQuery (.inr a) u) → u ∈ V := by
          rintro u ⟨a₁, b₁, hne, h₁, he⟩
          simp only [cacheQuery_inr_inrE] at h₁ he
          by_cases ha₁ : a₁ = a
          · subst ha₁
            have hb₁ : b₁ ≠ a₁ := Ne.symm hne
            simp only [hb₁, ↓reduceIte] at he
            refine Finset.mem_image.mpr ⟨b₁, hc.mem_toFinset.mpr (by simp [eDom, ← he]), ?_⟩
            simp [eOf, ← he]
          · by_cases hb₁ : b₁ = a
            · subst hb₁
              simp only [ha₁, ↓reduceIte] at he h₁
              refine Finset.mem_image.mpr ⟨a₁, hc.mem_toFinset.mpr (by simp [eDom, he]), ?_⟩
              simp [eOf, he]
            · simp only [ha₁, hb₁, ↓reduceIte] at h₁ he
              exact absurd ⟨a₁, b₁, hne, h₁, he⟩ hbad
        have hV : (V.card : ℝ≥0∞) ≤ N := by
          have h1 : V.card ≤ hc.toFinset.card := Finset.card_image_le
          rw [← Set.ncard_eq_toFinset_card _ hc] at h1
          have h2 : (eDom c).ncard + 1 ≤ N := by simpa [eCalls] using hN
          exact_mod_cast (h1.trans (by omega))
        calc Pr{let x ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[HColE (c.cacheQuery (.inr a) x)]
            ≤ Pr{let x ← ($ᵗ DigestBytes : ProbComp DigestBytes)}[x ∈ V] :=
              prEvent_mono _ _ _ fun u hu ↦ hmem u hu
          _ = V.card / 2 ^ 256 := by
              rw [SampleableType.prEvent_uniformSample, card_digest, Finset.filter_mem_eq_inter,
                Finset.univ_inter]
              norm_num
          _ ≤ eCalls (.inr (.inr a)) * ((N : ℝ≥0∞) / 2 ^ 256) := by
              simp only [eCalls, Nat.cast_one, one_mul]
              gcongr
      · rw [roStep_of_some h]
        simp only [prEvent_pure]
        simp [hbad]

/-- **A winning final check leaves a collision in the cache.** -/
theorem hColE_of_finalCheck {Z : OracleComp (unifSpec + XS) (List UInt8 × List UInt8)}
    {z : Bool × ECache}
    (hz : z ∈ support ((simulateQ ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl
      (simulateQ embE (Z >>= finalCheck))).run ∅)) (hwin : z.1 = true) : HColE z.2 := by
  rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨w, -, hz⟩ := hz
  unfold finalCheck at hz
  split at hz
  · next hab =>
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨x, hx, y, hy, hz⟩ := hz
    change x ∈ support ((simulateQ ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl
      (liftM (ESpec.query (.inr (.inr w.1.1))))).run w.2) at hx
    change y ∈ support ((simulateQ ((Common.DigestBytes →ₒ MembershipChallenge) + (List UInt8 →ₒ DigestBytes)).romImpl
      (liftM (ESpec.query (.inr (.inr w.1.2))))).run x.2) at hy
    rw [simulateQ_spec_query, romImpl_inr_run] at hx hy
    obtain ⟨-, hx2⟩ := le_of_mem_support_roStep _ _ hx
    obtain ⟨hle, hy2⟩ := le_of_mem_support_roStep _ _ hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
    obtain ⟨hne, hxy⟩ := hwin
    have h1 : y.2 (.inr w.1.1) = some x.1 := hle hx2
    exact ⟨w.1.1, w.1.2, hne, by simp [h1], by rw [h1, hy2, hxy]⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    cases hwin

/-- **A collision finder of `N` queries of `H` on short strings, against a uniformly random table**:
its final check wins with probability at most `(N + 2)² / 2^256`. -/
theorem prob_collision_le (Z : OracleComp (unifSpec + XS) (List UInt8 × List UInt8)) (N : ℕ)
    (hZ : QueryCostAtMost Z xCalls N) :
    Pr{let b ← ($ᵗ HTab : ProbComp HTab) >>= fun h ↦ simulateQ (col h) (Z >>= finalCheck)}[
      b = true] ≤ ((N + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
  rw [(uniform_col_evalDistEq _).prEvent_eq, StateT.run'_eq, prEvent_map]
  have hW : QueryCostAtMost (Z >>= finalCheck) xCalls (N + 2) :=
    hZ.bind fun ab ↦ isWeightBound_finalCheck ab
  calc _ ≤ _ := prEvent_mono_of_support _ _ _ fun z hz hw ↦ hColE_of_finalCheck hz hw
    _ ≤ (N + 2 : ℕ) * (((N + 2 : ℕ) : ℝ≥0∞) / 2 ^ 256) :=
        prob_hColE_le _ (N + 2) (isWeightBound_embE hW)
    _ = _ := by rw [← mul_div_assoc, ← pow_two]

end LeanDa
