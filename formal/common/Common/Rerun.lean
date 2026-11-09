module

public import Common.RomComm

@[expose] public section

/-!
# Recomputing a coin-free computation in the random oracle model

A computation that makes random-oracle queries but flips no coins (`NoCoins`) is a function of
the random oracle: run again from any later cache, it returns the same result and leaves the
cache unchanged (`run_rerun`), every query hitting the cache. A verifier that recomputes the same
challenges for every opening therefore computes them once.

Also: a prefix of a computation weighs at most the computation (`QueryCostAtMost.of_bind`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]

/-- **A coin-free computation**: every query on every path is a random-oracle query. -/
def NoCoins {α : Type} : OracleComp (unifSpec + hs) α → Prop
  | .pure _ => True
  | .liftBind (.inl _) _ => False
  | .liftBind (.inr _) k => ∀ u, NoCoins (k u)

theorem noCoins_pure {α : Type} (a : α) : NoCoins (pure a : OracleComp (unifSpec + hs) α) :=
  trivial

theorem noCoins_hq_bind {α : Type} (t : ι) (k : hs.Range t → OracleComp (unifSpec + hs) α) :
    NoCoins (hq t >>= k) ↔ ∀ u, NoCoins (k u) := Iff.rfl

theorem noCoins_bind {α β : Type} {X : OracleComp (unifSpec + hs) α}
    {f : α → OracleComp (unifSpec + hs) β} (hX : NoCoins X) (hf : ∀ a, NoCoins (f a)) :
    NoCoins (X >>= f) := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [bind_assoc]
    rcases t with n | t
    · exact hX.elim
    · exact fun u ↦ ih u (hX u)

theorem noCoins_map {α β : Type} {X : OracleComp (unifSpec + hs) α} (f : α → β)
    (hX : NoCoins X) : NoCoins (f <$> X) := by
  rw [map_eq_bind_pure_comp]
  exact noCoins_bind hX fun _ ↦ trivial

theorem noCoins_hq (t : ι) : NoCoins (hq (hs := hs) t) := by
  have := (noCoins_hq_bind (hs := hs) t pure).mpr fun _ ↦ trivial
  simpa using this

/-- **Recomputing a coin-free computation** from any cache extending one of its final caches
returns the same result and leaves the cache unchanged. -/
theorem run_rerun {α : Type} (X : OracleComp (unifSpec + hs) α) (hX : NoCoins X)
    (c : hs.QueryCache) {z : α × hs.QueryCache} (hz : z ∈ support ((simulateQ hs.romImpl X).run c))
    (c' : hs.QueryCache) (hc' : z.2 ≤ c') : (simulateQ hs.romImpl X).run c' = pure (z.1, c') := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz ⊢
    subst hz; rfl
  | query_bind t k ih =>
    rcases t with n | t
    · exact hX.elim
    have hk : ∀ u, NoCoins (k u) := hX
    change (simulateQ hs.romImpl (hq t >>= k)).run c' = _
    change z ∈ support ((simulateQ hs.romImpl (hq t >>= k)).run c) at hz
    rw [simulateQ_bind, StateT.run_bind, run_hq, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨-, hwt⟩ := le_of_mem_support_roStep t c hw
    have hz2 := le_of_mem_support_run (k w.1) w.2 hz
    rw [simulateQ_bind, StateT.run_bind, run_hq, roStep_of_some (hc' (hz2 hwt)), pure_bind]
    exact ih w.1 (hk w.1) w.2 hz

/-- **A prefix weighs at most the computation.** -/
theorem QueryCostAtMost.of_bind {ι' : Type} {spec : OracleSpec.{0, 0} ι'} {α β : Type}
    {X : OracleComp spec α} {f : α → OracleComp spec β} {w : ι' → ℕ} {Q : ℕ}
    (h : QueryCostAtMost (X >>= f) w Q) : QueryCostAtMost X w Q := by
  induction X using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [bind_assoc, isWeightBound_query_bind_iff] at h
    rw [isWeightBound_query_bind_iff]
    exact ⟨h.1, fun u ↦ ih u (h.2 u)⟩

/-- **A continuation weighs at most the computation**, on every output of the prefix. -/
theorem QueryCostAtMost.of_bind_mem_support {ι' : Type} {spec : OracleSpec.{0, 0} ι'} {α β : Type}
    {X : OracleComp spec α} {f : α → OracleComp spec β} {w : ι' → ℕ} {Q : ℕ}
    (h : QueryCostAtMost (X >>= f) w Q) {x : α} (hx : x ∈ support X) : QueryCostAtMost (f x) w Q := by
  induction X using OracleComp.inductionOn generalizing Q with
  | pure a =>
    simp only [support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simpa using h
  | query_bind t k ih =>
    rw [bind_assoc, isWeightBound_query_bind_iff] at h
    rw [mem_support_bind_iff] at hx
    obtain ⟨u, -, hu⟩ := hx
    exact (ih u (h.2 u) hu).mono (Nat.sub_le _ _)

/-- **Weight bounds through a simulation**: if every query's image weighs at most the query's
weight, the simulation weighs at most the computation's bound. -/
theorem isWeightBound_simulateQ {ι₁ ι₂ : Type} {spec₁ : OracleSpec.{0, 0} ι₁}
    {spec₂ : OracleSpec.{0, 0} ι₂} {α : Type} (impl : QueryImpl spec₁ (OracleComp spec₂))
    (w₁ : ι₁ → ℕ) (w₂ : ι₂ → ℕ) (hstep : ∀ t, QueryCostAtMost (impl t) w₂ (w₁ t))
    {X : OracleComp spec₁ α} {Q : ℕ} (h : QueryCostAtMost X w₁ Q) :
    QueryCostAtMost (simulateQ impl X) w₂ Q := by
  induction X using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    exact ((hstep t).bind fun u ↦ ih u (h.2 u)).mono (by omega)

/-! ## Coins through simulations -/

section Coins

variable {ι₁ ι₂ : Type} {hs₁ : OracleSpec.{0, 0} ι₁} {hs₂ : OracleSpec.{0, 0} ι₂} {α : Type}

/-- **A simulation forwarding the coins keeps a coin computation.** -/
theorem simulateQ_liftM_of_coins (impl : QueryImpl (unifSpec + hs₁) (OracleComp (unifSpec + hs₂)))
    (h : ∀ n, impl (.inl n) = liftM ((unifSpec + hs₂).query (.inl n))) (p : ProbComp α) :
    simulateQ impl (liftM p : OracleComp (unifSpec + hs₁) α) = liftM p := by
  change simulateQ impl (OracleComp.liftComp p _) = OracleComp.liftComp p _
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_bind, simulateQ_bind,
      OracleComp.liftComp_query, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change simulateQ impl (liftM ((unifSpec + hs₁).query (.inl n))) >>= _ =
      liftM ((unifSpec + hs₂).query (.inl n)) >>= _
    rw [simulateQ_spec_query, h n]
    exact bind_congr fun u ↦ ih u

/-- **A stateful simulation forwarding the coins keeps a coin computation**, and its state. -/
theorem run_simulateQ_liftM_of_coins {σ : Type}
    (impl : QueryImpl (unifSpec + hs₁) (StateT σ (OracleComp (unifSpec + hs₂))))
    (h : ∀ n s, (impl (.inl n)).run s =
      (·, s) <$> (liftM ((unifSpec + hs₂).query (.inl n)) : OracleComp (unifSpec + hs₂) _))
    (p : ProbComp α) (s : σ) :
    (simulateQ impl (liftM p : OracleComp (unifSpec + hs₁) α)).run s =
      (·, s) <$> (liftM p : OracleComp (unifSpec + hs₂) α) := by
  change (simulateQ impl (OracleComp.liftComp p _)).run s = _ <$> OracleComp.liftComp p _
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_bind, simulateQ_bind,
      OracleComp.liftComp_query, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change (simulateQ impl (liftM ((unifSpec + hs₁).query (.inl n))) >>= _).run s =
      _ <$> (liftM ((unifSpec + hs₂).query (.inl n)) >>= _)
    rw [simulateQ_spec_query, StateT.run_bind, h n s, bind_map_left, map_bind]
    exact bind_congr fun u ↦ ih u

end Coins

end Common
