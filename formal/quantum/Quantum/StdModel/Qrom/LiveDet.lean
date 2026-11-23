module

public import Quantum.StdModel.Qrom.Moded

@[expose] public section

/-!
# Live runs of hash-only computations are determined by the log

On a live run (`LiveRun`: every read answered consistently with the log `rl`, the memory moved
by a policy that logs the outcome), the log only grows (`liveRun_logLe`), and a computation that
flips no coin returns the same value on two live runs when the second starts from a log that
extends the end of the first (`liveRun_det`).
-/

open OracleComp OracleSpec

namespace Quantum.StdModel.Qrom.LiveDet

open Quantum.Qrom HashSig Common

variable {M : Type} (rl : M → HashDomain → Option HashOutput)

/-- The log of `m'` extends that of `m`. -/
def LogLe (m m' : M) : Prop :=
  ∀ z v, rl m z = some v → rl m' z = some v

variable {rl}

theorem LogLe.refl (m : M) : LogLe rl m m := fun _ _ h ↦ h

theorem LogLe.trans {m m' m'' : M} (h : LogLe rl m m') (h' : LogLe rl m' m'') :
    LogLe rl m m'' := fun z v hv ↦ h' z v (h z v hv)

/-- The coins of the world, as a weight. -/
def coinW : romWorld.Oracles.Domain → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- A live read logs its outcome. -/
theorem rl_stepRd_self {u : M → Option HashOutput → M} {z : HashDomain} (hu : RecordsAt rl z u)
    {m m' : M} {v : HashOutput} (h : stepRd rl u z (some m) v = some m') : rl m' z = some v := by
  obtain ⟨rfl, -⟩ := stepRd_some h
  rw [hu m (some v), Function.update_self]

/-- **A live read extends the log.** -/
theorem logLe_stepRd {u : M → Option HashOutput → M} {z : HashDomain} (hu : RecordsAt rl z u)
    {m m' : M} {v : HashOutput} (h : stepRd rl u z (some m) v = some m') : LogLe rl m m' := by
  obtain ⟨rfl, hz⟩ := stepRd_some h
  intro y w hy
  rw [hu m (some v)]
  by_cases hyz : y = z
  · subst hyz
    rw [Function.update_self]
    rcases hz with hz | hz
    · rw [hz] at hy
      cases hy
    · rw [hz] at hy
      exact hy
  · rw [Function.update_of_ne hyz]
    exact hy

/-- **The log only grows along a live run.** -/
theorem liveRun_logLe {u : HashDomain → M → Option HashOutput → M}
    (hu : ∀ z, RecordsAt rl z (u z)) {α : Type} (oa : OracleComp romWorld.Oracles α) :
    ∀ {m m' : M} {a : α}, LiveRun rl u oa (some m) a (some m') → LogLe rl m m' := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro m m' a h
    obtain ⟨-, h⟩ := liveRun_pure_inv h
    cases h
    exact LogLe.refl m
  | query_bind t k ih =>
    intro m m' a h
    obtain ⟨y, μ₁, h₁, h₂⟩ := liveRun_query_bind h
    rcases t with n | z
    · change (y, μ₁) ∈ support ((fun b ↦ (b, some m)) <$>
        liftM (romWorld.Oracles.query (.inl n))) at h₁
      rw [support_map] at h₁
      obtain ⟨_, _, he⟩ := h₁
      rw [← (Prod.mk.inj he).2] at h₂
      exact ih y h₂
    · have hμ := eq_stepRd_of_mem_support h₁
      rcases hs : stepRd rl (u z) z (some m) y with _ | m₁
      · rw [hμ, hs] at h₂
        exact absurd (liveRun_none_mode _ h₂) (Option.some_ne_none _)
      · rw [hμ, hs] at h₂
        exact (logLe_stepRd (hu z) hs).trans (ih y h₂)

/-- **A computation flipping no coin is determined by the log on live runs**: two live runs, the
second from a log extending the end of the first, return the same value. -/
theorem liveRun_det {u u' : HashDomain → M → Option HashOutput → M}
    (hu : ∀ z, RecordsAt rl z (u z)) (hu' : ∀ z, RecordsAt rl z (u' z)) {α : Type}
    (oa : OracleComp romWorld.Oracles α) (hc : QueryCostAtMost oa coinW 0) :
    ∀ {m₁ m₁' m₂ m₂' : M} {a b : α}, LiveRun rl u oa (some m₁) a (some m₁') →
      LiveRun rl u' oa (some m₂) b (some m₂') → LogLe rl m₁' m₂ → a = b := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro m₁ m₁' m₂ m₂' a b h₁ h₂ _
    exact (liveRun_pure_inv h₁).1.trans (liveRun_pure_inv h₂).1.symm
  | query_bind t k ih =>
    intro m₁ m₁' m₂ m₂' a b h₁ h₂ hle
    rw [isWeightBound_query_bind_iff] at hc
    rcases t with n | z
    · exact absurd hc.1 (by simp [coinW])
    obtain ⟨y₁, μ₁, hq₁, hk₁⟩ := liveRun_query_bind h₁
    obtain ⟨y₂, μ₂, hq₂, hk₂⟩ := liveRun_query_bind h₂
    rw [eq_stepRd_of_mem_support hq₁] at hk₁
    rw [eq_stepRd_of_mem_support hq₂] at hk₂
    rcases hs₁ : stepRd rl (u z) z (some m₁) y₁ with _ | n₁
    · rw [hs₁] at hk₁
      exact absurd (liveRun_none_mode _ hk₁) (Option.some_ne_none _)
    rcases hs₂ : stepRd rl (u' z) z (some m₂) y₂ with _ | n₂
    · rw [hs₂] at hk₂
      exact absurd (liveRun_none_mode _ hk₂) (Option.some_ne_none _)
    rw [hs₁] at hk₁
    rw [hs₂] at hk₂
    have hn₁ : rl n₁ z = some y₁ := rl_stepRd_self (hu z) hs₁
    have hm₂ : rl m₂ z = some y₁ := hle z y₁ (liveRun_logLe hu _ hk₁ z y₁ hn₁)
    have hy : y₂ = y₁ := by
      obtain ⟨-, h⟩ := stepRd_some hs₂
      rw [hm₂] at h
      rcases h with h | h
      · cases h
      · exact (Option.some.inj h).symm
    subst hy
    have hc' : QueryCostAtMost (k y₂) coinW 0 := by
      have h2 := hc.2 y₂
      rwa [Nat.zero_sub] at h2
    exact ih y₂ hc' hk₁ hk₂ (hle.trans (logLe_stepRd (hu' z) hs₂))

end Quantum.StdModel.Qrom.LiveDet

end
