module

public import Quantum.Model

@[expose] public section

/-!
# A uniform permutation as Feistel rounds around a uniform permutation

The first step of Alagic, Carolan, Majenz and Tokat, *The Sponge is Quantum Indifferentiable*
(ePrint 2025/731, §2.1, eq. (5)). On the sponge state `S = X × Z` (rate `X`, capacity `Z`), keys
`k, k' : X → Z` and `h : Z → X` give the Feistel rounds

`σ_k (x, z) = (x, z + k x)` and `ω_h (x, z) = (x + h z, z)`,

and for a permutation `π` of `S`, `φ = ω_h ∘ σ_k' ∘ π ∘ σ_k` (`spongePerm`). With the keys and `π`
drawn uniformly and independently, `φ` is uniform: for fixed keys, `π ↦ φ` is a bijection. So a
program in the quantum random-permutation model runs the same against `φ` as against a uniform
permutation (`qrpmEvalDistMap_eq_spongePerm`), and the keys, now random functions, can be
answered by compressed oracles.
-/

open MeasureTheory
open scoped ENNReal

universe u v w

namespace Quantum

section reparam

variable {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
  {β : Type*} {Ω Ω' F : Type} [Fintype Ω] [Fintype Ω'] [Fintype F] [Nonempty F]

/-- Sampling `ω'` uniformly and running against `R (e ω').1` is sampling `ω` uniformly and running
against `R ω`, when `e : Ω' ≃ Ω × F` (every `ω` has `|F|` preimages). -/
theorem sampledEvalDistMap_reparam [MeasurableSpace β] (e : Ω' ≃ Ω × F)
    (R : Ω → QuantumRuntime spec) (I : L.Interp) (x : QuantumComp L spec W A) (ρ : SubState A)
    (f : Ω → (Σ u, W u) → β) :
    sampledEvalDistMap (fun ω' ↦ R (e ω').1) I x ρ (fun ω' ↦ f (e ω').1) =
      sampledEvalDistMap R I x ρ f := by
  rw [sampledEvalDistMap_eq_sum, sampledEvalDistMap_eq_sum, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul, ← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

end reparam

variable {X Z : Type}

/-- The Feistel round `σ_k (x, z) = (x, z + k x)`, which adds a key of the rate into the capacity. -/
def capacityRound [AddCommGroup Z] (k : X → Z) : Equiv.Perm (X × Z) :=
  Equiv.prodShear (Equiv.refl X) fun x ↦ Equiv.addRight (k x)

/-- The Feistel round `ω_h (x, z) = (x + h z, z)`, which adds a key of the capacity into the rate. -/
def rateRound [AddCommGroup X] (h : Z → X) : Equiv.Perm (X × Z) :=
  ((Equiv.prodComm X Z).trans (Equiv.prodShear (Equiv.refl Z) fun z ↦ Equiv.addRight (h z))).trans
    (Equiv.prodComm Z X)

@[simp]
theorem capacityRound_apply [AddCommGroup Z] (k : X → Z) (s : X × Z) :
    capacityRound k s = (s.1, s.2 + k s.1) :=
  rfl

@[simp]
theorem rateRound_apply [AddCommGroup X] (h : Z → X) (s : X × Z) :
    rateRound h s = (s.1 + h s.2, s.2) :=
  rfl

variable [Fintype X] [DecidableEq X] [AddCommGroup X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The keys of the three Feistel rounds: `h`, then `k`, then `k'`. -/
abbrev SpongeKeys (X Z : Type) := (Z → X) × (X → Z) × (X → Z)

/-- `φ = ω_h ∘ σ_k' ∘ π ∘ σ_k`. -/
def spongePerm (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) : Equiv.Perm (X × Z) :=
  rateRound t.1 * capacityRound t.2.2 * π * capacityRound t.2.1

/-- For fixed keys, `π ↦ spongePerm t π` is a bijection, so the pair of keys and `π` is the pair of
`φ` and keys. -/
def spongePermEquiv (X Z : Type) [Fintype X] [DecidableEq X] [AddCommGroup X]
    [Fintype Z] [DecidableEq Z] [AddCommGroup Z] :
    SpongeKeys X Z × Equiv.Perm (X × Z) ≃ Equiv.Perm (X × Z) × SpongeKeys X Z :=
  (Equiv.prodShear (Equiv.refl _) fun t ↦
      (Equiv.mulLeft (rateRound t.1 * capacityRound t.2.2)).trans
        (Equiv.mulRight (capacityRound t.2.1))).trans
    (Equiv.prodComm _ _)

theorem spongePermEquiv_fst (ω : SpongeKeys X Z × Equiv.Perm (X × Z)) :
    (spongePermEquiv X Z ω).1 = spongePerm ω.1 ω.2 :=
  rfl

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} {β : Type*}

/-- **The decomposition is exact.** Drawing the keys and `π` uniformly and running against
`spongePerm t π` is the quantum random-permutation model, observations of `φ` included. -/
theorem qrpmEvalDistMap_eq_spongePerm [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qrpmSpec (X × Z)) W A) (ρ : SubState A)
    (f : Equiv.Perm (X × Z) → (Σ u, W u) → β) :
    sampledEvalDistMap (fun ω : SpongeKeys X Z × Equiv.Perm (X × Z) ↦
        permutationRuntime (spongePerm ω.1 ω.2)) I x ρ (fun ω ↦ f (spongePerm ω.1 ω.2)) =
      qrpmEvalDistMap I x ρ f :=
  sampledEvalDistMap_reparam (spongePermEquiv X Z) permutationRuntime I x ρ f

end Quantum

end
