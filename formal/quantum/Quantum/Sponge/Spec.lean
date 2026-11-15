module

public import VCVio.Quantum.Oracle.Model

@[expose] public section

/-!
# The three random functions of the sponge permutation

After the decomposition `φ = ω_h ∘ σ_k' ∘ π ∘ σ_k` (`Quantum.spongePerm`), an adversary against
the sponge calls three independent uniform random functions `h : Z → X` and `k, k' : X → Z`,
each through its additive oracle: port `h` applies `|z, x⟩ ↦ |z, x + h z⟩` on `Z × X`, ports `k`
and `k'` apply `|x, z⟩ ↦ |x, z + k x⟩` on `X × Z` (`spongeSpec`, `spongeFnRuntime`).
`spongeEvalDistMap` draws `(h, k, k')` uniformly, in the order of `Quantum.SpongeKeys`, and runs
the program against their oracles, as VCVio's `Quantum.qromEvalDistMap` does for one function.
-/

open MeasureTheory
open scoped ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-- The three oracle ports of the sponge's random functions. -/
inductive SpongePort where
  /-- `h : Z → X`, added into the rate. -/
  | h
  /-- `k : X → Z`, added into the capacity before `π`. -/
  | k
  /-- `k' : X → Z`, added into the capacity after `π`. -/
  | k'
  deriving DecidableEq

instance : Fintype SpongePort where
  elems := {.h, .k, .k'}
  complete i := by cases i <;> simp

/-- The register of each port: query input, then response. -/
@[reducible]
def spongeIn (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] :
    SpongePort → QReg
  | .h => QReg.of (Z × X)
  | .k => QReg.of (X × Z)
  | .k' => QReg.of (X × Z)

/-- The signature of the three random functions: port `h` on `Z × X`, ports `k` and `k'` on
`X × Z`, each returning its register and reporting nothing classical. -/
@[reducible]
def spongeSpec (X Z : Type) [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] :
    QuantumOracleSpec.{0, 0} where
  Port := SpongePort
  In := spongeIn X Z
  Out := spongeIn X Z
  Result _ := Unit

variable {X Z : Type} [Fintype X] [DecidableEq X] [AddCommGroup X]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The oracles of fixed functions `h`, `k`, `k'`: each port applies the oracle unitary of its
function. The private register is `Unit`. -/
noncomputable def spongeFnRuntime (h : Z → X) (k k' : X → Z) : QuantumRuntime (spongeSpec X Z) where
  D := QReg.of Unit
  init := SubState.basis ()
  step
    | .h => (oracleQuery h).frame Unit
    | .k => (oracleQuery k).frame Unit
    | .k' => (oracleQuery k').frame Unit

theorem lossless_spongeFnRuntime_step (h : Z → X) (k k' : X → Z) (i : SpongePort) :
    ((spongeFnRuntime h k k').step i).Lossless := by
  cases i
  exacts [(lossless_oracleQuery h).frame Unit, (lossless_oracleQuery k).frame Unit,
    (lossless_oracleQuery k').frame Unit]

theorem trace_re_spongeFnRuntime_init (h : Z → X) (k k' : X → Z) :
    (spongeFnRuntime h k k').init.matrix.trace.re = 1 :=
  (congrArg Complex.re (SubState.trace_basis (A := Unit) ())).trans Complex.one_re

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} {β : Type*}

/-- An observation `f t p` of the leaf `p` reached by `x` from `ρ` when the functions
`t = (h, k, k')` are drawn uniformly and `x` runs under `I` against their oracles. -/
noncomputable def spongeEvalDistMap [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Z → X) × (X → Z) × (X → Z) → (Σ u, W u) → β) : Measure β :=
  sampledEvalDistMap (fun t : (Z → X) × (X → Z) × (X → Z) ↦ spongeFnRuntime t.1 t.2.1 t.2.2)
    I x ρ f

/-- The experiment is the average, over all triples of functions, of the runs against them. -/
theorem spongeEvalDistMap_eq_sum [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A)
    (f : (Z → X) × (X → Z) × (X → Z) → (Σ u, W u) → β) :
    spongeEvalDistMap I x ρ f =
      (Fintype.card ((Z → X) × (X → Z) × (X → Z)) : ℝ≥0∞)⁻¹ •
        ∑ t : (Z → X) × (X → Z) × (X → Z),
          (spongeFnRuntime t.1 t.2.1 t.2.2).evalDistMap I x ρ (f t) :=
  sampledEvalDistMap_eq_sum _ I x ρ f

/-- The distribution of the leaf a program reaches against uniform `(h, k, k')`. -/
noncomputable def spongeEvalDist [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  sampledEvalDist (fun t : (Z → X) × (X → Z) × (X → Z) ↦ spongeFnRuntime t.1 t.2.1 t.2.2) I x ρ

/-- Observing the leaf itself gives the distribution of the leaf. -/
theorem spongeEvalDistMap_id [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (spongeSpec X Z) W A) (ρ : SubState A) :
    spongeEvalDistMap I x ρ (fun _ p ↦ p) = spongeEvalDist I x ρ :=
  rfl

/-- A lossless program's distribution has total mass the trace of its initial substate. -/
theorem spongeEvalDist_apply_univ_of_lossless [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (spongeSpec X Z) W A} (hx : x.Lossless I) (ρ : SubState A) :
    spongeEvalDist I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  have h := sampledEvalDist_apply_univ
    (R := fun t : (Z → X) × (X → Z) × (X → Z) ↦ spongeFnRuntime t.1 t.2.1 t.2.2)
    (fun t ↦ (spongeFnRuntime t.1 t.2.1 t.2.2).lossless_run I hx
      (lossless_spongeFnRuntime_step t.1 t.2.1 t.2.2))
    (fun t ↦ trace_re_spongeFnRuntime_init t.1 t.2.1 t.2.2) ρ
  rw [mul_one] at h
  exact h

end Quantum.Sponge

end
