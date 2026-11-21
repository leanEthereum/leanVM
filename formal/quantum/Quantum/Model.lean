module

public import VCVio.Quantum.Oracle.Model

@[expose] public section

/-!
# The quantum random-permutation model

A permutation `φ` of a finite state type `S` is sampled uniformly once, before the program runs,
and the program may call it in both directions, each on a superposition of inputs: the forward
port applies `U_φ |x, y⟩ = |x, y + φ x⟩` and the inverse port `U_{φ⁻¹} |x, y⟩ = |x, y + φ⁻¹ x⟩`
(`qrpmSpec`, `permutationRuntime`). The response register is added into, as in VCVio's QROM
(`Quantum.additiveOracleRuntime`), so `S` is a finite additive group: for bit strings, XOR.

`qrpmEvalDistMap` averages complete runs over `φ`, each against one permutation, through VCVio's
`Quantum.sampledEvalDistMap`, of which the QROM is another instance. The classical
random-permutation model of `Statement/RandomPermutation.lean` samples `π` lazily instead; on
classical programs the two agree (`Quantum.qrpmEvalDistMap_toQuantumAt_qrpmImpl`).
-/

open MeasureTheory
open scoped ENNReal

universe u v w

namespace Quantum

/-- The two ports of a permutation oracle. -/
inductive PermutationPort where
  /-- `φ`. -/
  | forward
  /-- `φ⁻¹`. -/
  | inverse
  deriving DecidableEq

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The signature of a permutation oracle on `S`: a forward and an inverse port, each on the
register `S × S` (query input, then response), reporting nothing classical. -/
@[reducible]
def qrpmSpec (S : Type) [Fintype S] [DecidableEq S] : QuantumOracleSpec.{0, 0} where
  Port := PermutationPort
  In _ := QReg.of (S × S)
  Out _ := QReg.of (S × S)
  Result _ := Unit

variable [AddCommGroup S]

/-- The oracle of a fixed permutation `φ`: the forward port applies the oracle unitary of `φ`, the
inverse port that of `φ⁻¹`. The private register is `Unit`. -/
noncomputable def permutationRuntime (φ : Equiv.Perm S) : QuantumRuntime (qrpmSpec S) where
  D := QReg.of Unit
  init := SubState.basis ()
  step
    | .forward => (oracleQuery φ).frame Unit
    | .inverse => (oracleQuery φ.symm).frame Unit

theorem lossless_permutationRuntime_step (φ : Equiv.Perm S) (i : PermutationPort) :
    ((permutationRuntime φ).step i).Lossless := by
  cases i
  exacts [(lossless_oracleQuery φ).frame Unit, (lossless_oracleQuery φ.symm).frame Unit]

theorem trace_re_permutationRuntime_init (φ : Equiv.Perm S) :
    (permutationRuntime φ).init.matrix.trace.re = 1 :=
  (congrArg Complex.re (SubState.trace_basis (A := Unit) ())).trans Complex.one_re

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg} {β : Type*}

/-- An observation `f φ p` of the leaf `p` reached by `x` from `ρ` in the quantum
random-permutation model: `φ` is drawn uniformly from the permutations of `S`, and `x` runs
under `I` against `permutationRuntime φ`. -/
noncomputable def qrpmEvalDistMap [MeasurableSpace β] (I : L.Interp)
    (x : QuantumComp L (qrpmSpec S) W A) (ρ : SubState A) (f : Equiv.Perm S → (Σ u, W u) → β) :
    Measure β :=
  sampledEvalDistMap permutationRuntime I x ρ f

/-- The distribution of the leaf a program reaches in the quantum random-permutation model. -/
noncomputable def qrpmEvalDist [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qrpmSpec S) W A) (ρ : SubState A) : Measure (Σ u, W u) :=
  sampledEvalDist permutationRuntime I x ρ

/-- The distribution is the average, over all `|S|!` permutations, of the runs against them. -/
theorem qrpmEvalDist_eq_sum [MeasurableSpace (Σ u, W u)] (I : L.Interp)
    (x : QuantumComp L (qrpmSpec S) W A) (ρ : SubState A) :
    qrpmEvalDist I x ρ =
      ((Fintype.card S).factorial : ℝ≥0∞)⁻¹ •
        ∑ φ : Equiv.Perm S, (permutationRuntime φ).evalDist I x ρ := by
  rw [qrpmEvalDist, sampledEvalDist_eq_sum, Fintype.card_perm]

/-- A lossless program's distribution has total mass the trace of its initial substate. -/
theorem qrpmEvalDist_apply_univ_of_lossless [MeasurableSpace (Σ u, W u)] {I : L.Interp}
    {x : QuantumComp L (qrpmSpec S) W A} (hx : x.Lossless I) (ρ : SubState A) :
    qrpmEvalDist I x ρ Set.univ = ENNReal.ofReal ρ.matrix.trace.re := by
  rw [qrpmEvalDist, sampledEvalDist_apply_univ
    (fun φ ↦ (permutationRuntime φ).lossless_run I hx (lossless_permutationRuntime_step φ))
    trace_re_permutationRuntime_init, mul_one]

end Quantum

end
