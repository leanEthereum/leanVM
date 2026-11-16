module

public import Quantum.Xmss.Assembly.TrialHit
public import Quantum.Sponge.Oracle.Hardwired.DecUniform

@[expose] public section

/-!
# The decompressed databases of the game are uniform off the table

TrialHit's `DecUniformHyp` for every table: DecUniform's `eventWeight_hwDecProj_le` for runtime 2
with record ports (`runtimeR`, the hardwired runtime from `hwEmpty` extended by `recStep`, whose
Kraus operators act as the identity on the databases: `clsKraus_one_commute_hwDecProj`), along the
canonical game, whose program calls program only cells of `tableHw L` (ProgView's
`forallQueries_of_progsIn` with `progsIn_gameT`). WinDecomp's `decProj` is DecUniform's
`hwDecProj`. Hence `uavg_trialHitMass_le_goodL`: the averaged trial-hit mass is at most `2^-399`
on the tables with `TrialsOff` and `PermGood 18`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid
open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma LeanXmss.RandomPermutationModel

/-- A program port programming a cell of `W` with its value programs a cell hardwired in `W`. -/
theorem hwPortIn_of_hwSupp (m₀ : Finset HPos × Selections) (W : Hw X Z)
    (i : (recHwSpec X Z HPos Selections).Port) (E : QReg)
    (σ : Matrix (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
      (((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ)
    (h : hwSupp Selections m₀ W i E σ) : HwPortIn (Finset HPos × Selections) W i := by
  rcases i with ((_ | _) | c) | _
  · trivial
  · trivial
  · have hc := h.1
    cases c with
    | programH z v => exact fun h' ↦ Option.some_ne_none v (hc.symm.trans h')
    | programK x v => exact fun h' ↦ Option.some_ne_none v (hc.symm.trans h')
    | programK' x v => exact fun h' ↦ Option.some_ne_none v (hc.symm.trans h')
  · trivial

/-- **The decompressed databases of the canonical game are uniform off `tableHw L`**: TrialHit's
`DecUniformHyp` at every table. -/
theorem decUniformHyp (m₀ : Finset HPos × Selections) (A : Adversary (X × Z)) (L : HonestTable) :
    DecUniformHyp m₀ A L := by
  intro F hF
  have hx := forallQueries_of_progsIn (tableHw L) (valueAt L) m₀ .instruments
    (gameT Selections cwUpd (pubOf L) A)
    (progsIn_gameT (tableHw L) (valueAt L) cwUpd (progsOf_tableHw L) A) _
    (supp_init_hw m₀ (tableHw L))
  have hE : ∀ s : HwReg X Z (Finset HPos × Selections), s ∈ {s | F s.1} ↔ F s.1 :=
    fun _ ↦ Iff.rfl
  classical
  have h := eventWeight_hwDecProj_le (t := recSpec HPos Selections) .instruments (hwEmpty X Z) m₀
    recStep {s | F s.1}
    (fun T r ↦ branch_comm_of_commute (recStep_branch T r)
      (clsKraus_one_commute_hwDecProj {s | F s.1} F hE _ _))
    (W := tableHw L) (fun D D' h₁ h₂ h₃ ↦ hF D D' ⟨h₁, h₂, h₃⟩) hE
    (hwPortIn_of_hwSupp m₀ (tableHw L)) (wGame A L) (SubState.basis ()).posSemidef hx
  have htr : ENNReal.ofReal ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit)
      ℂ).trace.re = 1 := by
    rw [SubState.matrix_basis, Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one]
  rw [htr, one_mul] at h
  exact h

/-- **The averaged trial-hit mass**: at most `2^-399` over the tables of a set on which
`TrialsOff` and `PermGood 18` hold. -/
theorem uavg_trialHitMass_le_of_good (m₀ : Finset HPos × Selections) (A : Adversary (X × Z))
    (good : HonestTable → Prop) [DecidablePred good]
    (hg : ∀ L, good L → TrialsOff L ∧ PermGood L.perm 18) :
    uavg (fun L ↦ if good L then trialHitMass m₀ A L else 0) ≤ ENNReal.ofReal (1 / 2 ^ 399) :=
  uavg_trialHitMass_le good fun L h ↦ ⟨decUniformHyp m₀ A L, hg L h⟩

end Quantum.Xmss.Assembly

end
