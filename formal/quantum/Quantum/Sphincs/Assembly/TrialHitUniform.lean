module

public import Quantum.Sphincs.Assembly.TrialHit

@[expose] public section

/-!
# The decompressed databases of leanSPHINCS's game are uniform off the programmable cells

TrialHit's `DecUniformHypP` at every digest policy, memory, adversary and template data
(`decUniformHypP`): DecUniform's `eventWeight_hwDecProj_le` for runtime 2 with record ports
(`runtimeR`, whose record ports act as the identity on the databases:
`clsKraus_one_commute_hwDecProj`), along the canonical game, whose program calls program only
`ProgCell` cells (`forallQueries_cellPortIn_gameT`), hardwired in the static `cellsHw`. Hence
`trialHitMassAt_le_keccak` (`2^-189` on data with `TrialsOff` and `PermGood 18`) and its average
over any finite family of template data, `uavg_trialHitMass_le_of_good`.
-/

open Matrix
open scoped ENNReal Kronecker ComplexOrder

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (uavg uavg_mono)
open Quantum.Xmss.Assembly (recHwSpec recSpec recStep recStep_branch runtimeR)

namespace Quantum.Sphincs.Assembly

/- Instance search for the run families over the register `SReg` exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-- A port programming a cell of `Pc` programs a cell hardwired in `cellsHw Pc`. -/
theorem hwPortIn_of_cellPortIn {Pc : SpongeQuery X Z → Prop}
    (i : (recHwSpec X Z HPos Selections).Port) (h : CellPortIn Pc i) :
    HwPortIn (Finset HPos × Selections) (cellsHw Pc) i := by
  rcases i with ((_ | _) | c) | _
  · trivial
  · trivial
  · exact cellIn_cellsHw h
  · trivial

/-- **The decompressed databases of the canonical game are uniform off the programmable cells**:
TrialHit's `DecUniformHypP` everywhere. -/
theorem decUniformHypP (pol : DigestPolicy) (m₀ : Mem HPos) (A : SAdversary) (pub : Pub)
    (v : (s : HPos) → XD s) : DecUniformHypP pol m₀ A pub v := by
  intro F hF
  have hx := forallQueries_cellPortIn_gameT pub v m₀ cwUpd pol A
    ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)
  have hE : ∀ s : HwReg X Z (Mem HPos), s ∈ {s | F s.1} ↔ F s.1 := fun _ ↦ Iff.rfl
  classical
  have h := eventWeight_hwDecProj_le (t := recSpec HPos Selections) .instruments (hwEmpty X Z) m₀
    recStep {s | F s.1}
    (fun T r ↦ branch_comm_of_commute (recStep_branch T r)
      (clsKraus_one_commute_hwDecProj {s | F s.1} F hE _ _))
    (W := cellsHw (ProgCell pub v)) hF hE (fun i _ _ h ↦ hwPortIn_of_cellPortIn i h)
    (gameR pol A pub v) (SubState.basis ()).posSemidef hx
  have htr : ENNReal.ofReal ((SubState.basis ()).matrix : Matrix (QReg.of Unit) (QReg.of Unit)
      ℂ).trace.re = 1 := by
    rw [SubState.matrix_basis, Matrix.trace_single_eq_same, Complex.one_re, ENNReal.ofReal_one]
  rw [htr, one_mul] at h
  exact h

/-- **The trial-hit mass at Keccak's sizes**: at most `2^-189` on template data with `TrialsOff`
and `PermGood pub.perm 18`, at every digest policy. -/
theorem trialHitMassAt_le_keccak (pol : DigestPolicy) (m₀ : Mem HPos) (A : SAdversary)
    {pub : Pub} {v : (s : HPos) → XD s} (hoff : TrialsOff pub.xw pub.keys.1 (valsOf v))
    (hπ : PermGood pub.perm 18) : trialHitMassAt pol m₀ A pub v ≤ ENNReal.ofReal (1 / 2 ^ 189) :=
  trialHitMass_le_keccak (decUniformHypP pol m₀ A pub v) hoff hπ

/-- **The averaged trial-hit mass** of the event side: at most `2^-189` over any finite family of
template data `(pubF y, valF y)`, counting only the members of a set on which `TrialsOff` and
`PermGood 18` hold. -/
theorem uavg_trialHitMass_le_of_good {Y : Type} [Fintype Y] [Nonempty Y] (m₀ : Mem HPos)
    (A : SAdversary) (pubF : Y → Pub) (valF : Y → (s : HPos) → XD s) (good : Y → Prop)
    [DecidablePred good]
    (hg : ∀ y, good y → TrialsOff (pubF y).xw (pubF y).keys.1 (valsOf (valF y)) ∧
      PermGood (pubF y).perm 18) :
    uavg (fun y ↦ if good y then trialHitMassP m₀ A (pubF y) (valF y) else 0) ≤
      ENNReal.ofReal (1 / 2 ^ 189) := by
  refine (uavg_mono fun y ↦ ?_ : _ ≤ uavg fun _ : Y ↦ ENNReal.ofReal (1 / 2 ^ 189)).trans ?_
  · split_ifs with h
    · exact trialHitMassAt_le_keccak strPol m₀ A (hg y h).1 (hg y h).2
    · exact zero_le
  · unfold uavg
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        (ENNReal.natCast_ne_top _), one_mul]

end Quantum.Sphincs.Assembly

end
