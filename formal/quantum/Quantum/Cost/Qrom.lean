module

public import Quantum.Cost.GateSet
public import Quantum.Qrom.Xmss.BoundValue
public import Quantum.Qrom.Sphincs.BoundValue

@[expose] public section

/-!
# Gate-count security in the QROM

A gate-set adversary (`GateAdversary Γ`) is a program over the named operations of the gate set
`Γ` and the adversary's ports; its interpretation (`GateAdversary.toAdversary`) is an adversary of
the QROM SUF-CMA game with the same calls. Its cost charges `Γ.gates o` per local operation and
`GK` per call of `H` (`hashGates GK`); signing requests are answered by the challenger and cost
the adversary nothing.

`GateSecure sch limit GK bound`: every gate-set adversary within `G` gates on every path and
`limit` signing requests forges with probability at most `bound (G / GK)`. It follows from the
query-count statement for every `GK > 0` (`gateSecure_of`): `GK` gates per call give at most
`G / GK` calls. The per-call cost `GK` is an explicit parameter.

## Main statements

* `Quantum.Qrom.SufCma.winProb_le_one`: the winning probability is at most `1`.
* `leanXmss_qrom_gates`, `leanSphincs_qrom_gates`: the pinned QROM theorems in gates.
* `leanXmss_qrom_gates_closed`, `leanSphincs_qrom_gates_closed`: their closed forms at
  `q = G / GK`, for every gate budget `G`.
-/

open IPFunctor MeasureTheory
open scoped ENNReal

universe u v w u₁ v₁

namespace Quantum.Cost

/-- Observations of runs against a sampled runtime are subprobabilities. -/
theorem sampledEvalDistMap_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}
    {β : Type*} [MeasurableSpace β] (R : Ω → QuantumRuntime spec) (I : L.Interp)
    (x : QuantumComp L spec W A) (ρ : SubState A) (f : Ω → (Σ u, W u) → β) (s : Set β) :
    sampledEvalDistMap R I x ρ f s ≤ 1 := by
  refine (measure_mono (Set.subset_univ s)).trans ?_
  rw [sampledEvalDistMap_apply R I x ρ f MeasurableSet.univ]
  calc ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * (R ω).evalDistMap I x ρ (f ω) Set.univ
      ≤ ∑ _ω : Ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * 1 :=
        Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left
          ((R ω).outcomeLawWith_le_one I x ρ (f ω) Set.univ) zero_le
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _)]

end Quantum.Cost

namespace Quantum.Qrom.SufCma

variable {PK Req Resp F Seed SK : Type}

/-- The winning probability is at most `1`. -/
theorem winProb_le_one [Fintype Seed] (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
    (A : Adversary PK Req Resp F) : winProb sch A ≤ 1 := by
  unfold winProb
  calc _ ≤ ∑ S0 : Seed, Pr{let s ← sch.sampleSeed}[s = S0] * 1 :=
        Finset.sum_le_sum fun S0 _ ↦ mul_le_mul_of_nonneg_left
          (Cost.sampledEvalDistMap_le_one _ _ _ _ _ _) zero_le
    _ ≤ 1 := by simpa using sum_prEvent_eq_some_le_one sch.sampleSeed some

/-- The command charge of a port charge is the port charge of `Quantum.Cost`. -/
theorem cmdCharge_eq_portCharge {L : LocalSig.{u, v}} (c : AdvPort Req → ℕ) :
    cmdCharge (L := L) (Resp := Resp) c = Cost.portCharge c := by
  funext A cmd
  cases cmd <;> rfl

end Quantum.Qrom.SufCma

namespace Quantum.Cost.Qrom

open Quantum.Qrom Quantum.Qrom.SufCma

/-- A gate-set adversary in the QROM: from the public key, a program over the operations of `Γ`
and the adversary's ports that returns a claimed forgery. -/
abbrev GateAdversary (Γ : GateSet) (PK Req Resp F : Type) :=
  PK → QuantumComp₂ Γ.L (advSpec Req Resp) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F Seed SK : Type}

/-- The adversary of the QROM game that a gate-set adversary means: each operation replaced by
its instrument, the same calls. -/
noncomputable def GateAdversary.toAdversary {Γ : GateSet} (A : GateAdversary Γ PK Req Resp F) :
    Adversary PK Req Resp F :=
  fun pk ↦ interpret₂ Γ (A pk)

/-- `GK` gates per call of `H`; a signing request costs the adversary nothing. -/
def hashGates (GK : ℕ) : AdvPort Req → ℕ
  | .hash => GK
  | .sign _ => 0

/-- **Gate-count security in the QROM**: every gate-set adversary within `G` gates on every path
(its local gates plus `GK` per call of `H`) and `limit` signing requests forges with probability at
most `bound (G / GK)`. -/
def GateSecure [Fintype Seed] (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
    (limit GK : ℕ) (bound : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Γ : GateSet) (G : ℕ) (A : GateAdversary Γ PK Req Resp F),
    (∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (hashGates GK)) G) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) limit) →
    winProb sch A.toAdversary ≤ bound (G / GK)

/-- **Calls from gates in the QROM**: query-count security with `bound` gives gate-count
security with `bound` at `G / GK` calls, for every gate set. -/
theorem gateSecure_of [Fintype Seed] {sch : SchemeOver RomOracles Seed PK SK Req Resp F}
    {limit GK : ℕ} {bound : ℕ → ℝ≥0∞} (hGK : 0 < GK)
    (h : QuantumStronglyUnforgeable sch limit bound) : GateSecure sch limit GK bound := by
  intro Γ G A hG hS
  refine h (G / GK) A.toAdversary (fun pk ↦ ?_) (fun pk ↦ ?_)
  · rw [cmdCharge_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_gates Γ hGK (fun i ↦ ?_) (hG pk))
    cases i <;> simp [hashCharge, hashGates]
  · have hs := hS pk
    rw [cmdCharge_eq_portCharge] at hs ⊢
    exact (isChargeBound_interpret_iff Γ _ _ _).2 hs

/-- **leanXMSS in the QROM, in gates**: within `G` gates, `GK` per call of `H`, and `lifetime`
signing requests, forging succeeds with probability at most `xmssQromBound (G / GK)`. -/
theorem leanXmss_qrom_gates {GK : ℕ} (hGK : 0 < GK) :
    GateSecure Xmss.xmssRom LeanXmss.lifetime GK Xmss.xmssQromBound :=
  gateSecure_of hGK Xmss.leanXmss_qrom_security

/-- **leanSPHINCS in the QROM, in gates**: within `G` gates, `GK` per call of `H`, and
`signatureLimit` signing requests, forging succeeds with probability at most
`sphincsQromBound (G / GK)`. -/
theorem leanSphincs_qrom_gates {GK : ℕ} (hGK : 0 < GK) :
    GateSecure Sphincs.sphincsRom _root_.Sphincs.signatureLimit GK Sphincs.sphincsQromBound :=
  gateSecure_of hGK Sphincs.leanSphincs_qrom_security

/-- **leanXMSS in the QROM, in gates, closed form**: with `q = G / GK`, forging succeeds with
probability at most `((4.45 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`, for every `G`. -/
theorem leanXmss_qrom_gates_closed {GK : ℕ} (hGK : 0 < GK) :
    GateSecure Xmss.xmssRom LeanXmss.lifetime GK fun q ↦
      ENNReal.ofReal (((4.45 * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2) :=
  fun Γ G A hG hS ↦ le_closedForm (by norm_num) (by norm_num) (by norm_num)
    (winProb_le_one _ _) (leanXmss_qrom_gates hGK Γ G A hG hS) Xmss.xmssQromBound_le

/-- **leanSPHINCS in the QROM, in gates, closed form**: with `q = G / GK`, forging succeeds with
probability at most `((5.86 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`, for every `G`. -/
theorem leanSphincs_qrom_gates_closed {GK : ℕ} (hGK : 0 < GK) :
    GateSecure Sphincs.sphincsRom _root_.Sphincs.signatureLimit GK fun q ↦
      ENNReal.ofReal (((5.86 * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2) :=
  fun Γ G A hG hS ↦ le_closedForm (by norm_num) (by norm_num) (by norm_num)
    (winProb_le_one _ _) (leanSphincs_qrom_gates hGK Γ G A hG hS) Sphincs.sphincsQromBound_le

end Quantum.Cost.Qrom

end
