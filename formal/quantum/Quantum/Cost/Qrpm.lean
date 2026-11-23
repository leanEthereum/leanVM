module

public import Quantum.Cost.GateSet
public import Quantum.Xmss.Assembly.BoundValue
public import Quantum.Sphincs.Assembly.BoundValue

@[expose] public section

/-!
# Gate-count security in the QRPM

A gate-set adversary (`GateAdversary Γ`) is a program over the named operations of the gate set
`Γ` and the adversary's ports; its interpretation (`GateAdversary.toAdversary`) is an adversary of
the QRPM SUF-CMA game with the same calls. Its cost charges `Γ.gates o` per local operation and
`GK` per call of `φ` or `φ⁻¹` (`permGates GK`, one cost for both directions); signing requests
are answered by the challenger and cost the adversary nothing.

`GateSecure sch e limit GK bound`: every gate-set adversary within `G` gates on every path and
`limit` signing requests forges with probability at most `bound (G / GK)`. It follows from the
query-count statement for every `GK > 0` (`gateSecure_of`). The per-call cost `GK` is an explicit
parameter.

## Main statements

* `leanXmss_qrpm_gates`, `leanSphincs_qrpm_gates`: the pinned QRPM theorems in gates.
* `leanXmss_qrpm_gates_closed`, `leanSphincs_qrpm_gates_closed`: their closed forms at
  `q = G / GK`, for every gate budget `G`.
-/

open IPFunctor
open scoped ENNReal

universe u v

namespace Quantum.SufCma

variable {Req Resp S : Type} [Fintype S] [DecidableEq S]

/-- The command charge of a port charge is the port charge of `Quantum.Cost`. -/
theorem cmdCharge_eq_portCharge {L : LocalSig.{u, v}} (c : AdvPort Req → ℕ) :
    cmdCharge (L := L) (Resp := Resp) (S := S) c = Cost.portCharge c := by
  funext A cmd
  cases cmd <;> rfl

end Quantum.SufCma

namespace Quantum.Cost.Qrpm

open Quantum.SufCma
open LeanVM.Semantics (KeccakState)

/-- A gate-set adversary in the QRPM: from the public key, a program over the operations of `Γ`
and the adversary's ports that returns a claimed forgery. -/
abbrev GateAdversary (Γ : GateSet) (PK Req Resp F S : Type) [Fintype S] [DecidableEq S] :=
  PK → QuantumComp₂ Γ.L (advSpec Req Resp S) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F S Seed SK : Type} [Fintype S] [DecidableEq S]

/-- The adversary of the QRPM game that a gate-set adversary means: each operation replaced by
its instrument, the same calls. -/
noncomputable def GateAdversary.toAdversary {Γ : GateSet}
    (A : GateAdversary Γ PK Req Resp F S) : Adversary PK Req Resp F S :=
  fun pk ↦ interpret₂ Γ (A pk)

/-- `GK` gates per call of `φ` or `φ⁻¹`; a signing request costs the adversary nothing. -/
def permGates (GK : ℕ) : AdvPort Req → ℕ
  | .perm _ => GK
  | .sign _ => 0

/-- **Gate-count security in the QRPM**: every gate-set adversary within `G` gates on every path
(its local gates plus `GK` per call of `φ` or `φ⁻¹`) and `limit` signing requests forges with
probability at most `bound (G / GK)`. -/
def GateSecure [Fintype Seed] [AddCommGroup S] (sch : Common.SufCma.Scheme Seed PK SK Req Resp F)
    (e : KeccakState ≃ S) (limit GK : ℕ) (bound : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Γ : GateSet) (G : ℕ) (A : GateAdversary Γ PK Req Resp F S),
    (∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (permGates GK)) G) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) limit) →
    winProb sch e A.toAdversary ≤ bound (G / GK)

/-- **Calls from gates in the QRPM**: query-count security with `bound` gives gate-count
security with `bound` at `G / GK` calls, for every gate set. -/
theorem gateSecure_of [Fintype Seed] [AddCommGroup S]
    {sch : Common.SufCma.Scheme Seed PK SK Req Resp F} {e : KeccakState ≃ S} {limit GK : ℕ}
    {bound : ℕ → ℝ≥0∞} (hGK : 0 < GK) (h : QuantumStronglyUnforgeable sch e limit bound) :
    GateSecure sch e limit GK bound := by
  intro Γ G A hG hS
  refine h (G / GK) A.toAdversary (fun pk ↦ ?_) (fun pk ↦ ?_)
  · rw [cmdCharge_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_gates Γ hGK (fun i ↦ ?_) (hG pk))
    cases i <;> simp [permCharge, permGates]
  · have hs := hS pk
    rw [cmdCharge_eq_portCharge] at hs ⊢
    exact (isChargeBound_interpret_iff Γ _ _ _).2 hs

/-- **leanXMSS in the QRPM, in gates**: within `G` gates, `GK` per call of `φ` or `φ⁻¹`, and
`lifetime` signing requests, forging succeeds with probability at most `qrpmBound (G / GK)`. -/
theorem leanXmss_qrpm_gates {GK : ℕ} (hGK : 0 < GK) :
    GateSecure LeanXmss.RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
      LeanXmss.lifetime GK Xmss.Assembly.qrpmBound :=
  gateSecure_of hGK Xmss.Assembly.leanXmss_qrpm_security

/-- **leanSPHINCS in the QRPM, in gates**: within `G` gates, `GK` per call of `φ` or `φ⁻¹`, and
`signatureLimit` signing requests, forging succeeds with probability at most
`sphincsQrpmBound (G / GK)`. -/
theorem leanSphincs_qrpm_gates {GK : ℕ} (hGK : 0 < GK) :
    GateSecure _root_.Sphincs.RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
      _root_.Sphincs.signatureLimit GK Quantum.Sphincs.Assembly.sphincsQrpmBound :=
  gateSecure_of hGK Quantum.Sphincs.Assembly.leanSphincs_qrpm_security

/-- **leanXMSS in the QRPM, in gates, closed form**: with `q = G / GK`, forging succeeds with
probability at most `((28 q + 21 · 2^14 √q + 75 · 2^30) / 2^64)²`, for every `G`. -/
theorem leanXmss_qrpm_gates_closed {GK : ℕ} (hGK : 0 < GK) :
    GateSecure LeanXmss.RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
      LeanXmss.lifetime GK fun q ↦
        ENNReal.ofReal (((28 * q + 21 * 2 ^ 14 * √(q : ℝ) + 75 * 2 ^ 30) / 2 ^ 64) ^ 2) :=
  fun Γ G A hG hS ↦ le_closedForm (by norm_num) (by norm_num) (by norm_num)
    (Xmss.Assembly.winProb_le_one _) (leanXmss_qrpm_gates hGK Γ G A hG hS)
    Xmss.Assembly.qrpmBound_le

/-- **leanSPHINCS in the QRPM, in gates, closed form**: with `q = G / GK`, forging succeeds with
probability at most `((4611 q + 2^11 √q + 2^36) / 2^64)²`, for every `G`. -/
theorem leanSphincs_qrpm_gates_closed {GK : ℕ} (hGK : 0 < GK) :
    GateSecure _root_.Sphincs.RandomPermutationModel.sufCmaScheme Xmss.keccakStateEquiv
      _root_.Sphincs.signatureLimit GK fun q ↦
        ENNReal.ofReal (((4611 * q + 2 ^ 11 * √(q : ℝ) + 2 ^ 36) / 2 ^ 64) ^ 2) :=
  fun Γ G A hG hS ↦ le_closedForm (by norm_num) (by norm_num) (by norm_num)
    (Quantum.Sphincs.Assembly.winProb_le_one_sph _) (leanSphincs_qrpm_gates hGK Γ G A hG hS)
    Quantum.Sphincs.Assembly.sphincsQrpmBound_le

end Quantum.Cost.Qrpm

end
