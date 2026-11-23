module

public import Quantum.Cost.Qrom
public import Quantum.Cost.Qrpm
public import Quantum.Qrom.Xmss.DepthBoundValue

@[expose] public section

/-!
# Gate-and-depth security against parallel adversaries

A parallel gate-set adversary (`ParGateAdversary Γ`) is a program over the operations of the gate
set `Γ` and the parallel adversary's ports: rounds of `w` oracle calls at once and signing
requests. Its interpretation (`ParGateAdversary.toAdversary`) is a parallel adversary of the
existing games with the same calls.

Two costs. **Gates**: `Γ.gates o` per local operation and `GK · w` per round of width `w`
(`hashGatesPar`, `permGatesPar`). **Depth**: any charge `δ o` per local operation and `DK` per
round, whatever its width (`hashDepthPar`, `permDepthPar`, through `opCharge δ`). Only the
number of rounds enters the parallel bounds, so the depth hypothesis is a round-depth charge and
the statements hold for every `δ` (the intended instance is `δ = 0`); reading a circuit of depth
`MD` with oracle boxes of depth `DK` as a program of at most `MD / DK` rounds is the standard
re-layering of the circuit, not formalized here.

`GateDepthSecure sch limit GK DK bound`: every parallel gate-set adversary within `G` gates and
depth charge `MD` on every path and `limit` signing requests forges with probability at most
`bound (G / GK) (MD / DK)`. It follows from parallel query-count security for every `GK, DK > 0`
(`Qrom.gateDepthSecure_of`, `Qrpm.gateDepthSecure_of`): `GK · w` gates per round give total
width at most `G / GK`, depth `DK` per round gives at most `MD / DK` rounds.

## Main statements

* `Qrom.gateDepthSecure_of`, `Qrpm.gateDepthSecure_of`: the transfer in both models. Each of
  the other depth theorems (`QuantumStronglyUnforgeablePar` for leanSPHINCS in the QROM and for
  both schemes in the QRPM) gives its gate-and-depth form by one application of these.
* `leanXmss_qrom_gateDepth`: leanXMSS in the QROM (`leanXmss_qrom_depth_security`).
* `leanXmss_qrom_gateDepth_closed`: its closed form at `q = G / GK`, `d = MD / DK`, for every `G`
  and `MD`.
-/

open IPFunctor
open scoped ENNReal

universe u v

namespace Quantum.Qrom.SufCma

variable {Req Resp : Type}

/-- The parallel command charge of a port charge is the port charge of `Quantum.Cost`. -/
theorem cmdChargePar_eq_portCharge {L : LocalSig.{u, v}} (c : AdvPortPar Req → ℕ) :
    cmdChargePar (L := L) (Resp := Resp) c = Cost.portCharge c := by
  funext A cmd
  cases cmd <;> rfl

end Quantum.Qrom.SufCma

namespace Quantum.SufCma

variable {Req Resp S : Type} [Fintype S] [DecidableEq S]

/-- The parallel command charge of a port charge is the port charge of `Quantum.Cost`. -/
theorem cmdChargePar_eq_portCharge {L : LocalSig.{u, v}} (c : AdvPortPar Req → ℕ) :
    cmdChargePar (L := L) (Resp := Resp) (S := S) c = Cost.portCharge c := by
  funext A cmd
  cases cmd <;> rfl

end Quantum.SufCma

/-! ## The QROM -/

namespace Quantum.Cost.Qrom

open Quantum.Qrom Quantum.Qrom.SufCma

/-- A parallel gate-set adversary in the QROM: from the public key, a program over the operations
of `Γ` and the parallel adversary's ports that returns a claimed forgery. -/
abbrev ParGateAdversary (Γ : GateSet) (PK Req Resp F : Type) :=
  PK → QuantumComp₂ Γ.L (advSpecPar Req Resp) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F Seed SK : Type}

/-- The parallel adversary of the QROM game that a gate-set adversary means: each operation
replaced by its instrument, the same rounds and requests. -/
noncomputable def ParGateAdversary.toAdversary {Γ : GateSet}
    (A : ParGateAdversary Γ PK Req Resp F) : AdversaryPar PK Req Resp F :=
  fun pk ↦ interpret₂ Γ (A pk)

/-- `GK · w` gates per round of width `w`; a signing request costs the adversary nothing. -/
def hashGatesPar (GK : ℕ) : AdvPortPar Req → ℕ
  | .hashPar w => GK * w
  | .sign _ => 0

/-- Depth `DK` per round, whatever its width; a signing request costs no depth. -/
def hashDepthPar (DK : ℕ) : AdvPortPar Req → ℕ
  | .hashPar _ => DK
  | .sign _ => 0

/-- **Gate-and-depth security in the QROM**: every parallel gate-set adversary within `G` gates
(its local gates plus `GK · w` per round of width `w`) and depth charge `MD` (any `δ o` per local
operation plus `DK` per round) on every path, and `limit` signing requests, forges with
probability at most `bound (G / GK) (MD / DK)`. -/
def GateDepthSecure [Fintype Seed] (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
    (limit GK DK : ℕ) (bound : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ)
    (A : ParGateAdversary Γ PK Req Resp F),
    (∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (hashGatesPar GK)) G) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (hashDepthPar DK)) MD) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar signChargePar) limit) →
    winProbPar sch A.toAdversary ≤ bound (G / GK) (MD / DK)

/-- **Calls and rounds from gates and depth in the QROM**: parallel query-count security with
`bound` gives gate-and-depth security with `bound` at `G / GK` calls in `MD / DK` rounds, for
every gate set and every depth charge of the local operations. -/
theorem gateDepthSecure_of [Fintype Seed] {sch : SchemeOver RomOracles Seed PK SK Req Resp F}
    {limit GK DK : ℕ} {bound : ℕ → ℕ → ℝ≥0∞} (hGK : 0 < GK) (hDK : 0 < DK)
    (h : QuantumStronglyUnforgeablePar sch limit bound) :
    GateDepthSecure sch limit GK DK bound := by
  intro Γ δ G MD A hG hD hS
  refine h (G / GK) (MD / DK) A.toAdversary (fun pk ↦ ?_) (fun pk ↦ ?_) (fun pk ↦ ?_)
  · rw [cmdChargePar_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_gates Γ hGK (fun i ↦ ?_) (hG pk))
    cases i <;> simp [widthCharge, hashGatesPar]
  · rw [cmdChargePar_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_opCharge hDK (fun i ↦ ?_) (hD pk))
    cases i <;> simp [roundCharge, hashDepthPar]
  · have hs := hS pk
    rw [cmdChargePar_eq_portCharge] at hs ⊢
    exact (isChargeBound_interpret_iff Γ _ _ _).2 hs

/-- The winning probability of a parallel adversary is at most `1`. -/
theorem winProbPar_le_one [Fintype Seed] (sch : SchemeOver RomOracles Seed PK SK Req Resp F)
    (A : AdversaryPar PK Req Resp F) : winProbPar sch A ≤ 1 :=
  winProb_le_one sch _

/-- **leanXMSS in the QROM, in gates and depth**: within `G` gates (`GK` per call of `H`), depth
charge `MD` (`DK` per round) and `lifetime` signing requests, forging succeeds with probability
at most `xmssQromDepthBound (G / GK) (MD / DK)`. -/
theorem leanXmss_qrom_gateDepth {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure Xmss.xmssRom LeanXmss.lifetime GK DK Xmss.xmssQromDepthBound :=
  gateDepthSecure_of hGK hDK Xmss.leanXmss_qrom_depth_security

/-- The closed form of the depth-aware leanXMSS QROM bound is at least `1` beyond `2^100` calls:
its linear term `0.7072 · 2^-35 q` alone exceeds `2^64`. -/
theorem one_le_xmssQromDepthClosed {q d : ℕ} (hq : ¬q ≤ 2 ^ 100) :
    1 ≤ ((4.45 * √((q : ℝ) * (min d q : ℕ)) + 0.7072 * (2 ^ 35)⁻¹ * q +
      0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by
  have hq' : (2 : ℝ) ^ 100 ≤ q := by exact_mod_cast (not_le.mp hq).le
  have h1 := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  have h2 := Real.sqrt_nonneg (q : ℝ)
  refine one_le_pow₀ ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **leanXMSS in the QROM, in gates and depth, closed form**: with `q = G / GK` and
`d = MD / DK`, forging succeeds with probability at most
`((4.45 √(q · min d q) + 0.7072 · 2^-35 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`, for every
`G` and `MD`. -/
theorem leanXmss_qrom_gateDepth_closed {GK DK : ℕ} (hGK : 0 < GK) (hDK : 0 < DK) :
    GateDepthSecure Xmss.xmssRom LeanXmss.lifetime GK DK fun q d ↦
      ENNReal.ofReal (((4.45 * √((q : ℝ) * (min d q : ℕ)) + 0.7072 * (2 ^ 35)⁻¹ * q +
        0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2) := by
  intro Γ δ G MD A hG hD hS
  by_cases hq : G / GK ≤ 2 ^ 100
  · exact (leanXmss_qrom_gateDepth hGK hDK Γ δ G MD A hG hD hS).trans
      (Xmss.xmssQromDepthBound_le hq)
  · exact (winProbPar_le_one _ _).trans
      (ENNReal.one_le_ofReal.2 (one_le_xmssQromDepthClosed hq))

end Quantum.Cost.Qrom

/-! ## The QRPM -/

namespace Quantum.Cost.Qrpm

open Quantum.SufCma
open LeanVM.Semantics (KeccakState)

/-- A parallel gate-set adversary in the QRPM: from the public key, a program over the operations
of `Γ` and the parallel adversary's ports that returns a claimed forgery. -/
abbrev ParGateAdversary (Γ : GateSet) (PK Req Resp F S : Type) [Fintype S] [DecidableEq S] :=
  PK → QuantumComp₂ Γ.L (advSpecPar Req Resp S) (QReg.of Unit) (QReg.of Unit) F

variable {PK Req Resp F S Seed SK : Type} [Fintype S] [DecidableEq S]

/-- The parallel adversary of the QRPM game that a gate-set adversary means. -/
noncomputable def ParGateAdversary.toAdversary {Γ : GateSet}
    (A : ParGateAdversary Γ PK Req Resp F S) : AdversaryPar PK Req Resp F S :=
  fun pk ↦ interpret₂ Γ (A pk)

/-- `GK · w` gates per round of `w` calls of `φ` or `φ⁻¹`; a signing request costs nothing. -/
def permGatesPar (GK : ℕ) : AdvPortPar Req → ℕ
  | .permPar w _ => GK * w
  | .sign _ => 0

/-- Depth `DK` per round, whatever its width and directions; a signing request costs no
depth. -/
def permDepthPar (DK : ℕ) : AdvPortPar Req → ℕ
  | .permPar _ _ => DK
  | .sign _ => 0

/-- **Gate-and-depth security in the QRPM**: as `Qrom.GateDepthSecure`, with `GK · w` gates and
depth `DK` per round of `w` permutation calls. -/
def GateDepthSecure [Fintype Seed] [AddCommGroup S]
    (sch : Common.SufCma.Scheme Seed PK SK Req Resp F) (e : KeccakState ≃ S)
    (limit GK DK : ℕ) (bound : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (Γ : GateSet) (δ : ∀ ⦃A : QReg⦄, Γ.L.Op A → ℕ) (G MD : ℕ)
    (A : ParGateAdversary Γ PK Req Resp F S),
    (∀ pk, IFreeM.IsChargeBound (A pk) (gateCharge Γ (permGatesPar GK)) G) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (opCharge δ (permDepthPar DK)) MD) →
    (∀ pk, IFreeM.IsChargeBound (A pk) (cmdChargePar signChargePar) limit) →
    winProbPar sch e A.toAdversary ≤ bound (G / GK) (MD / DK)

/-- **Calls and rounds from gates and depth in the QRPM**: parallel query-count security with
`bound` gives gate-and-depth security with `bound` at `G / GK` calls in `MD / DK` rounds. -/
theorem gateDepthSecure_of [Fintype Seed] [AddCommGroup S]
    {sch : Common.SufCma.Scheme Seed PK SK Req Resp F} {e : KeccakState ≃ S}
    {limit GK DK : ℕ} {bound : ℕ → ℕ → ℝ≥0∞} (hGK : 0 < GK) (hDK : 0 < DK)
    (h : QuantumStronglyUnforgeablePar sch e limit bound) :
    GateDepthSecure sch e limit GK DK bound := by
  intro Γ δ G MD A hG hD hS
  refine h (G / GK) (MD / DK) A.toAdversary (fun pk ↦ ?_) (fun pk ↦ ?_) (fun pk ↦ ?_)
  · rw [cmdChargePar_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_gates Γ hGK (fun i ↦ ?_) (hG pk))
    cases i <;> simp [widthCharge, permGatesPar]
  · rw [cmdChargePar_eq_portCharge]
    refine (isChargeBound_interpret_iff Γ _ _ _).2
      (calls_le_of_opCharge hDK (fun i ↦ ?_) (hD pk))
    cases i <;> simp [roundCharge, permDepthPar]
  · have hs := hS pk
    rw [cmdChargePar_eq_portCharge] at hs ⊢
    exact (isChargeBound_interpret_iff Γ _ _ _).2 hs

end Quantum.Cost.Qrpm

end
