module

public import Quantum.StdModel.Qrom.SphincsItsrHybFacts
public import Quantum.StdModel.Qrom.SphincsItsrCalls

@[expose] public section

/-!
# The hidden-value hybrid of leanSPHINCS's ITSR game in the QROM (runtime 1 against runtime 2)

The graded hybrid (`uavg_win_runtime1R_le_graded_total`) for the canonical realized ITSR game
`gameIQ msgPol A θ`, against any runtime-1 tables `L θ` covering the hidden cells `hidCells θ`,
with the sources of the direct pipeline (`sourcesQ`, `kappaQ`, `Quantum.Qrom.Sphincs.Hybrid`); the
stream reindexing (`uavg_gameIT_msgPol_eq_strPol`) then moves runtime 2 to `strPol`.

* **Calls of `F`** (`uavg_spongeMassI_le`): at most `q · 2^-128`, from the `q` adversary calls
  (`advCalls_gameIQ`) and the source invariant (`hinvI`).
* **Reads** (`uavg_readMassI_le`): at most `clsCapQ · 2^-128` (`readCalls_gameIQ`).
* **The hybrid** (`uavg_runtime1R_gameIQ_le`): `E P₁ ≤ (√(E p2I strPol) + hybTermQ q)²`.
-/

open Matrix IPFunctor MeasureTheory
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.StdModel.Sphincs.SphItsr

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Qrom.Sphincs
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT runtime1R extCls
  sum_totalWeight_portMass_runtimeR_le_inv)

attribute [local irreducible] Quantum.Qrom.hashQ LeanSphincsOver.messageDigest

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk)
    (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk)
    (Quantum.Qrom.SufCma.cmdCharge Quantum.Qrom.SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **The masses of the ITSR game at the calls of `F`**: at most `q · 2^-128`, averaged over the
hidden values. -/
theorem uavg_spongeMassI_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (spongeMass (hidCells θ) ∅ ∅) (gameIQ msgPol A θ) initH) ≤ q * kappaQ := by
  have hc : (fun i ↦ if (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i = false) then 1 else 0) =
      fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem) (recSpec TPos SelMem) i
        then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i) with h | h <;> simp [h]
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments
    (fun i ↦ extCls PairOut Qrom.HashDomain (Finset TPos × SelMem) (recSpec TPos SelMem) i = false)
    m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameIQ msgPol A θ) (fun _ ↦ initH)
    (fun _ ↦ initH_posSemidef) (fun j ↦ viewByOn_gameIT SelMem cwUpd msgPol A m0H initH j)
    (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvI msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) A θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ by rw [hc]; exact advCalls_gameIQ msgPol A hhash hsign θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one q

/-- **The read masses of the ITSR game**: at most `clsCapQ · 2^-128`, averaged over the hidden
values. -/
theorem uavg_readMassI_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (readMass (hidCells θ) ∅ ∅) (gameIQ msgPol A θ) initH) ≤ clsCapQ * kappaQ := by
  refine (uavg_mono fun θ ↦ totalWeight_le_totalWeight (runtimeR m0H) .instruments
    (fun i σ _ ↦ readMass_le_readPortQ θ i σ) (gameIQ msgPol A θ) initH_posSemidef).trans ?_
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments (fun i ↦ readPortQ i = true) m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameIQ msgPol A θ)
    (fun _ ↦ initH) (fun _ ↦ initH_posSemidef)
    (fun j ↦ viewByOn_gameIT SelMem cwUpd msgPol A m0H initH j) (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvI msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) A θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ readCalls_gameIQ msgPol A hhash hsign θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one clsCapQ

/-- **The hidden-value hybrid of the ITSR game**: for runtime-1 tables `L θ` covering the hidden
cells, runtime 1's averaged ITSR win at `msgPol` is at most `(√(E p2I strPol) + hybTermQ q)²`. -/
theorem uavg_runtime1R_gameIQ_le (L : TVals → Hw PairOut Qrom.HashDomain)
    (hL : ∀ θ, Covers (L θ) (hidCells θ) ∅ ∅) :
    uavg (fun θ ↦ (runtime1R PairOut Qrom.HashDomain (L θ) m0H).evalDistMap .instruments
      (gameIQ msgPol A θ) (SubState.basis ()) winObsQ {true}) ≤
      (uavg (p2I strPol A) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  have h := uavg_win_runtime1R_le_graded_total .instruments L hidCells (fun _ ↦ ∅)
    (fun _ ↦ ∅) hL m0H (fun θ ↦ gameIQ msgPol A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) q
    (fun θ ↦ advCalls_gameIQ msgPol A hhash hsign θ) (q * kappaQ) (clsCapQ * kappaQ)
    (uavg_spongeMassI_le A hhash hsign) (uavg_readMassI_le A hhash hsign)
  rw [add_assoc] at h
  have he : uavg (p2I msgPol A) = uavg (p2I strPol A) :=
    uavg_gameIT_msgPol_eq_strPol cwUpd A (fun _ ↦ none) (SubState.basis ()) winObsQ
      (measurableSet_singleton true)
  rw [← he]
  exact h

end Quantum.StdModel.Sphincs.SphItsr

end
