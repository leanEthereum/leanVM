module

public import Quantum.StdModel.Sphincs.Costs

@[expose] public section

/-!
# leanSPHINCS's reductions B3 and B4: their hash calls

The hash-call charges of the ITSR reduction `itsrRed` (B3) and of the EncTCR+C reduction `encRed`
(B4) without cost hypotheses, for a world whose cost per hash call is `κ` (`HashCostLe W κ`).
Coins and challenger queries cost nothing under `hcallCost`; the routed hash keeps the bound `κ`
on every kind (`routeHash_kinds`).

With `q` hash calls and `signs` signing requests of `A`:
* B3 (`isChargeBound_itsrRed_hashN`): `273410 κ + ((q + 12886291206 κ · signs) + 0)`: key
  generation in the setup, the signer per request, an output without hash calls.
* B4 (`isChargeBound_encRed_hashN`): `0 + ((q + 12886291206 κ · signs) + 1758 κ)`: a setup of
  challenger queries only, the signer per request, the recorded verification (`879 κ`) and its
  recorded inputs hashed again (`879 κ`).
-/

open IPFunctor OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key)
open Quantum.Qrom.Sphincs (RawPos)
open Common (QueryCostAtMost QueryCostAtMost.bind QueryCostAtMost.mono isWeightBound_pure
  isWeightBound_map)

namespace Quantum.StdModel.Sphincs

attribute [local instance] secretsSampleable encRndSampleable

/-- The targets make only challenger queries. -/
theorem encTargets_hcost (W : OracleWorld) (msg : Key → Digest) : ∀ Ks : List Key,
    QueryCostAtMost (encTargets W msg Ks) (hcallCost W (R' := EncCtrPorts)) 0
  | [] => isWeightBound_pure _ _ _
  | K :: Ks => by
    rw [encTargets]
    exact ((queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).bind fun _ ↦
      (encTargets_hcost W msg Ks).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by omega)

/-- The setup after the sampling makes only challenger queries. -/
theorem encCore_hcost (W : OracleWorld) (s : KeygenDomain → Digest) (r : Message → Digest) :
    QueryCostAtMost (encCore W s r) (hcallCost W (R' := EncCtrPorts)) 0 := by
  have hask : ∀ p t, QueryCostAtMost (encAsk W s p t) (hcallCost W (R' := EncCtrPorts)) 0 := by
    intro p t
    unfold encAsk
    split
    · exact isWeightBound_pure _ _ _
    · exact queryCostAtMost_portQ W (fun _ ↦ le_rfl) _
  unfold encCore
  exact ((buildDig_cost hask).bind fun _ ↦ (encTargets_hcost W _ _).bind fun _ ↦
    (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp)

section B34

variable {W : OracleWorld} {κ : ℕ} (hW : HashCostLe W κ) (A : SAdv W) {q signs : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) signs)
include hW

/-- **B3's setup**: key generation, `273410 κ`. -/
theorem itsrPre_hcost :
    QueryCostAtMost (itsrPre W) (hcallCost W (R' := ItsrSpec)) (273410 * κ) := by
  have hk : HashKinds (itsrHash W) (hcallCost W (R' := ItsrSpec)) (Kinds.const κ) :=
    hashKinds_liftW hW
  unfold itsrPre
  refine ((queryCostAtMost_liftW_of W (c := W.cost) (fun _ ↦ le_rfl)
    (queryCostAtMost_sample hW _)).bind fun P ↦ (queryCostAtMost_liftW_of W (c := W.cost)
      (fun _ ↦ le_rfl) (queryCostAtMost_sample hW _)).bind fun s ↦
    (keygenFromSeed_cost (routeHash_kinds (P := P) hk (fun _ ↦ isWeightBound_pure _ _ _)
      (fun _ ↦ isWeightBound_pure _ _ _)) 0).bind fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  rw [keygenW_const]
  omega

/-- **B3's signer**: an ITSR query (free) and the routed signer, `12886291206 κ`. -/
theorem itsrHandler_hcost (st : ItsrState) (M : Message) :
    QueryCostAtMost (itsrHandler W st M) (hcallCost W (R' := ItsrSpec)) (12886291206 * κ) := by
  have hk : HashKinds (itsrHash W) (hcallCost W (R' := ItsrSpec)) (Kinds.const κ) :=
    hashKinds_liftW hW
  have hr : QueryCostAtMost (itsrRnd W st.1.2.2 st.2.2 M) (hcallCost W (R' := ItsrSpec)) 0 := by
    unfold itsrRnd
    split
    · exact isWeightBound_pure _ _ _
    · exact isWeightBound_map _ (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _)
  unfold itsrHandler
  refine (hr.bind fun x ↦ (sign_cost (routeHash_kinds (P := st.1.1) hk
    (fun _ ↦ isWeightBound_pure _ _ _) (fun _ ↦ isWeightBound_pure _ _ _)) 0 M).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono ?_
  rw [signW_const]
  omega

include hq hs in
/-- **B3's hash calls**: `A`'s, key generation `273410 κ`, the signer `12886291206 κ` per
signing request, none in the output. -/
theorem isChargeBound_itsrRed_hashN :
    IFreeM.IsChargeBound (itsrRed W A ()) (cmdCharge hashCharge)
      (273410 * κ + ((q + 12886291206 * κ * signs) + 0)) :=
  isChargeBound_itsrRed_hash W A (itsrPre_hcost hW) (itsrHandler_hcost hW) hq hs

/-- **B4's setup**: sampling and challenger queries only. -/
theorem encRedPre_hcost :
    QueryCostAtMost (encRedPre W) (hcallCost W (R' := EncCtrPorts)) 0 := by
  unfold encRedPre
  exact ((queryCostAtMost_liftW_of W (c := W.cost) (fun _ ↦ le_rfl)
    (queryCostAtMost_sample hW _)).bind fun _ ↦ (queryCostAtMost_liftW_of W (c := W.cost)
      (fun _ ↦ le_rfl) (queryCostAtMost_sample hW _)).bind fun _ ↦ encCore_hcost W _ _).mono
        (by omega)

/-- **B4's signer**: the routed signer, `12886291206 κ`. -/
theorem encRedSign_hcost (st : EncData × SignLog) (M : Message) :
    QueryCostAtMost (encRedSign W st M) (hcallCost W (R' := EncCtrPorts)) (12886291206 * κ) := by
  have hk : HashKinds (encH W) (hcallCost W (R' := EncCtrPorts)) (Kinds.const κ) :=
    hashKinds_liftW hW
  unfold encRedSign
  refine ((sign_cost (routeHash_kinds (P := st.1.P) hk (fun _ ↦ isWeightBound_pure _ _ _)
    (fun _ ↦ isWeightBound_pure _ _ _)) 0 M).bind fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  rw [signW_const]
  omega

/-- **B4's output**: the recorded verification and its recorded inputs hashed again, `1758 κ`. -/
theorem encRedPost_hcost (a : EncData) (f : Forgery) (st : EncData × SignLog) :
    QueryCostAtMost (encRedPost W a f st) (hcallCost W (R' := EncCtrPorts)) (1758 * κ) := by
  unfold encRedPost
  exact (recVerify_mapM_cost (h := encH W)
    (fun l hl ↦ queryCostAtMost_liftW_of W (c := W.cost) (fun _ ↦ le_rfl) (hW.hash l hl))
    (fun rv os ↦ encPick a.P a.tg (rv.2.zip os)) a.pk f.message f.signature).mono (by omega)

include hq hs in
/-- **B4's hash calls**: `A`'s, none in the setup, the signer `12886291206 κ` per signing
request, the output `1758 κ`. -/
theorem isChargeBound_encRed_hashN :
    IFreeM.IsChargeBound (encRed W A ()) (cmdCharge hashCharge)
      (0 + ((q + 12886291206 * κ * signs) + 1758 * κ)) :=
  isChargeBound_encRed_hash W A (encRedPre_hcost hW) (encRedSign_hcost hW)
    (encRedPost_hcost hW) hq hs

end B34

end Quantum.StdModel.Sphincs

end
