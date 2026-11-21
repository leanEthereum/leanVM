module

public import Quantum.StdModel.Sphincs.Costs

@[expose] public section

/-!
# B5 and B6: their honest work and their challenger queries

The charge lemmas of the CPRE reduction `cpreRed` (B5) and of the SM-TCR reduction `tcrRed` (B6)
without cost hypotheses, `κ` the world's cost per hash call (`HashCostLe W κ`), `q` the hash
calls and `signs` the signing requests of `A`.

* B5's hash calls (`isChargeBound_cpreRed_hashN`): `0 + ((q + 2 κ · signs) + 1758 κ)`: the setup
  makes only challenger queries, the signer computes the two `H_msg` outputs, the output runs the
  recorded verification and hashes the recorded inputs again.
* B5's challenger queries (`isChargeBound_cpreRed_callN`):
  `(keyOrder.length + 885443715538058477568 + 52776558133248 + 1) + (24 · signs + 0)`: the build
  (one query per key position), the counter search of each of the `3 · 2 ^ 36` keys at its cap
  `2 ^ 32`, the openings of the `3 · 2 ^ 36 · 256` chain positions, the reveal; the `24` FORS
  secrets of a signature.
* B6's hash calls (`isChargeBound_tcrRed_hashN`):
  `273410 κ + ((q + 12886291206 κ · signs) + 1758 κ)`: the routed key generation, the routed
  signer, the recorded verification with its inputs hashed again.
-/

open IPFunctor OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Quantum.Sphincs (Key messageDigestInput)
open Quantum.Qrom.Sphincs (RawPos)
open Common (QueryCostAtMost QueryCostAtMost.bind QueryCostAtMost.mono isWeightBound_pure
  QueryCostAtMost.bind_of_support)

namespace Quantum.StdModel.Sphincs

/-! ## B5's programs -/

section Cpre

variable (W : OracleWorld) {w : (W.Oracles + CpreS).Domain → ℕ} {b : ℕ}

/-- The number of keys. -/
theorem length_cpreKeys : cpreKeys.length = 206158430208 := by
  unfold cpreKeys
  simp only [List.length_product, List.length_finRange]
  norm_num [layerCount, indexBits, layerHeight, topLayer]

/-- The number of chain positions. -/
theorem length_cprePositions : cprePositions.length = 52776558133248 := by
  unfold cprePositions
  simp only [List.length_product, List.length_finRange, length_cpreKeys]
  norm_num [chainCount, chainLength, winternitzBits]

/-- An ask of the build makes at most one query. -/
theorem cpreAsk_cost (hw : ∀ x, w (.inr x) ≤ b) (p : RawPos) (t : RawPos → Digest) :
    QueryCostAtMost (cpreAsk W p t) w b := by
  unfold cpreAsk
  split
  · unfold cpreChainAsk
    split
    · exact queryCostAtMost_portQ W hw _
    · exact isWeightBound_pure _ _ _
  all_goals first
    | exact queryCostAtMost_portQ W hw _
    | exact isWeightBound_pure _ _ _

/-- The counter search with `n` trials left makes at most `n` queries. -/
theorem cpreSelFrom_cost (hw : ∀ x, w (.inr x) ≤ b) (K : Key) (m : Digest) :
    ∀ n c, QueryCostAtMost (cpreSelFrom W K m n c) w (n * b)
  | 0, _ => isWeightBound_pure _ _ _
  | n + 1, c => by
    rw [cpreSelFrom]
    refine QueryCostAtMost.mono ((queryCostAtMost_portQ W hw _).bind fun d ↦ ?_)
      (Nat.le_of_eq (by rw [Nat.succ_mul, Nat.add_comm]))
    split
    · exact isWeightBound_pure _ _ _
    · exact cpreSelFrom_cost hw K m n (c + 1)

/-- An opening makes at most one query. -/
theorem cpreOpenQ_cost (hw : ∀ x, w (.inr x) ≤ b) (sel : Key → Option (EncodingCounter × Encoding))
    (x : Key × ChainIndex × Fin chainLength) : QueryCostAtMost (cpreOpenQ W sel x) w b := by
  unfold cpreOpenQ
  split
  · split
    · exact queryCostAtMost_portQ W hw _
    · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

/-- **The hidden-parameter work**: the build, the counter searches at their cap, the openings. -/
theorem cpreStage_cost (hw : ∀ x, w (.inr x) ≤ b) :
    QueryCostAtMost (cpreStage W) w (keyOrder.length * b + (cpreKeys.length *
      (encodingAttemptLimit * b) + (cprePositions.length * b + 0))) := by
  unfold cpreStage
  exact (buildDig_cost (cpreAsk_cost W hw)).bind fun tf ↦
    (cpreTab_cost cpreKeys none fun K ↦ cpreSelFrom_cost W hw K _ encodingAttemptLimit 0).bind
      fun sel ↦ (cpreTab_cost cprePositions 0 (cpreOpenQ_cost W hw sel)).bind fun _ ↦
        isWeightBound_pure _ _ 0

/-- **B5's setup**: the randomizers' sample, the hidden-parameter work, the reveal. -/
theorem cprePre_cost (hw : ∀ x, w (.inr x) ≤ b) {s : ℕ}
    (hs : QueryCostAtMost (liftW CpreS (Props.sample W (Message → Digest))) w s) :
    QueryCostAtMost (cprePre W) w (s + ((keyOrder.length * b + (cpreKeys.length *
      (encodingAttemptLimit * b) + (cprePositions.length * b + 0))) + (b + 0))) := by
  unfold cprePre
  exact hs.bind fun _ ↦ (cpreStage_cost W hw).bind fun _ ↦
    (queryCostAtMost_portQ W hw _).bind fun _ ↦ isWeightBound_pure _ _ 0

/-- The FORS secrets of a signature: one query per FORS tree. -/
theorem cpreForsQ_cost (hw : ∀ x, w (.inr x) ≤ b) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (cpreForsQ W idx lv) w (forsTreeCount * b) := by
  unfold cpreForsQ
  exact QueryCostAtMost.mono (cpreTab_cost (List.finRange forsTreeCount) 0 fun _ ↦
    queryCostAtMost_portQ W hw _) (Nat.le_of_eq (by rw [List.length_finRange]))

theorem cpreSignIdx_cost (hw : ∀ x, w (.inr x) ≤ b) (a : CpreData) (sl : SignLog)
    (fl : List (CpreFJ × Digest)) (M : Message) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (cpreSignIdx W a sl fl M idx lv) w (forsTreeCount * b + 0) := by
  unfold cpreSignIdx
  split
  · exact isWeightBound_pure _ _ _
  · exact (cpreForsQ_cost W hw idx lv).bind fun _ ↦ isWeightBound_pure _ _ 0

/-- **B5's signer**: two `H_msg` hashes, then the FORS secrets. -/
theorem cpreHandler_cost (hw : ∀ x, w (.inr x) ≤ b) {a : ℕ}
    (hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (cpreHash W l) w a)
    (st : CpreSt) (M : Message) :
    QueryCostAtMost (cpreHandler W st M) w (a + (a + (forsTreeCount * b + 0))) := by
  have hl : ∀ R P root M c, (messageDigestInput R P root M c).length ≤ Quantum.Qrom.maxLen :=
    fun R P root M c ↦ by
      rw [Quantum.Sphincs.length_messageDigestInput]
      decide
  unfold cpreHandler
  exact (hh _ (hl _ _ _ _ _)).bind fun _ ↦ (hh _ (hl _ _ _ _ _)).bind fun _ ↦
    cpreSignIdx_cost W hw _ _ _ _ _ _

/-- **B5's output**: the recorded verification, the recorded inputs hashed again. -/
theorem cprePost_cost {a : ℕ}
    (hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (cpreHash W l) w a)
    (x : CpreData) (f : Forgery) (st : CpreSt) :
    QueryCostAtMost (cprePost W x f st) w (879 * a + 879 * a) :=
  recVerify_mapM_cost hh (fun rv os ↦ cpreOut x st.2.2 (cpreLookup rv.2 os)) _ _ _

end Cpre

/-! ## B6's programs -/

section Tcr

variable (W : OracleWorld) {w : (W.Oracles + TcrPorts).Domain → ℕ} {a : ℕ}
  (hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (tcrHash W l) w a)
include hh

/-- Hashing recorded inputs of at most `maxLen` bytes: `a` per input. -/
theorem tcrHashAll_cost :
    ∀ xs : List HashInput, (∀ y ∈ xs, y.length ≤ Quantum.Qrom.maxLen) →
      QueryCostAtMost (tcrHashAll W xs) w (xs.length * a)
  | [], _ => isWeightBound_pure _ _ _
  | x :: xs, hx => by
    rw [tcrHashAll]
    exact QueryCostAtMost.mono ((hh x (hx x List.mem_cons_self)).bind fun _ ↦
      (tcrHashAll_cost xs fun y hy ↦ hx y (List.mem_cons_of_mem _ hy)).bind fun _ ↦
        isWeightBound_pure _ _ 0)
      (Nat.le_of_eq (by rw [List.length_cons, Nat.succ_mul, Nat.add_zero, Nat.add_comm]))

/-- **B6's output**: the recorded verification, the recorded inputs hashed again. -/
theorem tcrPost_cost (x : TcrData) (f : Forgery) (st : TcrSt) :
    QueryCostAtMost (tcrPost W x f st) w (879 * a + 879 * a) := by
  unfold tcrPost
  refine QueryCostAtMost.bind_of_support (recVerify_cost hh x.pk f.message f.signature).1
    fun rv hrv ↦ ?_
  obtain ⟨hl, hs⟩ := (recVerify_cost hh x.pk f.message f.signature).2 rv hrv
  exact QueryCostAtMost.mono ((tcrHashAll_cost W hh rv.2 hs).bind fun _ ↦
    isWeightBound_pure _ _ 0) (by rw [Nat.add_zero]; exact Nat.mul_le_mul_right _ hl)

end Tcr

/-! ## The charges -/

section B56

variable {W : OracleWorld} {κ : ℕ} (hW : HashCostLe W κ) (A : SAdv W) {q signs : ℕ}
  (hq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hs : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) signs)

/-- B5's setup's challenger queries. -/
theorem cprePre_port :
    QueryCostAtMost (cprePre W) (portCost W (R' := CpreS))
      (keyOrder.length + 885443715538058477568 + 52776558133248 + 1) := by
  refine QueryCostAtMost.mono (cprePre_cost W (b := 1) (fun _ ↦ le_rfl)
    (queryCostAtMost_liftW_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl) (queryCostAtMost_zero _))) ?_
  rw [length_cpreKeys, length_cprePositions, show encodingAttemptLimit = 4294967296 from rfl]
  omega

/-- B5's hash makes no challenger query. -/
theorem cpreHash_port (l : HashInput) :
    QueryCostAtMost (cpreHash W l) (portCost W (R' := CpreS)) 0 :=
  queryCostAtMost_liftW_of W (c := fun _ ↦ 0) (fun _ ↦ le_rfl) (queryCostAtMost_zero _)

/-- B5's signer's challenger queries: the `24` FORS secrets. -/
theorem cpreHandler_port (st : CpreSt) (M : Message) :
    QueryCostAtMost (cpreHandler W st M) (portCost W (R' := CpreS)) 24 :=
  QueryCostAtMost.mono (cpreHandler_cost W (b := 1) (fun _ ↦ le_rfl)
    (fun l _ ↦ cpreHash_port l) st M) (by simp [forsTreeCount])

/-- B5's output makes no challenger query. -/
theorem cprePost_port (x : CpreData) (f : Forgery) (st : CpreSt) :
    QueryCostAtMost (cprePost W x f st) (portCost W (R' := CpreS)) 0 :=
  QueryCostAtMost.mono (cprePost_cost W (fun l _ ↦ cpreHash_port l) x f st) (by omega)

section Hash

include hW

theorem cpreHash_hcall (l : HashInput) (hl : l.length ≤ Quantum.Qrom.maxLen) :
    QueryCostAtMost (cpreHash W l) (hcallCost W (R' := CpreS)) κ :=
  queryCostAtMost_liftW_of W (fun _ ↦ le_rfl) (hW.hash l hl)

/-- B5's setup makes no hash call. -/
theorem cprePre_hcall : QueryCostAtMost (cprePre W) (hcallCost W (R' := CpreS)) 0 :=
  QueryCostAtMost.mono (cprePre_cost W (b := 0) (fun _ ↦ le_rfl)
    (queryCostAtMost_liftW_of W (c := W.cost) (fun _ ↦ le_rfl) (queryCostAtMost_sample hW _)))
    (by omega)

/-- B5's signer: the two `H_msg` outputs. -/
theorem cpreHandler_hcall (st : CpreSt) (M : Message) :
    QueryCostAtMost (cpreHandler W st M) (hcallCost W (R' := CpreS)) (2 * κ) :=
  QueryCostAtMost.mono (cpreHandler_cost W (b := 0) (fun _ ↦ le_rfl) (cpreHash_hcall hW) st M)
    (by omega)

/-- B5's output: the recorded verification, its inputs hashed again. -/
theorem cprePost_hcall (x : CpreData) (f : Forgery) (st : CpreSt) :
    QueryCostAtMost (cprePost W x f st) (hcallCost W (R' := CpreS)) (1758 * κ) :=
  QueryCostAtMost.mono (cprePost_cost W (cpreHash_hcall hW) x f st) (by omega)

end Hash

include hW hq hs in
/-- **B5's hash calls**: `A`'s, `2 κ` per signing request (the two `H_msg` outputs), `1758 κ` in
the output (the recorded verification, its inputs hashed again). -/
theorem isChargeBound_cpreRed_hashN :
    IFreeM.IsChargeBound (cpreRed W A ()) (cmdCharge hashCharge)
      (0 + ((q + 2 * κ * signs) + 1758 * κ)) :=
  (isChargeBound_cpreRed W A (cprePre_hcall hW) (cpreHandler_hcall hW) (cprePost_hcall hW)
    cprePre_port cpreHandler_port cprePost_port hq hs ()).1

include hs in
/-- **B5's challenger queries**: the build (one per key position), the counter search of every
key at its cap `2 ^ 32`, the openings of every chain position, the reveal; the `24` FORS secrets
per signing request. -/
theorem isChargeBound_cpreRed_callN :
    IFreeM.IsChargeBound (cpreRed W A ()) (cmdCharge callCharge)
      ((keyOrder.length + 885443715538058477568 + 52776558133248 + 1) + (24 * signs + 0)) :=
  isChargeBound_slRed_call W _ _ _ _ _ cprePre_port cpreHandler_port cprePost_port
    fun a ↦ hs a.pk

include hW hq hs in
/-- **B6's hash calls**: `A`'s, key generation `273410 κ`, the routed signer `12886291206 κ` per
signing request, `1758 κ` in the output (the recorded verification, its inputs hashed again). -/
theorem isChargeBound_tcrRed_hashN :
    IFreeM.IsChargeBound (tcrRed W A ()) (cmdCharge hashCharge)
      (273410 * κ + ((q + 12886291206 * κ * signs) + 1758 * κ)) := by
  have hk : HashKinds (tcrHash W) (hcallCost W (R' := TcrPorts)) (Kinds.const κ) :=
    hashKinds_liftW hW
  have hh : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen →
      QueryCostAtMost (tcrHash W l) (hcallCost W (R' := TcrPorts)) κ :=
    fun l hl ↦ queryCostAtMost_liftW_of W (fun _ ↦ le_rfl) (hW.hash l hl)
  have hsamp : ∀ (α : Type) [SampleableType α],
      QueryCostAtMost (liftW TcrPorts (Props.sample W α)) (hcallCost W (R' := TcrPorts)) 0 :=
    fun α _ ↦ queryCostAtMost_liftW_of W (c := W.cost) (fun _ ↦ le_rfl)
      (queryCostAtMost_sample hW α)
  have hask : ∀ s p t, QueryCostAtMost (tcrAsk W s p t) (hcallCost W (R' := TcrPorts)) 0 := by
    intro s p t
    unfold tcrAsk
    by_cases hg : tcrIsTgt p = true
    · simp only [hg, ↓reduceIte]
      exact queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _
    · have hg' : tcrIsTgt p = false := by simpa using hg
      simp only [hg', Bool.false_eq_true, ↓reduceIte]
      rcases tcrSecOf p with _ | k <;> dsimp only
      · exact queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _
      · exact isWeightBound_pure _ _ _
  have hpre : QueryCostAtMost (tcrPre W) (hcallCost W (R' := TcrPorts)) (273410 * κ) := by
    unfold tcrPre tcrRest
    refine QueryCostAtMost.mono ((hsamp _).bind fun s ↦ (hsamp _).bind fun r ↦
      (buildDig_cost (hask s)).bind fun _ ↦
        (queryCostAtMost_portQ W (b := 0) (fun _ ↦ le_rfl) _).bind fun P ↦
          (keygenFromSeed_cost (routeHash_kinds hk (fun _ ↦ isWeightBound_pure _ _ _)
            (fun _ ↦ isWeightBound_pure _ _ _)) 0).bind fun _ ↦ isWeightBound_pure _ _ 0) ?_
    simp [keygenW_const]
  have hσ : ∀ st M,
      QueryCostAtMost (tcrSigner W st M) (hcallCost W (R' := TcrPorts)) (12886291206 * κ) := by
    intro st M
    unfold tcrSigner
    refine QueryCostAtMost.mono ((sign_cost (routeHash_kinds hk
      (fun _ ↦ isWeightBound_pure _ _ _) (fun _ ↦ isWeightBound_pure _ _ _)) 0 M).bind fun _ ↦
        isWeightBound_pure _ _ 0) ?_
    simp [signW_const]
  have hpost : ∀ x f st,
      QueryCostAtMost (tcrPost W x f st) (hcallCost W (R' := TcrPorts)) (1758 * κ) :=
    fun x f st ↦ QueryCostAtMost.mono (tcrPost_cost W hh x f st) (by omega)
  exact isChargeBound_tcrRed W A hpre hσ hpost hq hs ()

end B56

end Quantum.StdModel.Sphincs

end
