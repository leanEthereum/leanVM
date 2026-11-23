module

public import Quantum.Sphincs.Assembly.Template
public import Quantum.Xmss.Assembly.GameTCalls

@[expose] public section

/-!
# The calls of leanSPHINCS's template game, by kind

Charge bounds on `gameT M upd pol pub A` (`Quantum.Sphincs.Assembly.Template`) for every digest
policy `pol`, public datum `pub` and trial update `upd`: `a` per sponge call, `b` per read, `c` per
program call, `d` per reveal (`tCharge`; realized, `rCharge`, where a reveal is a record call).

* **The verifier's blocks** (`verify_hashBlocks`): the hash-query verifier (`schemeWithHash`)
  queries at most `verifyBlocks = 903` Keccak-f blocks (`H_msg` two, FORS `24 · 11 + 4`, each
  layer `1 + 64 · 3 + 8 + 10`).
* **Program calls of the slots** (`length_slotPorts`, `nBlk_chain`, …): three per block; one
  block for a chain step, a node, a FORS leaf or node and `H_msg`, eight for a one-time leaf, four
  for the FORS roots. A FORS opening programs at most `804` cells
  (`sum_length_slotPorts_forsSlots_le`), a layer signature at most `630`
  (`sum_length_slotPorts_layerSlots_le`: `192` chain steps for any codeword, the leaf, `10`
  nodes), the digest `6`.
* Per component: `chg_grindK` (three reads per counter trial, one block), `chg_forsOpenT`
  (`forsCalls`), `chg_signLayerT` (`layerCalls`), `chg_signT` (`signCalls`), `chg_challengeT`
  (`6a` per permutation call, `S` per signing request), composed in `chg_gameT_of_signT` and
  `chg_realizeT_gameT` (`gameCalls a b c d q`).
* **`hN`**: `hN_sponge` (`6q` sponge calls), `hN_cls` and `hN_readRec` (`clsCalls` classical
  calls, `clsCalls_eq`), `hN_prog` (`progCalls = 2700 · signatureLimit` program calls).
-/

open Matrix IPFunctor OracleComp OracleSpec
open scoped ENNReal Kronecker

universe u v w

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput ChainStep chainLength
  winternitzBits littleEndianBytes digestsPayload)
open HashSig.OverPermutation (sequenceFin walkChain foldPath nodePayload)
open Quantum.Xmss (X Z blocks length_blocks hashBlocks hashBlocks_le extProgCharge)
open Quantum.Xmss.Hybrid (LazyProg)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLiftQ readLens tmplLens
  realizeT revealThen progThen hashTrial rdCharge chg_act chg_map chg_hashTrial chg_readsProgram
  RevealVals
  isChargeBound_simulate extCls)

namespace Quantum.Sphincs.Assembly

/-! ## The verifier's blocks -/

section verifyCost

attribute [local irreducible] sequenceFin walkChain foldPath

/-- One hash query costs its blocks. -/
theorem hashQuery_cost (input : HashInput) :
    QueryCostAtMost (WithHash.hashQuery input) hashBlocks (hashBlocks input) := by
  rw [WithHash.hashQuery, HasQuery.instOfMonadLift_query]
  exact isWeightBound_query _ _

theorem hqAddressedHash_cost (seed : PublicParameter) (address : Address) (payload : HashInput)
    {k : ℕ} (h : 48 + payload.length < 136 * (k + 1)) :
    QueryCostAtMost (WithHash.addressedHash WithHash.hashQuery seed address payload) hashBlocks
      (k + 1) := by
  unfold WithHash.addressedHash
  refine ((hashQuery_cost _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  rw [Nat.add_zero]
  exact hashBlocks_le (by rw [length_addressedHashInput]; exact h)

theorem hqChainWalk_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) (start steps : ℕ) (x : Digest) :
    QueryCostAtMost (WithHash.chainWalk WithHash.hashQuery seed l τ e i start steps x) hashBlocks
      (steps * 1) :=
  walkChain_cost _ 1 (fun _ _ ↦ hqAddressedHash_cost _ _ _ (k := 0) (by
    simp [littleEndianBytes])) start steps x

theorem hqRecoverChain_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) (digit : HashSig.WinternitzDigit) (x : Digest) :
    QueryCostAtMost (WithHash.recoverChain WithHash.hashQuery seed l τ e i digit x) hashBlocks
      (3 * 1) :=
  (hqChainWalk_cost _ _ _ _ _ _ _ _).mono
    (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem hqLeafHash_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (endpoints : ChainIndex → Digest) :
    QueryCostAtMost (WithHash.leafHash WithHash.hashQuery seed l τ e endpoints) hashBlocks 8 :=
  hqAddressedHash_cost _ _ _ (k := 7) (by rw [length_digestsPayload]; simp [chainCount])

theorem hqEncode_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (msg : Digest) (counter : EncodingCounter) :
    QueryCostAtMost (WithHash.encode WithHash.hashQuery seed l τ e msg counter) hashBlocks 1 := by
  unfold WithHash.encode
  exact ((hqAddressedHash_cost _ _ _ (k := 0) (by simp [littleEndianBytes, bigEndianBytes])).bind
    fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)

/-- The blocks of a one-time leaf's recovery. -/
def otsLeafBlocks : ℕ := 1 + (chainCount * (3 * 1) + 8)

theorem hqOtsLeaf_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (msg : Digest) (counter : EncodingCounter) (values : ChainIndex → Digest) :
    QueryCostAtMost (WithHash.otsLeaf WithHash.hashQuery seed l τ e msg counter values) hashBlocks
      otsLeafBlocks := by
  unfold WithHash.otsLeaf
  refine ((hqEncode_cost _ _ _ _ _ _).bind fun x ↦ ?_).mono le_rfl
  cases x with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ hqRecoverChain_cost _ _ _ _ _ _ _)
      fun _ ↦ QueryCostAtMost.bind (hqLeafHash_cost _ _ _ _ _) fun _ ↦
        isWeightBound_pure _ _ 0).mono (by simp)

theorem hqTreeFold_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (path : ℕ → Digest) (levels : ℕ) (x : Digest) :
    QueryCostAtMost (WithHash.treeFold WithHash.hashQuery seed l τ e path levels x) hashBlocks
      (levels * 1) :=
  foldPath_cost _ 1 (fun _ _ _ _ ↦ hqAddressedHash_cost _ _ _ (k := 0) (by
    simp [nodePayload, littleEndianBytes])) _ _ levels x

/-- The blocks of one FORS tree's recovery. -/
def forsTreeBlocks : ℕ := 1 + forsTreeHeight * 1

theorem hqForsTreeRecover_cost (seed : PublicParameter) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) :
    QueryCostAtMost (WithHash.forsTreeRecover WithHash.hashQuery seed idx κ leaf opening)
      hashBlocks forsTreeBlocks := by
  unfold WithHash.forsTreeRecover WithHash.forsLeafHash
  exact (hqAddressedHash_cost _ _ _ (k := 0) (by simp [littleEndianBytes])).bind fun _ ↦
    foldPath_cost _ 1 (fun _ _ _ _ ↦ hqAddressedHash_cost _ _ _ (k := 0) (by
      simp [nodePayload, littleEndianBytes])) _ _ _ _

/-- The blocks of the FORS key's recovery. -/
def forsRecoverBlocks : ℕ := forsTreeCount * forsTreeBlocks + 4

theorem hqForsRecover_cost (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    QueryCostAtMost (WithHash.forsRecover WithHash.hashQuery seed idx leaves opening) hashBlocks
      forsRecoverBlocks := by
  unfold WithHash.forsRecover WithHash.forsPublicKey
  exact (sequenceFin_cost _ _ fun _ ↦ hqForsTreeRecover_cost _ _ _ _ _).bind fun _ ↦
    hqAddressedHash_cost _ _ _ (k := 3) (by rw [length_digestsPayload]; simp [forsTreeCount])

theorem hqMessageDigest_cost (pk : PublicKey) (R : Randomizer) (msg : Message) :
    QueryCostAtMost (WithHash.messageDigest WithHash.hashQuery pk R msg) hashBlocks 2 := by
  unfold WithHash.messageDigest WithHash.messageDigestCall
  exact (QueryCostAtMost.bind (sequenceFin_cost 1 _ fun _ ↦ (hashQuery_cost _).mono
    (hashBlocks_le (k := 0) (by rw [length_messageDigestInput]; omega))) fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp [digestCallCount])

/-- The blocks of one layer of the walk up the hypertree. -/
def layerBlocks : ℕ := otsLeafBlocks + 10 * 1

theorem hqVerifyLayers_cost (seed : PublicParameter) (idx : Index) (sig : Signature) :
    ∀ n msg, QueryCostAtMost (WithHash.verifyLayers WithHash.hashQuery seed idx sig n msg)
      hashBlocks (n * layerBlocks)
  | 0, _ => by
    simp only [WithHash.verifyLayers]
    exact isWeightBound_pure _ _ _
  | n + 1, msg => by
    simp only [WithHash.verifyLayers]
    split
    · refine ((hqOtsLeaf_cost _ _ _ _ _ _ _).bind fun x ↦ ?_).mono
        (Q := otsLeafBlocks + (10 * 1 + n * layerBlocks)) (by
          have := Nat.add_one_mul n layerBlocks; unfold layerBlocks at *; omega)
      cases x with
      | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
      | some _ =>
        refine ((hqTreeFold_cost _ _ _ _ _ _ _).bind fun _ ↦ ?_).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (layerHeight_le _)) _)
        split
        · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
        · exact hqVerifyLayers_cost seed idx sig n _
    · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

/-- **The verifier's blocks.** -/
def verifyBlocks : ℕ := 2 + (forsRecoverBlocks + layerCount * layerBlocks)

theorem verifyBlocks_eq : verifyBlocks = 903 := by
  simp [verifyBlocks, forsRecoverBlocks, forsTreeBlocks, layerBlocks, otsLeafBlocks, chainCount,
    forsTreeCount, forsTreeHeight, layerCount]

/-- **The hash-query verifier queries at most `verifyBlocks` blocks.** -/
theorem verify_hashBlocks (pk : PublicKey) (f : Forgery) :
    QueryCostAtMost (schemeWithHash.verify pk f) hashBlocks verifyBlocks := by
  show QueryCostAtMost (WithHash.verify WithHash.hashQuery pk f.message f.signature) _ _
  unfold WithHash.verify
  refine (hqMessageDigest_cost _ _ _).bind fun _ ↦ (hqForsRecover_cost _ _ _ _).bind fun _ ↦ ?_
  refine ((hqVerifyLayers_cost _ _ _ _ _).bind fun r ↦ ?_).mono
    (Q := layerCount * layerBlocks + 0) (by simp)
  cases r <;> exact isWeightBound_pure _ _ _

end verifyCost

/-! ## Charges by kind -/

section charges

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports by kind: `a` per sponge call, `b` per read, `c` per program
call, `d` per reveal. -/
def tCharge (a b c d : ℕ) : (SSpec M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rCharge (a b c d : ℕ) : (recHwSpec X Z HPos M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (a b c d : ℕ)

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeT (v : (s : HPos) → XD s) {A : QReg}
    {y : QuantumComp L (SSpec M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (realizeT v y) (portCharge (rCharge M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens v) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rCharge M a b c d) s ((tmplLens v).toFunA s cmd)) =
      portCharge (tCharge M a b c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift {A : QReg} {y : QuantumComp L (hwReadSpec X Z M) Ω A} {n : ℕ}
    (h : IFreeM.IsChargeBound y (portCharge (rdCharge M a b)) n) :
    IFreeM.IsChargeBound (readLift goodAll y) (portCharge (tCharge M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodAll) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tCharge M a b c d) s
      ((readLens goodAll).toFunA s cmd)) = portCharge (rdCharge M a b) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen {B B' : QReg} {α : Type} (T : Finset HPos)
    (k : RevealVals XD T × (Finset HPos × M) → QComp (SSpec M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (revealThen goodAll T k) (portCharge (tCharge M a b c d)) (d + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen {B B' : QReg} {α : Type} (p : LazyProg X Z HPos XD) (hp : goodAll p)
    (k : QComp (SSpec M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tCharge M a b c d)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tCharge M a b c d)) (c + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c n, fun r ↦ ?_⟩
  simp only [tCharge, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPorts (B : QReg) (ps : List (LazyProg X Z HPos XD)) :
    IFreeM.IsChargeBound (progPorts M B ps) (portCharge (tCharge M a b c d)) (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThen a b c d p trivial _ ih) (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

omit [Fintype M] [DecidableEq M] in
theorem chg_progSlots (pub : Pub) (B : QReg) (ss : List Slot) :
    IFreeM.IsChargeBound (progSlots M pub B ss) (portCharge (tCharge M a b c d))
      (c * (ss.map fun s ↦ (slotPorts pub s).length).sum) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    refine IFreeM.IsChargeBound.mono
      (FreeM₂.isChargeBound_bind (chg_progPorts a b c d B _) fun _ ↦ ih) (le_of_eq ?_)
    rw [List.map_cons, List.sum_cons, Nat.mul_add]

/-! ### The slots' program calls -/

theorem length_pathPorts (pub : Pub) (T₀ : Finset HPos) (bl : RevealVals XD T₀ → ℕ → X)
    (cor : RevealVals XD T₀ → X → X → X) (n : ℕ) :
    (pathPorts pub T₀ bl cor n).length = 3 * n := by
  simp [pathPorts, List.length_flatMap, Nat.mul_comm]

theorem length_slotPorts (pub : Pub) (s : Slot) :
    (slotPorts pub s).length = 3 * nBlk pub.seed s :=
  length_pathPorts pub _ _ _ _

theorem length_digestPorts (pub : Pub) (pol : DigestPolicy) (T : Finset HPos) (msg : Message) :
    (digestPorts pub pol T msg).length = 6 := by
  rw [digestPorts, List.length_append, hmsgPorts, hmsgPorts, length_pathPorts, length_pathPorts]

theorem nBlk_chain (P : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) (step : ChainStep) : nBlk P (.chain l τ e i step) = 1 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (littleEndianBytes 16 _)).length / 136 + 1 = 1
  rw [length_addressedHashInput, length_le16]

theorem nBlk_leaf (P : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    nBlk P (.leaf l τ e) = 8 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (digestsPayload _)).length / 136 + 1 = 8
  rw [length_addressedHashInput, length_digestsPayload]
  simp [chainCount]

theorem nBlk_node (P : PublicParameter) (l : Layer) (τ : TreeIndex) (height index : ℕ) :
    nBlk P (.node l τ height index) = 1 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (nodePayload _ _)).length / 136 + 1 = 1
  rw [length_addressedHashInput, length_nodePayload]

theorem nBlk_forsLeaf (P : PublicParameter) (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
    nBlk P (.forsLeaf idx κ s) = 1 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (littleEndianBytes 16 _)).length / 136 + 1 = 1
  rw [length_addressedHashInput, length_le16]

theorem nBlk_forsNode (P : PublicParameter) (idx : Index) (κ : ForsTreeIndex) (height node : ℕ) :
    nBlk P (.forsNode idx κ height node) = 1 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (nodePayload _ _)).length / 136 + 1 = 1
  rw [length_addressedHashInput, length_nodePayload]

theorem nBlk_forsRoots (P : PublicParameter) (idx : Index) : nBlk P (.forsRoots idx) = 4 := by
  rw [nBlk, length_blocks]
  show (addressedHashInput P _ (digestsPayload _)).length / 136 + 1 = 4
  rw [length_addressedHashInput, length_digestsPayload]
  simp [forsTreeCount]

/-- **The program calls of a FORS opening**: `804` (three per block of the `24` opened leaves and
`240` nodes, twelve for the `4`-block roots compression). -/
theorem sum_length_slotPorts_forsSlots_le (pub : Pub) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    ((forsSlots idx lv).map fun s ↦ (slotPorts pub s).length).sum ≤ 804 := by
  have hA : ∀ y ∈ ((List.finRange forsTreeCount).flatMap fun κ ↦ Slot.forsLeaf idx κ (lv κ) ::
      (List.range forsTreeHeight).map fun h ↦
        Slot.forsNode idx κ (h + 1) ((lv κ).val >>> (h + 1))).map
        (fun s ↦ (slotPorts pub s).length), y ≤ 3 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨κ, -, hs⟩ := List.mem_flatMap.1 hs
    rcases List.mem_cons.1 hs with rfl | hs
    · rw [length_slotPorts, nBlk_forsLeaf]
    · obtain ⟨h, -, rfl⟩ := List.mem_map.1 hs
      rw [length_slotPorts, nBlk_forsNode]
  have hlen : ((List.finRange forsTreeCount).flatMap fun κ ↦ Slot.forsLeaf idx κ (lv κ) ::
      (List.range forsTreeHeight).map fun h ↦
        Slot.forsNode idx κ (h + 1) ((lv κ).val >>> (h + 1))).length = 264 := by
    rw [List.length_flatMap]
    simp [forsTreeCount, forsTreeHeight]
    decide
  have h1 := List.sum_le_length_nsmul _ 3 hA
  rw [List.length_map, hlen, smul_eq_mul] at h1
  rw [forsSlots, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, length_slotPorts, nBlk_forsRoots]
  omega

/-- **The program calls of a layer signature**: at most `630` (three per block of the `192` chain
steps at most, the `8`-block leaf and at most `10` nodes). -/
theorem sum_length_slotPorts_layerSlots_le (pub : Pub) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (x : Encoding) :
    ((layerSlots l τ e x).map fun s ↦ (slotPorts pub s).length).sum ≤ 630 := by
  have hchain : ∀ y ∈ ((List.finRange chainCount).flatMap fun i ↦
      ((List.finRange (chainLength - 1)).filter fun step ↦ decide ((x i).val ≤ step.val)).map
        fun step ↦ Slot.chain l τ e i step).map (fun s ↦ (slotPorts pub s).length), y ≤ 3 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, -, hs⟩ := List.mem_flatMap.1 hs
    obtain ⟨step, -, rfl⟩ := List.mem_map.1 hs
    rw [length_slotPorts, nBlk_chain]
  have hlen : ((List.finRange chainCount).flatMap fun i ↦
      ((List.finRange (chainLength - 1)).filter fun step ↦ decide ((x i).val ≤ step.val)).map
        fun step ↦ Slot.chain l τ e i step).length ≤ 192 := by
    rw [List.length_flatMap]
    refine (List.sum_le_length_nsmul _ 3 fun y hy ↦ ?_).trans
      (by rw [List.length_map, List.length_finRange]; simp [chainCount])
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans
      (by rw [List.length_finRange]; simp [chainLength, winternitzBits])
  have hnode : ∀ y ∈ ((List.range (layerHeight l)).map fun lev ↦
      Slot.node l τ (lev + 1) (e.val >>> (lev + 1))).map (fun s ↦ (slotPorts pub s).length),
      y ≤ 3 := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
    obtain ⟨lev, -, rfl⟩ := List.mem_map.1 hs
    rw [length_slotPorts, nBlk_node]
  have h1 := List.sum_le_length_nsmul _ 3 hchain
  have h2 := List.sum_le_length_nsmul _ 3 hnode
  simp only [List.length_map, smul_eq_mul, List.length_range] at h1 h2
  rw [layerSlots, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
    length_slotPorts, nBlk_leaf]
  have hH := layerHeight_le l
  omega

/-! ### The signer -/

variable (upd : TrialUpd M)

/-- A counter trial's input is one block. -/
theorem length_blocks_trialInput (pub : Pub) (K : Key) (m : Digest) (cnt : ℕ) :
    (blocks (trialInput pub K m cnt)).length = 1 := by
  rw [length_blocks, trialInput, length_addressedHashInput]
  simp [littleEndianBytes, bigEndianBytes]

omit [Fintype M] [DecidableEq M] in
/-- **The counter search**: three reads per trial. -/
theorem chg_grindK (pub : Pub) (B : QReg) (K : Key) (m : Digest) :
    ∀ n cnt, IFreeM.IsChargeBound (grindK M upd pub B K m n cnt)
      (portCharge (rdCharge M a b)) (n * (3 * b))
  | 0, _ => trivial
  | n + 1, cnt => by
    have ht := chg_hashTrial a b (upd K) pub.perm B (trialInput pub K m cnt)
    rw [length_blocks_trialInput, Nat.mul_one] at ht
    rw [grindK]
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n * (3 * b)) ht
      fun out ↦ ?_) (le_of_eq (by ring))
    split
    · trivial
    · exact chg_grindK pub B K m n (cnt + 1)

/-- The calls of a FORS opening by kind: one reveal and at most `804` program calls. -/
def forsCalls (c d : ℕ) : ℕ :=
  d + c * 804

/-- The calls of one layer signature by kind: the reveal of the value it signs, the counter
search's reads, one reveal and at most `630` program calls. -/
def layerCalls (b c d : ℕ) : ℕ :=
  d + (encodingAttemptLimit * (3 * b) + (d + c * 630))

/-- The calls of one signature by kind: two reveals, the digest's `6` program calls, the FORS
opening and three layer signatures. -/
def signCalls (b c d : ℕ) : ℕ :=
  d + (d + (c * 6 + (forsCalls c d + 3 * layerCalls b c d)))

omit [Fintype M] [DecidableEq M] in
/-- **A FORS opening's calls.** -/
theorem chg_forsOpenT (pub : Pub) (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT M pub B idx lv) (portCharge (tCharge M a b c d))
      (forsCalls c d) := by
  unfold forsOpenT
  refine chg_revealThen a b c d _ _ fun _ ↦ ?_
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (chg_progSlots a b c d pub B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (sum_length_slotPorts_forsSlots_le pub idx lv)

omit [Fintype M] [DecidableEq M] in
/-- **A layer signature's calls.** -/
theorem chg_signLayerT (pub : Pub) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (signLayerT M upd pub B K) (portCharge (tCharge M a b c d))
      (layerCalls b c d) := by
  unfold signLayerT
  refine chg_revealThen a b c d _ _ fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (isChargeBound_readLift a b c d
    (chg_grindK a b upd pub B K _ _ _)) fun g ↦ ?_
  rcases g with _ | ⟨cnt, x⟩
  · trivial
  · refine chg_revealThen a b c d _ _ fun r ↦ ?_
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
      (chg_progSlots a b c d pub B _) fun _ ↦ trivial) ?_
    rw [Nat.add_zero]
    exact Nat.mul_le_mul_left c (sum_length_slotPorts_layerSlots_le pub K.1 K.2.1 K.2.2 x)

omit [Fintype M] [DecidableEq M] in
theorem chg_digestPorts (pub : Pub) (pol : DigestPolicy) (B : QReg) (T : Finset HPos)
    (msg : Message) :
    IFreeM.IsChargeBound (progPorts M B (digestPorts pub pol T msg))
      (portCharge (tCharge M a b c d)) (c * 6) := by
  have h := chg_progPorts (M := M) a b c d B (digestPorts pub pol T msg)
  rwa [length_digestPorts] at h

omit [Fintype M] [DecidableEq M] in
/-- **A signature's calls**, for every digest policy. -/
theorem chg_signT (pol : DigestPolicy) (pub : Pub) (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (signT M upd pol pub B msg) (portCharge (tCharge M a b c d))
      (signCalls b c d) := by
  have h : IFreeM.IsChargeBound (signT M upd pol pub B msg) (portCharge (tCharge M a b c d))
      (d + (d + (c * 6 + (forsCalls c d + (layerCalls b c d + (layerCalls b c d +
        (layerCalls b c d + 0))))))) := by
    unfold signT
    refine chg_revealThen a b c d _ _ fun r₁ ↦ chg_revealThen a b c d _ _ fun r₂ ↦ ?_
    refine FreeM₂.isChargeBound_bind (chg_digestPorts a b c d pub pol B _ msg) fun _ ↦ ?_
    refine FreeM₂.isChargeBound_bind (chg_forsOpenT a b c d pub B _ _) fun _ ↦ ?_
    refine FreeM₂.isChargeBound_bind (chg_signLayerT a b c d upd pub B _) fun s₀ ↦ ?_
    rcases s₀ with _ | bottom
    · trivial
    · refine FreeM₂.isChargeBound_bind (chg_signLayerT a b c d upd pub B _) fun s₁ ↦ ?_
      rcases s₁ with _ | middle
      · trivial
      · refine FreeM₂.isChargeBound_bind (chg_signLayerT a b c d upd pub B _) fun s₂ ↦ ?_
        rcases s₂ with _ | top <;> trivial
  exact h.mono (le_of_eq (by simp only [signCalls]; omega))

/-! ### The challenger and the game -/

/-- The source charge of the adversary's commands: `α` per permutation call, `β` per signing
request. -/
def advCharge (α β : ℕ) (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ℕ :=
  α * cmdCharge permCharge A cmd + β * cmdCharge signCharge A cmd

omit [Fintype M] [DecidableEq M] in
/-- **The challenger's calls** per command: a local operation none, a permutation call `6a` (the
simulation), a signing request the signature's calls `S`. -/
theorem chg_challengeT (pol : DigestPolicy) (pub : Pub) {S : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT M upd pol pub B msg)
      (portCharge (tCharge M a b c d)) S)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (challengeT M upd pol pub A cmd) (portCharge (tCharge M a b c d))
      (advCharge (6 * a) S A cmd) := by
  rcases cmd with o | ⟨p | msg, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift a b c d (isChargeBound_simulate a b
      _ (q := 0) ((QuantumComp.isTotalQueryBound_primBind_iff _ _ _).mpr fun _ ↦ trivial))) ?_
    simp [advCharge, cmdCharge]
  · refine IFreeM.IsChargeBound.mono (isChargeBound_readLift a b c d (isChargeBound_simulate a b
      _ (q := 1) ((QuantumComp.isTotalQueryBound_queryBind_iff _ _ _ _ _).mpr
        ⟨Nat.one_pos, fun _ ↦ trivial⟩))) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hS _ msg) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp only [advCharge, cmdCharge, permCharge, signCharge]
    omega

omit [Fintype M] [DecidableEq M] in
/-- **The game's calls, by components**, for every digest policy: the root's reveal, the
challenged adversary (`6a` per permutation call, `S` per signing request), and the
verification's reads (three per block of the verifier's `V` blocks). -/
theorem chg_gameT_of_signT (pol : DigestPolicy) (pub : Pub) (A : SAdversary) {q n S V : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n)
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT M upd pol pub B msg)
      (portCharge (tCharge M a b c d)) S)
    (hV : ∀ pk f, QueryCostAtMost (schemeWithHash.verify pk f) hashBlocks V) :
    IFreeM.IsChargeBound (gameT M upd pol pub A) (portCharge (tCharge M a b c d))
      (d + ((6 * a * q + S * n) + 3 * b * V)) := by
  refine chg_revealThen a b c d _ _ fun r₀ ↦ ?_
  have hx := IFreeM.IsChargeBound.add
    ((isChargeBound_withSignLog (hperm (pkOf pub r₀.1))).mul (6 * a))
    ((isChargeBound_withSignLog (hsign (pkOf pub r₀.1))).mul S)
  have hh : ∀ s (cmd : (QuantumComp.toIPFunctor LocalSig.instruments.{0} sAdvSpec).A s),
      IFreeM.IsChargeBound (challengeT M upd pol pub s cmd) (portCharge (tCharge M a b c d))
        (advCharge (6 * a) S s cmd) :=
    chg_challengeT a b c d upd pol pub hS
  have hc := IFreeM.IsChargeBound.substitute (challengeT M upd pol pub) hh hx
  refine FreeM₂.isChargeBound_bind hc fun run ↦ ?_
  have hv := chg_readsProgram (M := M) a b pub.perm (QReg.of Unit) (hV (pkOf pub r₀.1) run.1)
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (isChargeBound_readLift a b c d (chg_map _ Prod.fst hv)) fun _ ↦ trivial) (Nat.add_zero _).le

/-- The calls of the game by kind: the root's reveal, `6a` per permutation call, a signature's
calls per signing request, three reads per verification block. -/
def gameCalls (a b c d q : ℕ) : ℕ :=
  d + ((6 * a * q + signCalls b c d * signatureLimit) + 3 * b * verifyBlocks)

omit [Fintype M] [DecidableEq M] in
/-- **The realized game's calls by kind**, for an adversary making at most `q` permutation calls
and at most `signatureLimit` signing requests on every path, for every digest policy, public
datum and hidden values. -/
theorem chg_realizeT_gameT (pol : DigestPolicy) (A : SAdversary) {q : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
    (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A)) (portCharge (rCharge M a b c d))
      (gameCalls a b c d q) :=
  isChargeBound_realizeT a b c d v
    (chg_gameT_of_signT a b c d upd pol pub A hperm hsign (chg_signT a b c d upd pol pub)
      verify_hashBlocks)

end charges

/-! ## `hN` -/

section hN

/-- The read and record ports of runtime 2 with record ports: the ports of the read mass on which
the invariant holds. -/
def readRecPort (M : Type) : (recHwSpec X Z HPos M).Port → Bool
  | .inl (.inl (.inr _)) => true
  | .inr _ => true
  | _ => false

/-- **The classical calls of the game**: one reveal for the root; per signing request two
reveals, the digest's `6` program calls, the FORS opening's reveal and `804` program calls, and
per layer two reveals, `3 · 2^32` reads and `630` program calls; `3 · verifyBlocks` reads for
the verification. -/
def clsCalls : ℕ :=
  gameCalls 0 1 1 1 0

theorem clsCalls_eq :
    clsCalls = 1 + (9 * 2 ^ 32 + 2709) * signatureLimit + 3 * 903 := by
  simp only [clsCalls, gameCalls, signCalls, forsCalls, layerCalls, verifyBlocks_eq,
    encodingAttemptLimit]
  ring

/-- **The program calls of the game**: `2700` per signing request. -/
def progCalls : ℕ :=
  signCalls 0 1 0 * signatureLimit

theorem progCalls_eq : progCalls = 2700 * signatureLimit := by
  simp [progCalls, signCalls, forsCalls, layerCalls]

variable {M : Type} (upd : TrialUpd M) (pol : DigestPolicy)
  (A : SAdversary) {q : ℕ} (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hperm hsign

/-- **`hN` at the sponge ports**: at most `6q` sponge calls. -/
theorem hN_sponge (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A))
      (portCharge fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 0 else 1)
      (6 * q) := by
  have he : (fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 0 else 1) =
      rCharge M 1 0 0 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 1 0 0 0 upd pol A hperm hsign pub v)
    (le_of_eq (by simp [gameCalls, signCalls, forsCalls, layerCalls]))

/-- **`hN` at the classical ports** (reads, program and record calls): at most `clsCalls`. -/
theorem hN_cls (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A))
      (portCharge fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 1 else 0)
      clsCalls := by
  have he : (fun i ↦ if extCls X Z (Finset HPos × M) (recSpec HPos M) i then 1 else 0) =
      rCharge M 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 1 1 upd pol A hperm hsign pub v)
    (le_of_eq (by simp [clsCalls, gameCalls]))

/-- **`hN` at the read and record ports** (`readRecPort`, the ports of the read mass): at most
`clsCalls`. -/
theorem hN_readRec (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A))
      (portCharge fun i ↦ if readRecPort M i = true then 1 else 0) clsCalls := by
  have he : (fun i ↦ if readRecPort M i = true then 1 else 0) = rCharge M 0 1 0 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 0 1 upd pol A hperm hsign pub v) ?_
  have h : signCalls 1 0 1 ≤ signCalls 1 1 1 := by
    simp only [signCalls, forsCalls, layerCalls]
    omega
  have h' := Nat.mul_le_mul_right signatureLimit h
  simp only [clsCalls, gameCalls]
  omega

/-- **`hN` at the program ports**: at most `progCalls` program calls. -/
theorem hN_prog (pub : Pub) (v : (s : HPos) → XD s) :
    IFreeM.IsChargeBound (realizeT v (gameT M upd pol pub A))
      (portCharge (extProgCharge X Z (Finset HPos × M) (recSpec HPos M))) progCalls := by
  have he : extProgCharge X Z (Finset HPos × M) (recSpec HPos M) = rCharge M 0 0 1 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 0 1 0 upd pol A hperm hsign pub v)
    (le_of_eq ?_)
  simp [gameCalls, progCalls, signCalls, forsCalls, layerCalls]

end hN

end Quantum.Sphincs.Assembly

end
