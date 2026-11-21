module

public import Quantum.Qrom.Sphincs.GameT
public import Quantum.Xmss.Assembly.GameTCalls
public import Common.CostCombinators

@[expose] public section

/-!
# The calls of leanSPHINCS's realized runtime-2 template game in the QROM

Charge bounds on `gameT M upd pol A` (`Quantum.Qrom.Sphincs.Template`) for every digest policy
`pol`, inner memory `M` and trial update `upd`: `a` per call of the regrouped function (port `h`,
the adversary's hash calls), `b` per read, `c` per program call, `d` per reveal (`tChargeQ`;
realized, `rChargeQ`, where a reveal is a record call).

* **The verifier's hash calls** (`verify_hashCalls`): `sphincsRom.verify` calls `H` at most
  `verifyCalls = 879` times (`H_msg` twice, FORS `24 · 11 + 1`, each layer `1 + 64 · 3 + 1 + 10`).
* **Program calls** (`length_layerPos_le`, `length_forsPos_le`): a layer publication programs
  at most `203` positions (`192` chain steps, the leaf, `10` nodes), a FORS opening at most `265`.
* Per component: `chg_grindT` (one read per counter trial), `chg_selectT`, `chg_publishT`,
  `chg_forsOpenT`, `chg_publishAllT`, `chg_signT` (`signCallsQ`), `chg_challengeT` (`a` per hash
  call, `S` per signing request), composed in `chg_gameT_of_signT`, `chg_realizeT_gameT`
  (`gameCallsQ a b c d q`) and the prefix's `chg_realizeT_prefixT`.
* **Counts**, for an adversary with at most `q` hash calls and `signatureLimit` signing requests,
  every digest policy and hidden values: `advCalls_gameT` (at most `q` calls of `F`),
  `clsCalls_gameT` (at most `clsCapQ` classical calls: reads, program and record calls),
  `progCalls_gameT` (at most `progCapQ` program calls), `readRec_gameT` (at most `clsCapQ` reads
  and record calls), and the same for the prefix and the canonical `gameQ`, `prefixQ`.
-/

open Matrix IPFunctor OracleComp OracleSpec
open scoped ENNReal

universe u v w

open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Common
open Quantum.Sponge (hwReadSpec hwReadCmdSpec readCall keepMem portCharge
  isChargeBound_portCharge_queryBind_iff HwRead)
open Quantum.Sphincs (Key keyOf)
open Quantum.Xmss.Hybrid (LazyProg)
open Quantum.Xmss.Assembly (tmplSpec recHwSpec recSpec readLift readLiftQ readLens tmplLens
  realizeT revealThen progThen RevealVals extCls chg_act chg_map SChg sChg_mono sChg_bind
  sChg_pure)
open Quantum.Xmss (extProgCharge)
open Quantum.Qrom.SufCma (hashCharge signCharge cmdCharge isChargeBound_withSignLog)

/-! ## The verifier's hash calls -/

section verifyCost

attribute [local irreducible] HashSig.OverPermutation.sequenceFin
  HashSig.OverPermutation.walkChain HashSig.OverPermutation.foldPath

/-- One hash costs at most one call of `H`. -/
theorem hashQ_cost (input : HashInput) : QueryCostAtMost (hashQ input) hashCallCost 1 := by
  unfold hashQ
  split
  · exact isWeightBound_query _ _
  · exact isWeightBound_pure _ _ _

attribute [local irreducible] hashQ

theorem addressedHash_cost (seed : PublicParameter) (address : Address) (payload : HashInput) :
    QueryCostAtMost (LeanSphincsOver.addressedHash hashQ seed address payload) hashCallCost 1 := by
  unfold LeanSphincsOver.addressedHash
  exact ((hashQ_cost _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono le_rfl

theorem recoverChain_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) (digit : WinternitzDigit) (x : Digest) :
    QueryCostAtMost (LeanSphincsOver.recoverChain hashQ seed l τ e i digit x) hashCallCost 3 := by
  unfold LeanSphincsOver.recoverChain LeanSphincsOver.chainWalk
  refine (walkChain_cost _ 1 (fun _ _ ↦ addressedHash_cost _ _ _) _ _ x).mono ?_
  simp [chainLength, winternitzBits]

/-- The calls of a one-time leaf's recovery. -/
def otsLeafCalls : ℕ := 1 + (chainCount * 3 + 1)

theorem otsLeaf_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (msg : Digest) (counter : EncodingCounter) (values : ChainIndex → Digest) :
    QueryCostAtMost (LeanSphincsOver.otsLeaf hashQ seed l τ e msg counter values) hashCallCost
      otsLeafCalls := by
  unfold LeanSphincsOver.otsLeaf LeanSphincsOver.encode
  refine ((QueryCostAtMost.bind (addressedHash_cost _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).bind
    fun x ↦ ?_).mono (le_of_eq rfl)
  cases x with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ recoverChain_cost _ _ _ _ _ _ _)
      fun _ ↦ QueryCostAtMost.bind (addressedHash_cost _ _ _) fun _ ↦
        isWeightBound_pure _ _ 0).mono (by simp)

theorem treeFold_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (path : ℕ → Digest) (levels : ℕ) (x : Digest) :
    QueryCostAtMost (LeanSphincsOver.treeFold hashQ seed l τ e path levels x) hashCallCost
      (levels * 1) :=
  foldPath_cost _ 1 (fun _ _ _ _ ↦ addressedHash_cost _ _ _) _ _ levels x

/-- The calls of one FORS tree's recovery. -/
def forsTreeCalls : ℕ := 1 + forsTreeHeight * 1

theorem forsTreeRecover_cost (seed : PublicParameter) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) :
    QueryCostAtMost (LeanSphincsOver.forsTreeRecover hashQ seed idx κ leaf opening) hashCallCost
      forsTreeCalls := by
  unfold LeanSphincsOver.forsTreeRecover LeanSphincsOver.forsLeafHash
  exact (addressedHash_cost _ _ _).bind fun _ ↦
    foldPath_cost _ 1 (fun _ _ _ _ ↦ addressedHash_cost _ _ _) _ _ _ _

/-- The calls of the FORS key's recovery. -/
def forsRecoverCalls : ℕ := forsTreeCount * forsTreeCalls + 1

theorem forsRecover_cost (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    QueryCostAtMost (LeanSphincsOver.forsRecover hashQ seed idx leaves opening) hashCallCost
      forsRecoverCalls := by
  unfold LeanSphincsOver.forsRecover LeanSphincsOver.forsPublicKey
  exact (sequenceFin_cost _ _ fun _ ↦ forsTreeRecover_cost _ _ _ _ _).bind fun _ ↦
    addressedHash_cost _ _ _

theorem messageDigest_cost (pk : PublicKey) (R : Randomizer) (msg : Message) :
    QueryCostAtMost (LeanSphincsOver.messageDigest hashQ pk R msg) hashCallCost 2 := by
  unfold LeanSphincsOver.messageDigest LeanSphincsOver.messageDigestCall
  exact (QueryCostAtMost.bind (sequenceFin_cost 1 _ fun _ ↦ hashQ_cost _) fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [digestCallCount])

/-- The calls of one layer of the walk up the hypertree. -/
def layerCalls : ℕ := otsLeafCalls + 10 * 1

theorem verifyLayers_cost (seed : PublicParameter) (idx : Index) (sig : Signature) :
    ∀ n msg, QueryCostAtMost (LeanSphincsOver.verifyLayers hashQ seed idx sig n msg)
      hashCallCost (n * layerCalls)
  | 0, _ => by
    simp only [LeanSphincsOver.verifyLayers]
    exact isWeightBound_pure _ _ _
  | n + 1, msg => by
    simp only [LeanSphincsOver.verifyLayers]
    split
    · refine ((otsLeaf_cost _ _ _ _ _ _ _).bind fun x ↦ ?_).mono
        (Q := otsLeafCalls + (10 * 1 + n * layerCalls)) (by
          have := Nat.add_one_mul n layerCalls; unfold layerCalls at *; omega)
      cases x with
      | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
      | some _ =>
        refine ((treeFold_cost _ _ _ _ _ _ _).bind fun _ ↦ ?_).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Quantum.Sphincs.layerHeight_le _)) _)
        split
        · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
        · exact verifyLayers_cost seed idx sig n _
    · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

/-- **The verifier's hash calls.** -/
def verifyCalls : ℕ := 2 + (forsRecoverCalls + layerCount * layerCalls)

theorem verifyCalls_eq : verifyCalls = 879 := by
  simp [verifyCalls, forsRecoverCalls, forsTreeCalls, layerCalls, otsLeafCalls, chainCount,
    forsTreeCount, forsTreeHeight, layerCount]

/-- **The verifier calls `H` at most `verifyCalls` times.** -/
theorem verify_hashCalls (pk : PublicKey) (f : Forgery) :
    QueryCostAtMost (sphincsRom.verify pk f) hashCallCost verifyCalls := by
  show QueryCostAtMost (LeanSphincsOver.verify hashQ pk f.message f.signature) _ _
  unfold LeanSphincsOver.verify
  refine (messageDigest_cost _ _ _).bind fun _ ↦ (forsRecover_cost _ _ _ _).bind fun _ ↦ ?_
  refine ((verifyLayers_cost _ _ _ _ _).bind fun r ↦ ?_).mono
    (Q := layerCount * layerCalls + 0) (by simp)
  cases r <;> exact isWeightBound_pure _ _ _

end verifyCost

attribute [local irreducible] sphincsRom

/-! ## Charges by kind -/

section charges

variable {M : Type} [Fintype M] [DecidableEq M] {L : LocalSig.{u, v}} {Ω : QReg → Type w}

variable (M) in
/-- A charge on the template ports by kind: `a` per call of `F`, `b` per read, `c` per program
call, `d` per reveal. -/
def tChargeQ (a b c d : ℕ) : (SSpecQ M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The same charge on runtime 2 with record ports (a reveal realizes as a record call). -/
def rChargeQ (a b c d : ℕ) : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → ℕ
  | .inl (.inl (.inl _)) => a
  | .inl (.inl (.inr _)) => b
  | .inl (.inr _) => c
  | .inr _ => d

variable (M) in
/-- The charge on runtime 1's ports: `a` per call of `F`, `b` per read. -/
def rdChargeQ (a b : ℕ) : (hwReadSpec PairOut Qrom.HashDomain M).Port → ℕ
  | .inl _ => a
  | .inr _ => b

variable (a b c d : ℕ)

omit [Fintype M] [DecidableEq M] in
/-- **Realizing keeps the charges by kind.** -/
theorem isChargeBound_realizeT (θ : TVals) {A : QReg} {y : QuantumComp L (SSpecQ M) Ω A}
    {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (tChargeQ M a b c d)) n) :
    IFreeM.IsChargeBound (realizeT θ y) (portCharge (rChargeQ M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (tmplLens θ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (rChargeQ M a b c d) s
      ((tmplLens θ).toFunA s cmd)) = portCharge (tChargeQ M a b c d) := by
    funext s cmd
    rcases cmd with o | ⟨((i | c) | p) | T, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem isChargeBound_readLift {A : QReg} {y : QuantumComp L (hwReadSpec PairOut Qrom.HashDomain M)
    Ω A} {n : ℕ} (h : IFreeM.IsChargeBound y (portCharge (rdChargeQ M a b)) n) :
    IFreeM.IsChargeBound (readLift goodQ y) (portCharge (tChargeQ M a b c d)) n := by
  refine IFreeM.IsChargeBound.mapLens (readLens goodQ) ?_
  have he : (fun s cmd ↦ portCharge (L := L) (tChargeQ M a b c d) s
      ((readLens goodQ).toFunA s cmd)) = portCharge (rdChargeQ M a b) := by
    funext s cmd
    rcases cmd with o | ⟨i | c, E, ℓ⟩ <;> rfl
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
theorem chg_revealThen {B B' : QReg} {α : Type} (T : Finset TPos)
    (k : RevealVals TVal T × (Finset TPos × M) → QComp (SSpecQ M) B B' α) {n : ℕ}
    (hk : ∀ r, IFreeM.IsChargeBound (k r) (portCharge (tChargeQ M a b c d)) n) :
    IFreeM.IsChargeBound (revealThen goodQ T k) (portCharge (tChargeQ M a b c d)) (d + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right d n, fun r ↦ ?_⟩
  simp only [tChargeQ, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk r) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progThen {B B' : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    (hp : goodQ p) (k : QComp (SSpecQ M) B B' α) {n : ℕ}
    (hk : IFreeM.IsChargeBound k (portCharge (tChargeQ M a b c d)) n) :
    IFreeM.IsChargeBound (progThen p hp k) (portCharge (tChargeQ M a b c d)) (c + n) := by
  refine (isChargeBound_portCharge_queryBind_iff _ _ _ _ _ _).mpr ⟨Nat.le_add_right c n, fun r ↦ ?_⟩
  simp only [tChargeQ, Nat.add_sub_cancel_left]
  exact IFreeM.IsChargeBound.mono
    (FreeM₂.isChargeBound_bind (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hk) (Nat.zero_add n).le

omit [Fintype M] [DecidableEq M] in
theorem chg_progPos (B : QReg) (ps : List Pos) :
    IFreeM.IsChargeBound (progPos M B ps) (portCharge (tChargeQ M a b c d)) (c * ps.length) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    refine IFreeM.IsChargeBound.mono (chg_progThen a b c d (progT p) trivial _ ih) (le_of_eq ?_)
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm]

omit [Fintype M] [DecidableEq M] in
theorem chg_readCallQ (c : HwRead PairOut Qrom.HashDomain M) (B : QReg) :
    IFreeM.IsChargeBound (readCall c B) (portCharge (rdChargeQ M a b)) b := by
  unfold readCall
  exact FreeM₂.isChargeBound_bind (n₂ := 0)
    ((IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨le_rfl, fun _ ↦ trivial⟩) fun _ ↦
      FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0) (chg_act _ _ 0) fun _ ↦ trivial

/-! ### Read programs -/

omit [Fintype M] [DecidableEq M] in
theorem sChg_romReadImpl (B : QReg) (t : RomOracles.Domain) :
    SChg (rdChargeQ M a b) (romReadImpl M B t) (b * hashCallCost t) := by
  rcases t with n | x
  · intro s
    show IFreeM.IsChargeBound ((QComp.coinImpl (hwReadSpec PairOut Qrom.HashDomain M) B n).bind
      fun r ↦ QuantumComp₂.pure (r, s)) _ _
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₁ := 0) (n₂ := 0)
      (chg_act _ _ 0) fun _ ↦ trivial) (Nat.zero_le _)
  · intro log
    show IFreeM.IsChargeBound ((readCall (.readH (hmsgRoute (x, false)).1 keepMem) B).bind fun r ↦
      QuantumComp₂.pure (pairPart (hmsgRoute (x, false)).2 (r.1.getD 0), log ++ [x])) _ _
    exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0) (chg_readCallQ a b _ B)
      fun _ ↦ trivial) (by simp [hashCallCost])

omit [Fintype M] [DecidableEq M] in
theorem sChg_simulateQ_romReadImpl (B : QReg) {α : Type} (x : OracleComp RomOracles α) {n : ℕ}
    (h : QueryCostAtMost x hashCallCost n) :
    SChg (rdChargeQ M a b) (simulateQ (romReadImpl M B) x) (b * n) := by
  induction x using OracleComp.inductionOn generalizing n with
  | pure x => rw [simulateQ_pure]; exact sChg_pure _ x _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    refine sChg_mono _ (sChg_bind _ (sChg_romReadImpl a b B t) fun u ↦ ih u (h.2 u)) ?_
    rw [← Nat.mul_add, Nat.add_sub_cancel' h.1]

omit [Fintype M] [DecidableEq M] in
/-- **A computation through read ports**: one read per call of `H` of a path bound. -/
theorem chg_readsProgram (B : QReg) {α : Type} {x : OracleComp RomOracles α} {n : ℕ}
    (h : QueryCostAtMost x hashCallCost n) :
    IFreeM.IsChargeBound (readsProgram M B x) (portCharge (rdChargeQ M a b)) (b * n) :=
  sChg_simulateQ_romReadImpl a b B x h []

/-! ### The positions a signature programs -/

theorem length_mkPos_le (q : RawPos) : (mkPos q).length ≤ 1 := by
  unfold mkPos
  split_ifs <;> simp

theorem length_nodePos_le (l : Layer) (τ : TreeIndex) (level index : ℕ) :
    (nodePos l τ level index).length ≤ 1 := by
  unfold nodePos
  split_ifs
  · exact length_mkPos_le _
  · simp

theorem length_forsNodePos_le (idx : Index) (κ : ForsTreeIndex) (height j : ℕ) :
    (forsNodePos idx κ height j).length ≤ 1 := by
  unfold forsNodePos
  split_ifs
  · exact length_mkPos_le _
  · simp

theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) {k : ℕ}
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun b hb ↦ h b (List.mem_cons_of_mem a hb)
    omega

/-- **A layer publication programs at most `203` positions**: `192` chain steps, the leaf and at
most `10` nodes. -/
theorem length_layerPos_le (K : Key) (x : Encoding) : (layerPos K x).length ≤ 203 := by
  have h1 : ((List.finRange chainCount).flatMap fun i ↦ ((List.finRange (chainLength - 1)).filter
      fun step ↦ decide ((x i).val ≤ step.val)).flatMap fun step ↦
        mkPos (.chain K.1 K.2.1 K.2.2 i step)).length ≤ chainCount * 3 := by
    refine (length_flatMap_le _ _ fun i _ ↦ ?_).trans (le_of_eq (by rw [List.length_finRange]))
    refine (length_flatMap_le _ _ fun _ _ ↦ length_mkPos_le _).trans ?_
    rw [Nat.mul_one]
    exact (List.length_filter_le _ _).trans (by rw [List.length_finRange]; decide)
  have h2 := length_mkPos_le (.leaf K.1 K.2.1 K.2.2)
  have h3 : ((List.range (layerHeight K.1)).flatMap fun lev ↦
      nodePos K.1 K.2.1 lev (K.2.2.val >>> (lev + 1))).length ≤ 10 := by
    refine (length_flatMap_le _ _ fun _ _ ↦ length_nodePos_le _ _ _ _).trans ?_
    rw [List.length_range, Nat.mul_one]
    exact Quantum.Sphincs.layerHeight_le _
  unfold layerPos
  rw [List.length_append, List.length_append]
  have h4 : chainCount = 64 := rfl
  omega

/-- **A FORS opening programs at most `265` positions**: `24` leaves, `240` nodes and the roots
compression. -/
theorem length_forsPos_le (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    (forsPos idx lv).length ≤ 265 := by
  have h1 : ((List.finRange forsTreeCount).flatMap fun κ ↦ mkPos (.forsLeaf idx κ (lv κ)) ++
      (List.range forsTreeHeight).flatMap fun h ↦
        forsNodePos idx κ h ((lv κ).val >>> (h + 1))).length ≤ forsTreeCount * 11 := by
    refine (length_flatMap_le _ _ fun κ _ ↦ ?_).trans (by rw [List.length_finRange])
    rw [List.length_append]
    have := length_mkPos_le (.forsLeaf idx κ (lv κ))
    have := length_flatMap_le (List.range forsTreeHeight)
      (fun h ↦ forsNodePos idx κ h ((lv κ).val >>> (h + 1))) fun _ _ ↦
        length_forsNodePos_le _ _ _ _
    rw [List.length_range] at this
    have : forsTreeHeight = 10 := rfl
    omega
  have h2 := length_mkPos_le (.forsRoots idx)
  unfold forsPos
  rw [List.length_append]
  have h4 : forsTreeCount = 24 := rfl
  omega

/-! ### The signer -/

variable (upd : TrialUpd M)

omit [Fintype M] [DecidableEq M] in
/-- **The counter search**: one read per trial. -/
theorem chg_grindT (seed : PublicParameter) (B : QReg) (K : Key) (m : Digest) :
    ∀ n cnt, IFreeM.IsChargeBound (grindT M upd seed B K m n cnt)
      (portCharge (rdChargeQ M a b)) (n * b)
  | 0, _ => trivial
  | n + 1, cnt => by
    rw [grindT]
    refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := n * b)
      (chg_readCallQ a b _ B) fun r ↦ ?_) (le_of_eq (by ring))
    generalize TargetSum.decodeDigest (truncateHash (r.1.getD 0).1) = dd
    cases dd with
    | none => exact chg_grindT seed B K m n (cnt + 1)
    | some x => trivial

/-- The calls of a counter search by kind: the reveal of the value the key signs and one read per
trial. -/
def selCallsQ (b d : ℕ) : ℕ :=
  d + encodingAttemptLimit * b

/-- The calls of a publication by kind: per layer one reveal and at most `203` program calls, the
FORS opening one reveal and at most `265` program calls. -/
def pubCallsQ (c d : ℕ) : ℕ :=
  (d + c * 265) + ((d + c * 203) + ((d + c * 203) + ((d + c * 203) + 0)))

/-- The calls of one signature by kind: three reveals, the digest's program call, three counter
searches and the publication. -/
def signCallsQ (b c d : ℕ) : ℕ :=
  d + (d + (c + (selCallsQ b d + (selCallsQ b d + (selCallsQ b d + pubCallsQ c d)))))

omit [Fintype M] [DecidableEq M] in
theorem chg_selectT (seed : PublicParameter) (B : QReg) (K : Key) :
    IFreeM.IsChargeBound (selectT M upd seed B K) (portCharge (tChargeQ M a b c d))
      (selCallsQ b d) := by
  unfold selectT
  refine chg_revealThen a b c d _ _ fun _ ↦ isChargeBound_readLift a b c d ?_
  exact chg_grindT a b upd seed B K _ _ _

omit [Fintype M] [DecidableEq M] in
theorem chg_publishT (B : QReg) (K : Key) (cnt : EncodingCounter) (x : Encoding) :
    IFreeM.IsChargeBound (publishT M B K cnt x) (portCharge (tChargeQ M a b c d))
      (d + c * 203) := by
  unfold publishT
  refine chg_revealThen a b c d _ _ fun _ ↦ ?_
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (chg_progPos a b c d B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_layerPos_le K x)

omit [Fintype M] [DecidableEq M] in
theorem chg_forsOpenT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    IFreeM.IsChargeBound (forsOpenT M B idx lv) (portCharge (tChargeQ M a b c d))
      (d + c * 265) := by
  unfold forsOpenT
  refine chg_revealThen a b c d _ _ fun _ ↦ ?_
  refine IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (chg_progPos a b c d B _) fun _ ↦ trivial) ?_
  rw [Nat.add_zero]
  exact Nat.mul_le_mul_left c (length_forsPos_le idx lv)

omit [Fintype M] [DecidableEq M] in
theorem chg_publishAllT (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) :
    IFreeM.IsChargeBound (publishAllT M B idx lv R g₀ g₁ g₂) (portCharge (tChargeQ M a b c d))
      (pubCallsQ c d) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try trivial
  simp only [publishAllT]
  refine FreeM₂.isChargeBound_bind (chg_forsOpenT a b c d B _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (chg_publishT a b c d B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (chg_publishT a b c d B _ _ _) fun _ ↦ ?_
  refine FreeM₂.isChargeBound_bind (n₂ := 0) (chg_publishT a b c d B _ _ _) fun _ ↦ ?_
  trivial

omit [Fintype M] [DecidableEq M] in
/-- **A signature's calls**, for every digest policy. -/
theorem chg_signT (pol : DigestPolicy) (B : QReg) (msg : Message) :
    IFreeM.IsChargeBound (signT M upd pol B msg) (portCharge (tChargeQ M a b c d))
      (signCallsQ b c d) := by
  unfold signT
  refine chg_revealThen a b c d _ _ fun r₁ ↦ chg_revealThen a b c d _ _ fun r₂ ↦ ?_
  refine chg_progThen a b c d _ trivial _ ?_
  exact FreeM₂.isChargeBound_bind (chg_selectT a b c d upd _ B _) fun _ ↦
    FreeM₂.isChargeBound_bind (chg_selectT a b c d upd _ B _) fun _ ↦
      FreeM₂.isChargeBound_bind (chg_selectT a b c d upd _ B _) fun _ ↦
        chg_publishAllT a b c d B _ _ _ _ _ _

/-! ### The challenger and the game -/

/-- The source charge of the adversary's commands: `α` per hash call, `β` per signing request. -/
def advChargeQ (α β : ℕ) (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ℕ :=
  α * cmdCharge hashCharge A cmd + β * cmdCharge signCharge A cmd

omit [Fintype M] [DecidableEq M] in
/-- A hash call of the adversary, regrouped and lifted, is one call of `F`. -/
theorem chg_hashCmd (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A)
    {n : ℕ} (hq : QuantumComp.IsQueryBound (SufCma.challenge sphincsRom noKey A cmd) fun _ ↦ n) :
    IFreeM.IsChargeBound (readLift goodQ ((liftH (regroupCalls hmsgRoute
      (SufCma.challenge sphincsRom noKey A cmd))).liftOrdinary
        (t := hwReadCmdSpec PairOut Qrom.HashDomain M))) (portCharge (tChargeQ M a b c d))
      (a * n) := by
  refine isChargeBound_readLift a b c d (isChargeBound_liftOrdinary (rdChargeQ M a b) ?_)
  refine (isChargeBound_liftH_iff _ _ _).mpr ?_
  have h := ((isQueryBound_regroupCalls hmsgRoute hq) ()).mul a
  have he : (portCharge fun _ ↦ (fun i ↦ rdChargeQ M a b (.inl i)) Quantum.Sponge.SpongePort.h) =
      fun s cmd ↦ a * QuantumComp.queryCharge (L := LocalSig.instruments.{0})
        (spec := qromSpec Qrom.HashDomain PairOut) () s cmd := by
    funext s cmd
    rcases cmd with o | ⟨i, E, ℓ⟩
    · simp [QuantumComp.queryCharge, portCharge]
    · simp [QuantumComp.queryCharge, portCharge, rdChargeQ]
  rw [he]
  exact h

omit [Fintype M] [DecidableEq M] in
/-- **The challenger's calls** per command: a local operation none, a hash call `a`, a signing
request the signature's calls `S`. -/
theorem chg_challengeT (pol : DigestPolicy) {S : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT M upd pol B msg)
      (portCharge (tChargeQ M a b c d)) S)
    (A : QReg) (cmd : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    IFreeM.IsChargeBound (challengeT M upd pol A cmd) (portCharge (tChargeQ M a b c d))
      (advChargeQ a S A cmd) := by
  rcases cmd with o | ⟨_ | msg, E, ℓ⟩
  · refine IFreeM.IsChargeBound.mono (chg_hashCmd a b c d A (.prim o) (n := 0) fun _ ↦
      (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨by simp [QuantumComp.queryCharge],
        fun _ ↦ trivial⟩) ?_
    simp [advChargeQ, cmdCharge]
  · refine IFreeM.IsChargeBound.mono (chg_hashCmd a b c d A (.query .hash E ℓ) (n := 1) fun _ ↦
      (IFreeM.isChargeBound_liftBind_iff _ _ _).mpr ⟨by simp [QuantumComp.queryCharge],
        fun _ ↦ trivial⟩) ?_
    simp [advChargeQ, cmdCharge, hashCharge, signCharge]
  · refine IFreeM.IsChargeBound.mono (IFreeM.isChargeBound_bind (FreeM₂.isChargeBound_bind
      (n₁ := 0) (chg_act _ _ 0) fun _ ↦ hS _ msg) fun _ _ ↦ IFreeM.isChargeBound_pure _ 0) ?_
    simp [advChargeQ, cmdCharge, hashCharge, signCharge]

omit [Fintype M] [DecidableEq M] in
/-- The challenged adversary's calls: `a` per hash call, `S` per signing request. -/
theorem chg_challengedT (pol : DigestPolicy) {S q n : ℕ}
    (hS : ∀ B msg, IFreeM.IsChargeBound (signT M upd pol B msg)
      (portCharge (tChargeQ M a b c d)) S)
    {x : QComp sAdvSpec (QReg.of Unit) (QReg.of Unit)
      (Forgery × SufCma.SignLog Message (Option Signature))}
    (hhash : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hsign : IFreeM.IsChargeBound x (cmdCharge signCharge) n) :
    IFreeM.IsChargeBound (challengedT M upd pol x) (portCharge (tChargeQ M a b c d))
      (a * q + S * n) :=
  IFreeM.IsChargeBound.substitute (challengeT M upd pol) (chg_challengeT a b c d upd pol hS)
    (IFreeM.IsChargeBound.add (hhash.mul a) (hsign.mul S))

omit [Fintype M] [DecidableEq M] in
/-- The verification's calls: one read per call of `H`. -/
theorem chg_verifyT (x : PublicKey × (Forgery × SufCma.SignLog Message (Option Signature))) :
    IFreeM.IsChargeBound (verifyT M x) (portCharge (tChargeQ M a b c d)) (b * verifyCalls) := by
  unfold verifyT
  rw [readsThenT_eq]
  exact IFreeM.IsChargeBound.mono (FreeM₂.isChargeBound_bind (n₂ := 0)
    (isChargeBound_readLift a b c d (chg_map _ Prod.fst
      (chg_readsProgram a b (QReg.of Unit) (verify_hashCalls x.1 x.2.1)))) fun _ ↦ trivial)
    (Nat.add_zero _).le

/-- The calls of the game by kind: the public key's reveal, `a` per hash call, a signature's
calls per signing request, one read per verifier's call of `H`. -/
def gameCallsQ (a b c d q : ℕ) : ℕ :=
  d + ((a * q + signCallsQ b c d * signatureLimit) + b * verifyCalls)

/-- The calls of the challenge prefix by kind. -/
def prefixCallsQ (a b c d q : ℕ) : ℕ :=
  d + ((a * q + signCallsQ b c d * signatureLimit) + 0)

variable {q : ℕ} (pol : DigestPolicy) (A : SAdversary)
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)

include hhash hsign

omit [Fintype M] [DecidableEq M] in
/-- **The game's calls by kind**, for every digest policy. -/
theorem chg_gameT :
    IFreeM.IsChargeBound (gameT M upd pol A) (portCharge (tChargeQ M a b c d))
      (gameCallsQ a b c d q) := by
  unfold gameT
  refine chg_revealThen a b c d _ _ fun r₀ ↦ ?_
  exact FreeM₂.isChargeBound_bind (chg_challengedT a b c d upd pol (chg_signT a b c d upd pol)
    (isChargeBound_withSignLog (hhash _)) (isChargeBound_withSignLog (hsign _))) fun run ↦
      chg_verifyT a b c d _

omit [Fintype M] [DecidableEq M] in
/-- **The prefix's calls by kind.** -/
theorem chg_prefixT :
    IFreeM.IsChargeBound (prefixT M upd pol A) (portCharge (tChargeQ M a b c d))
      (prefixCallsQ a b c d q) := by
  unfold prefixT
  refine chg_revealThen a b c d _ _ fun r₀ ↦ ?_
  exact FreeM₂.isChargeBound_bind (chg_challengedT a b c d upd pol (chg_signT a b c d upd pol)
    (isChargeBound_withSignLog (hhash _)) (isChargeBound_withSignLog (hsign _))) fun _ ↦ trivial

omit [Fintype M] [DecidableEq M] in
/-- **The realized game's calls by kind**, for every digest policy and hidden values. -/
theorem chg_realizeT_gameT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd pol A)) (portCharge (rChargeQ M a b c d))
      (gameCallsQ a b c d q) :=
  isChargeBound_realizeT a b c d θ (chg_gameT a b c d upd pol A hhash hsign)

omit [Fintype M] [DecidableEq M] in
/-- **The realized prefix's calls by kind.** -/
theorem chg_realizeT_prefixT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd pol A)) (portCharge (rChargeQ M a b c d))
      (prefixCallsQ a b c d q) :=
  isChargeBound_realizeT a b c d θ (chg_prefixT a b c d upd pol A hhash hsign)

end charges

/-! ## Counts -/

section counts

/-- **The classical calls of the game**: one reveal for the public key; per signing request three
reveals, the digest's program call, three counter searches (a reveal and `2^32` reads each) and
the publication (four reveals and at most `874` program calls); `verifyCalls` reads. -/
def clsCapQ : ℕ :=
  gameCallsQ 0 1 1 1 0

theorem clsCapQ_eq : clsCapQ = 1 + (3 * 2 ^ 32 + 884) * signatureLimit + 879 := by
  simp only [clsCapQ, gameCallsQ, signCallsQ, selCallsQ, pubCallsQ, verifyCalls_eq,
    encodingAttemptLimit]
  ring

/-- **The program calls of the game**: `875` per signing request. -/
def progCapQ : ℕ :=
  signCallsQ 0 1 0 * signatureLimit

theorem progCapQ_eq : progCapQ = 875 * signatureLimit := by
  simp [progCapQ, signCallsQ, selCallsQ, pubCallsQ]

/-- The adversary's ports of runtime 2 with record ports (`extCls` false): the calls of `F`. -/
theorem advCharge_eq (M : Type) :
    (fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 0 else 1) =
      rChargeQ M 1 0 0 0 := by
  funext i
  rcases i with ((i | c) | c) | T <;> rfl

variable {M : Type} [Fintype M] [DecidableEq M] (upd : TrialUpd M) (pol : DigestPolicy)
  (A : SAdversary) {q : ℕ} (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hhash hsign

omit [Fintype M] [DecidableEq M] in
/-- **At most `q` calls of `F`** in the realized game. -/
theorem advCalls_gameT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd pol A))
      (portCharge fun i ↦
        if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 0 else 1)
      q := by
  rw [advCharge_eq M]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 1 0 0 0 upd pol A hhash hsign θ)
    (le_of_eq (by simp [gameCallsQ, signCallsQ, selCallsQ, pubCallsQ]))

omit [Fintype M] [DecidableEq M] in
/-- **At most `clsCapQ` classical calls** (reads, program and record calls) in the realized game. -/
theorem clsCalls_gameT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd pol A))
      (portCharge fun i ↦
        if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 1 else 0)
      clsCapQ := by
  have he : (fun i ↦
      if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 1 else 0) =
      rChargeQ M 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 1 1 upd pol A hhash hsign θ)
    (le_of_eq (by simp [clsCapQ, gameCallsQ]))

omit [Fintype M] [DecidableEq M] in
/-- **At most `progCapQ` program calls** in the realized game. -/
theorem progCalls_gameT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd pol A))
      (portCharge (extProgCharge PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M)))
      progCapQ := by
  have he : extProgCharge PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) =
      rChargeQ M 0 0 1 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 0 1 0 upd pol A hhash hsign θ)
    (le_of_eq (by simp [gameCallsQ, progCapQ, signCallsQ, selCallsQ, pubCallsQ]))

/-- The read and record ports of runtime 2 with record ports. -/
def readRecPortQ (M : Type) : (recHwSpec PairOut Qrom.HashDomain TPos M).Port → Bool
  | .inl (.inl (.inr _)) => true
  | .inr _ => true
  | _ => false

omit [Fintype M] [DecidableEq M] in
/-- **At most `clsCapQ` reads and record calls** in the realized game. -/
theorem readRec_gameT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (gameT M upd pol A))
      (portCharge fun i ↦ if readRecPortQ M i = true then 1 else 0) clsCapQ := by
  have he : (fun i ↦ if readRecPortQ M i = true then 1 else 0) = rChargeQ M 0 1 0 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_gameT 0 1 0 1 upd pol A hhash hsign θ) ?_
  have h : signCallsQ 1 0 1 ≤ signCallsQ 1 1 1 := by
    simp only [signCallsQ, selCallsQ, pubCallsQ]
    omega
  have h' := Nat.mul_le_mul_right signatureLimit h
  simp only [clsCapQ, gameCallsQ]
  omega

omit [Fintype M] [DecidableEq M] in
/-- **At most `q` calls of `F`** in the realized prefix. -/
theorem advCalls_prefixT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd pol A))
      (portCharge fun i ↦
        if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 0 else 1)
      q := by
  rw [advCharge_eq M]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 1 0 0 0 upd pol A hhash hsign θ)
    (le_of_eq (by simp [prefixCallsQ, signCallsQ, selCallsQ, pubCallsQ]))

omit [Fintype M] [DecidableEq M] in
/-- **At most `progCapQ` program calls** in the realized prefix. -/
theorem progCalls_prefixT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd pol A))
      (portCharge (extProgCharge PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M)))
      progCapQ := by
  have he : extProgCharge PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) =
      rChargeQ M 0 0 1 0 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  exact IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 0 0 1 0 upd pol A hhash hsign θ)
    (le_of_eq (by simp [prefixCallsQ, progCapQ, signCallsQ, selCallsQ, pubCallsQ]))

omit [Fintype M] [DecidableEq M] in
/-- **At most `clsCapQ` classical calls** in the realized prefix. -/
theorem clsCalls_prefixT (θ : TVals) :
    IFreeM.IsChargeBound (realizeT θ (prefixT M upd pol A))
      (portCharge fun i ↦
        if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 1 else 0)
      clsCapQ := by
  have he : (fun i ↦
      if extCls PairOut Qrom.HashDomain (Finset TPos × M) (recSpec TPos M) i then 1 else 0) =
      rChargeQ M 0 1 1 1 := by
    funext i
    rcases i with ((i | c) | c) | T <;> rfl
  rw [he]
  refine IFreeM.IsChargeBound.mono (chg_realizeT_prefixT 0 1 1 1 upd pol A hhash hsign θ) ?_
  simp only [clsCapQ, gameCallsQ, prefixCallsQ]
  omega

end counts

/-! ## The canonical game -/

section canonical

variable (pol : DigestPolicy) (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) signatureLimit)
include hhash hsign

theorem advCalls_gameQ (θ : TVals) :
    IFreeM.IsChargeBound (gameQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 0 else 1) q :=
  advCalls_gameT cwUpd pol A hhash hsign θ

theorem clsCalls_gameQ (θ : TVals) :
    IFreeM.IsChargeBound (gameQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 1 else 0) clsCapQ :=
  clsCalls_gameT cwUpd pol A hhash hsign θ

theorem progCalls_gameQ (θ : TVals) :
    IFreeM.IsChargeBound (gameQ pol A θ)
      (portCharge (extProgCharge PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem))) progCapQ :=
  progCalls_gameT cwUpd pol A hhash hsign θ

theorem advCalls_prefixQ (θ : TVals) :
    IFreeM.IsChargeBound (prefixQ pol A θ)
      (portCharge fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
        (recSpec TPos SelMem) i then 0 else 1) q :=
  advCalls_prefixT cwUpd pol A hhash hsign θ

end canonical

end Quantum.Qrom.Sphincs

end
