module

public import Quantum.Qrom.Xmss.GameReads
public import Quantum.Qrom.Xmss.Multi.NoReuse

@[expose] public section

/-!
# The top-layer memo of the multi-user challenger, in the QROM

leanXMSS's signer re-runs the top key's signature of the bottom tree's root at every signature
below that top key. The memo challenger `muMemoFrom` keeps, per user and top key, the top layer's
signature once computed (`TopMemo`), and at a later request below the same top key computes only
the bottom layer (`signHit`) and reuses the memo. A request whose bottom layer fails records
nothing, as the statement's signer computes nothing for the top layer then (`signRecord`).

The memo is exact against every fixed function `H`: the signer hashes only (`isHash_sign`, no
coins), so against `H` it is a function of the secret key and the request, and the top layer's
signature is a function of the secret key and the top key (`topFull`). A classical algorithm run
by classical calls against `additiveOracleRuntime H` acts as the identity on the held register
and returns its value (`obsWeight_run_toQuantumAt_bind`).

* `topKeyOf r`, `assembleSig`, `topPart`, `topFull`: the top key of a request, a signature from its
  layers, and the top layer's signature from the scheme seed and from the secret key.
* `signHit sk r top`, `signRecord sk r`: the signer with a memoized top layer, and the signer that
  also reports its top layer.
* `TopMemo n`, `TopMemo.record`, `MemoOK H sks M`: the memo, its update, and its agreement with
  the top layers against `H`.
* `answerTree oa r E ℓ`: the answer program of a classical algorithm at a signing request, as
  `signTree` (`signTree_eq_answerTree`).
* `muMemoFrom sks M x`, `muGameMemo`, `muWinProbMemo`: the memo challenger from the memo `M`, and
  the multi-user game and winning probability with it.

## Main statements

* `obsWeight_muMemoFrom_eq`: against every `H`, a memo that agrees with `H` gives the challenged
  program's weights.
* `muWinProb_eq_muWinProbMemo`: the multi-user winning probability is the memo game's.
* `isTotalQueryBound_muMemoFrom`: the memo challenger's calls, `q + sc * total` when the memo
  signers make at most `sc` calls.
-/

open IPFunctor OracleComp OracleSpec
open scoped ENNReal

namespace Quantum.Qrom.Xmss.Multi

open LeanXmss HashSig HashSig.OverPermutation
open Quantum.Xmss (obsWeight obsWeight_run_bind obsWeight_run_bind₂)
open Quantum.SufCma (QueriesSatisfy queriesSatisfy_pure queriesSatisfy_bind
  queriesSatisfy_sequenceFin)
open Quantum.Qrom.SufCma.Multi (MuPort muAdvSpec cmdCharge hashCharge signCharge MuSignLog
  withMuSignLog muChallenge muChallenged muGame muWinProb generateAll)

variable {n : ℕ}

-- The adversary's commands, as an indexed polynomial functor.
set_option quotPrecheck false in
local notation "MuP" n => QuantumComp.toIPFunctor LocalSig.instruments.{0}
  (muAdvSpec n SigningRequest (Option Signature))

local notation "ev" H => evalWithAnswerFn (romAnswers H)

/-! ## The signer hashes only -/

section HashOnly

variable {f : QueryImpl RomOracles Id}

theorem isHash_bind {α β : Type} {x : OracleComp RomOracles α}
    {k : α → OracleComp RomOracles β} (hx : QueriesSatisfy f IsHash x)
    (hk : ∀ a, QueriesSatisfy f IsHash (k a)) : QueriesSatisfy f IsHash (x >>= k) :=
  queriesSatisfy_bind hx (hk _)

theorem isHash_chainWalk (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (start steps : ℕ) (value : Digest) :
    QueriesSatisfy f IsHash (Over.chainWalk hashQ P l e i start steps value) :=
  isHash_walkChain (fun _ _ ↦ isHash_th _ _ _) start steps value

theorem isHash_otsSecrets (P : PublicParameter) (l : Layer) (e : KeyIndex) (seed : MasterSeed) :
    QueriesSatisfy f IsHash (Over.otsSecrets hashQ P l e seed) :=
  isHash_bind (queriesSatisfy_sequenceFin fun _ ↦ isHash_hashQ _) fun _ ↦ queriesSatisfy_pure _

theorem isHash_oneTimePublicKey (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (seed : MasterSeed) : QueriesSatisfy f IsHash (Over.oneTimePublicKey hashQ P l e seed) :=
  isHash_bind (isHash_otsSecrets P l e seed) fun _ ↦
    queriesSatisfy_sequenceFin fun _ ↦ isHash_chainWalk _ _ _ _ _ _ _

theorem isHash_buildTree (leaf : ℕ → OracleComp RomOracles Digest)
    (node : ℕ → ℕ → HashInput → OracleComp RomOracles Digest)
    (hl : ∀ i, QueriesSatisfy f IsHash (leaf i))
    (hn : ∀ lv i p, QueriesSatisfy f IsHash (node lv i p)) :
    ∀ level index, QueriesSatisfy f IsHash (buildTree leaf node level index)
  | 0, index => hl index
  | level + 1, index => by
    rw [buildTree]
    exact isHash_bind (isHash_buildTree leaf node hl hn level _) fun _ ↦
      isHash_bind (isHash_buildTree leaf node hl hn level _) fun _ ↦ hn _ _ _

theorem isHash_treeNode (P : PublicParameter) (l : Layer) (seed : MasterSeed) (level index : ℕ) :
    QueriesSatisfy f IsHash (Over.treeNode hashQ P l seed level index) :=
  isHash_buildTree _ _
    (fun _ ↦ isHash_bind (isHash_oneTimePublicKey _ _ _ _) fun _ ↦ isHash_th _ _ _)
    (fun _ _ _ ↦ isHash_th _ _ _) level index

theorem isHash_treePath (P : PublicParameter) (l : Layer) (seed : MasterSeed) (e : KeyIndex) :
    QueriesSatisfy f IsHash (Over.treePath hashQ P l seed e) :=
  queriesSatisfy_sequenceFin fun _ ↦ isHash_treeNode _ _ _ _ _

theorem isHash_otsSignFrom (P : PublicParameter) (l : Layer) (e : KeyIndex) (seed : MasterSeed)
    (message : HashInput) (base : Randomizer) : ∀ attempts trial,
    QueriesSatisfy f IsHash (Over.otsSignFrom hashQ P l e seed message base attempts trial)
  | 0, _ => queriesSatisfy_pure _
  | attempts + 1, trial => by
    rw [Over.otsSignFrom]
    refine isHash_bind (isHash_th _ _ _) fun _ ↦ ?_
    split
    · exact isHash_bind (isHash_otsSecrets _ _ _ _) fun _ ↦
        isHash_bind (queriesSatisfy_sequenceFin fun _ ↦ isHash_chainWalk _ _ _ _ _ _ _) fun _ ↦
          queriesSatisfy_pure _
    · exact isHash_otsSignFrom P l e seed message base attempts (trial + 1)

theorem isHash_signLayer (seed : MasterSeed) (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (message : HashInput) : QueriesSatisfy f IsHash (Over.signLayer hashQ seed P l e message) := by
  rw [Over.signLayer, Over.otsSign]
  refine isHash_bind (isHash_bind (isHash_th _ _ _) fun _ ↦ isHash_otsSignFrom _ _ _ _ _ _ _ _)
    fun _ ↦ ?_
  split
  · exact isHash_bind (isHash_treePath _ _ _ _) fun _ ↦ queriesSatisfy_pure _
  · exact queriesSatisfy_pure _

theorem isHash_signWithSchemeSeed (seed : MasterSeed) (P : PublicParameter) (idx : LeafIndex)
    (m : Message) : QueriesSatisfy f IsHash (Over.signWithSchemeSeed hashQ seed P idx m) := by
  rw [Over.signWithSchemeSeed]
  refine isHash_bind (isHash_signLayer _ _ _ _ _) fun _ ↦ ?_
  split
  · refine isHash_bind (isHash_treeNode _ _ _ _ _) fun _ ↦
      isHash_bind (isHash_signLayer _ _ _ _ _) fun _ ↦ ?_
    split <;> exact queriesSatisfy_pure _
  · exact queriesSatisfy_pure _

/-- **leanXMSS's signer hashes only**: it samples no coins. -/
theorem isHash_sign (sk : SecretKey) (r : SigningRequest) :
    QueriesSatisfy f IsHash (xmssRom.sign sk r) := by
  change QueriesSatisfy f IsHash (Over.sign hashQ sk r.leafIndex r.message)
  exact isHash_bind (isHash_hashQ _) fun _ ↦ isHash_signWithSchemeSeed _ _ _ _

end HashOnly

/-! ## The signer with a memoized top layer -/

/-- The top key of a request: the top-layer key of its leaf. -/
def topKeyOf (r : SigningRequest) : KeyIndex :=
  keyIndexOnLayer r.leafIndex topLayer

/-- A signature at leaf `idx` from its bottom layer and its top layer, if any. -/
def assembleSig (idx : LeafIndex) (bottom : LayerSignature) :
    Option LayerSignature → Option Signature
  | none => none
  | some top => some ⟨idx, fun layer => if layer = bottomLayer then bottom else top⟩

/-- The top layer's signature at the top key `t` from the scheme seed: the root of the bottom tree
below `t`, signed by `t`. -/
def topPart (seed : MasterSeed) (P : PublicParameter) (t : KeyIndex) :
    OracleComp RomOracles (Option LayerSignature) := do
  let bottomRoot ← Over.treeNode hashQ P bottomLayer seed layerHeight t.val
  Over.signLayer hashQ seed P topLayer t (littleEndianBytes 16 bottomRoot)

/-- The top layer's signature at the top key `t` from the secret key. -/
def topFull (sk : SecretKey) (t : KeyIndex) : OracleComp RomOracles (Option LayerSignature) := do
  let seed ← Over.schemeSeedOf hashQ sk.keySeed
  topPart seed sk.parameter t

/-- **The signer with a memoized top layer `top`**: the scheme seed and the bottom layer, then
`top` in place of the top layer's computation. -/
def signHit (sk : SecretKey) (r : SigningRequest) (top : Option LayerSignature) :
    OracleComp RomOracles (Option Signature) := do
  let seed ← Over.schemeSeedOf hashQ sk.keySeed
  let some bottom ← Over.signLayer hashQ seed sk.parameter bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message)
    | return none
  return assembleSig r.leafIndex bottom top

/-- **The signer reporting its top layer**: the signature, and the top layer's signature when the
bottom layer succeeded. -/
def signRecord (sk : SecretKey) (r : SigningRequest) :
    OracleComp RomOracles (Option Signature × Option (Option LayerSignature)) := do
  let seed ← Over.schemeSeedOf hashQ sk.keySeed
  let some bottom ← Over.signLayer hashQ seed sk.parameter bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message)
    | return (none, none)
  let top ← topPart seed sk.parameter (topKeyOf r)
  return (assembleSig r.leafIndex bottom top, some top)

theorem isHash_topPart {f : QueryImpl RomOracles Id} (seed : MasterSeed) (P : PublicParameter)
    (t : KeyIndex) : QueriesSatisfy f IsHash (topPart seed P t) :=
  isHash_bind (isHash_treeNode _ _ _ _ _) fun _ ↦ isHash_signLayer _ _ _ _ _

theorem isHash_signHit {f : QueryImpl RomOracles Id} (sk : SecretKey) (r : SigningRequest)
    (top : Option LayerSignature) : QueriesSatisfy f IsHash (signHit sk r top) := by
  unfold signHit
  refine isHash_bind (isHash_hashQ _) fun _ ↦ isHash_bind (isHash_signLayer _ _ _ _ _) fun _ ↦ ?_
  split <;> exact queriesSatisfy_pure _

theorem isHash_signRecord {f : QueryImpl RomOracles Id} (sk : SecretKey) (r : SigningRequest) :
    QueriesSatisfy f IsHash (signRecord sk r) := by
  unfold signRecord
  refine isHash_bind (isHash_hashQ _) fun _ ↦ isHash_bind (isHash_signLayer _ _ _ _ _) fun _ ↦ ?_
  split
  · exact isHash_bind (isHash_topPart _ _ _) fun _ ↦ queriesSatisfy_pure _
  · exact queriesSatisfy_pure _

section Abstract

variable (f : QueryImpl RomOracles Id) (seedC : OracleComp RomOracles MasterSeed)
  (bl : MasterSeed → OracleComp RomOracles (Option LayerSignature))
  (tn : MasterSeed → OracleComp RomOracles Digest)
  (tl : MasterSeed → Digest → OracleComp RomOracles (Option LayerSignature)) (idx : LeafIndex)

/-- The memoized top layer, over abstract computations. -/
theorem eval_hit_abstract :
    evalWithAnswerFn f (do
      let seed ← seedC
      let some bottom ← bl seed | return none
      let bottomRoot ← tn seed
      let some top ← tl seed bottomRoot | return none
      return some (⟨idx, fun layer => if layer = bottomLayer then bottom else top⟩ : Signature)) =
    evalWithAnswerFn f (do
      let seed ← seedC
      let some bottom ← bl seed | return none
      return assembleSig idx bottom (evalWithAnswerFn f (do
        let seed ← seedC
        let bottomRoot ← tn seed
        tl seed bottomRoot))) := by
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn f (bl (evalWithAnswerFn f seedC)) with
  | none => rfl
  | some bottom =>
    simp only [evalWithAnswerFn_bind]
    cases evalWithAnswerFn f (tl (evalWithAnswerFn f seedC)
      (evalWithAnswerFn f (tn (evalWithAnswerFn f seedC)))) <;> rfl

/-- The recording signer's signature, over abstract computations. -/
theorem eval_record_fst_abstract :
    (evalWithAnswerFn f (do
      let seed ← seedC
      let some bottom ← bl seed
        | return ((none : Option Signature), (none : Option (Option LayerSignature)))
      let top ← (do let bottomRoot ← tn seed; tl seed bottomRoot)
      return (assembleSig idx bottom top, some top))).1 =
    evalWithAnswerFn f (do
      let seed ← seedC
      let some bottom ← bl seed | return none
      return assembleSig idx bottom (evalWithAnswerFn f (do
        let seed ← seedC
        let bottomRoot ← tn seed
        tl seed bottomRoot))) := by
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn f (bl (evalWithAnswerFn f seedC)) <;>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- The recording signer's top layer, over abstract computations. -/
theorem eval_record_snd_abstract (top : Option LayerSignature)
    (h : (evalWithAnswerFn f (do
      let seed ← seedC
      let some bottom ← bl seed
        | return ((none : Option Signature), (none : Option (Option LayerSignature)))
      let top ← (do let bottomRoot ← tn seed; tl seed bottomRoot)
      return (assembleSig idx bottom top, some top))).2 = some top) :
    top = evalWithAnswerFn f (do
      let seed ← seedC
      let bottomRoot ← tn seed
      tl seed bottomRoot) := by
  revert h
  simp only [evalWithAnswerFn_bind]
  cases evalWithAnswerFn f (bl (evalWithAnswerFn f seedC)) with
  | none => simp
  | some bottom =>
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq]
    exact fun h ↦ h.symm

end Abstract

section Eval

variable (f : QueryImpl RomOracles Id) (sk : SecretKey) (r : SigningRequest)

/-- **The memoized top layer is exact**: answered by `f`, the signer is the memo signer with the
top layer of the request's top key. -/
theorem eval_sign_eq_signHit :
    evalWithAnswerFn f (xmssRom.sign sk r) =
      evalWithAnswerFn f (signHit sk r (evalWithAnswerFn f (topFull sk (topKeyOf r)))) := by
  change evalWithAnswerFn f (Over.sign hashQ sk r.leafIndex r.message) = _
  exact eval_hit_abstract f (Over.schemeSeedOf hashQ sk.keySeed)
    (fun seed ↦ Over.signLayer hashQ seed sk.parameter bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message))
    (fun seed ↦ Over.treeNode hashQ sk.parameter bottomLayer seed layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val)
    (fun seed br ↦ Over.signLayer hashQ seed sk.parameter topLayer
      (keyIndexOnLayer r.leafIndex topLayer) (littleEndianBytes 16 br)) r.leafIndex

/-- The signature the recording signer returns is the signer's. -/
theorem eval_signRecord_fst :
    (evalWithAnswerFn f (signRecord sk r)).1 = evalWithAnswerFn f (xmssRom.sign sk r) := by
  rw [eval_sign_eq_signHit]
  exact eval_record_fst_abstract f (Over.schemeSeedOf hashQ sk.keySeed)
    (fun seed ↦ Over.signLayer hashQ seed sk.parameter bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message))
    (fun seed ↦ Over.treeNode hashQ sk.parameter bottomLayer seed layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val)
    (fun seed br ↦ Over.signLayer hashQ seed sk.parameter topLayer
      (keyIndexOnLayer r.leafIndex topLayer) (littleEndianBytes 16 br)) r.leafIndex

/-- The top layer the recording signer reports is the top layer of the request's top key. -/
theorem eval_signRecord_snd (top : Option LayerSignature)
    (h : (evalWithAnswerFn f (signRecord sk r)).2 = some top) :
    top = evalWithAnswerFn f (topFull sk (topKeyOf r)) :=
  eval_record_snd_abstract f (Over.schemeSeedOf hashQ sk.keySeed)
    (fun seed ↦ Over.signLayer hashQ seed sk.parameter bottomLayer
      (keyIndexOnLayer r.leafIndex bottomLayer) (littleEndianBytes 32 r.message))
    (fun seed ↦ Over.treeNode hashQ sk.parameter bottomLayer seed layerHeight
      (keyIndexOnLayer r.leafIndex topLayer).val)
    (fun seed br ↦ Over.signLayer hashQ seed sk.parameter topLayer
      (keyIndexOnLayer r.leafIndex topLayer) (littleEndianBytes 16 br)) r.leafIndex top h

end Eval

/-! ## The memo challenger -/

/-- **The memo**: per user and top key, the top layer's signature once computed. -/
abbrev TopMemo (n : ℕ) := Fin n → KeyIndex → Option (Option LayerSignature)

/-- Record the report `o` of user `i`'s recording signer at the top key `t`: nothing when the
bottom layer failed. -/
def TopMemo.record (M : TopMemo n) (i : Fin n) (t : KeyIndex) :
    Option (Option LayerSignature) → TopMemo n
  | none => M
  | some top => Function.update M i (Function.update (M i) t (some top))

/-- **The memo agrees with `H`**: every memoized top layer is the top layer against `H`. -/
def MemoOK (H : HashDomain → HashOutput) (sks : Fin n → SecretKey) (M : TopMemo n) : Prop :=
  ∀ i t top, M i t = some top → top = (ev H) (topFull (sks i) t)

theorem memoOK_empty (H : HashDomain → HashOutput) (sks : Fin n → SecretKey) :
    MemoOK H sks fun _ _ ↦ none :=
  fun _ _ _ h ↦ by simp at h

theorem MemoOK.record {H : HashDomain → HashOutput} {sks : Fin n → SecretKey} {M : TopMemo n}
    (hM : MemoOK H sks M) (i : Fin n) (t : KeyIndex) {o : Option (Option LayerSignature)}
    (ho : ∀ top, o = some top → top = (ev H) (topFull (sks i) t)) :
    MemoOK H sks (M.record i t o) := by
  intro j s top h
  rcases o with _ | top'
  · exact hM j s top h
  · by_cases hj : j = i
    · subst hj
      by_cases hs : s = t
      · subst hs
        simp only [TopMemo.record, Function.update_self, Option.some.injEq] at h
        rw [← h]
        exact ho top' rfl
      · simp only [TopMemo.record, Function.update_self, Function.update_of_ne hs] at h
        exact hM j s top h
    · simp only [TopMemo.record, Function.update_of_ne hj] at h
      exact hM j s top h

/-- **The answer program of a classical algorithm at a signing request**: relabel the register,
then run the algorithm by classical calls. -/
noncomputable def answerTree {β : Type} (oa : OracleComp RomOracles β) (r : SigningRequest)
    (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    QComp romSpec A
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E)) β :=
  (QComp.act (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
    (SubInstrument.relabel ℓ)).bind fun _ ↦ oa.toQuantumAt (SufCma.romImpl _)

theorem signTree_eq_answerTree (sk : SecretKey) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    SufCma.signTree xmssRom sk r E ℓ = answerTree (xmssRom.sign sk r) r E ℓ :=
  rfl

/-- **The memo challenger from the memo `M`**: a local operation and a hash call as the challenger;
a request to user `i` below a memoized top key is answered by `signHit` with the memo, any other
request by `signRecord`, whose report joins the memo. -/
noncomputable def muMemoFrom (sks : Fin n → SecretKey) {B : QReg} {α : Type} :
    {A : QReg} → TopMemo n → IFreeM (MuP n) (QuantumComp₂.Leaf B α) A → QComp romSpec A B α
  | _, _, .pure x => IFreeM.pure x
  | _, M, .liftBind (.prim o) next =>
      IFreeM.bind (Y := QuantumComp₂.Leaf B α) (muChallenge xmssRom sks _ (.prim o))
        fun _ ans ↦ ans.2 ▸ muMemoFrom sks M (next ans.1)
  | _, M, .liftBind (.query .hash E ℓ) next =>
      IFreeM.bind (Y := QuantumComp₂.Leaf B α) (muChallenge xmssRom sks _ (.query .hash E ℓ))
        fun _ ans ↦ ans.2 ▸ muMemoFrom sks M (next ans.1)
  | _, M, .liftBind (.query (.sign i r) E ℓ) next =>
      match M i (topKeyOf r) with
      | some top => QuantumComp₂.bind (answerTree (signHit (sks i) r top) r E ℓ) fun resp ↦
          muMemoFrom sks M (next (ULift.up resp))
      | none => QuantumComp₂.bind (answerTree (signRecord (sks i) r) r E ℓ) fun w ↦
          muMemoFrom sks (M.record i (topKeyOf r) w.2) (next (ULift.up w.1))

/-- **The multi-user game with the memo challenger**, from the empty memo. -/
noncomputable def muGameMemo (valid : SignLog → Bool) (S0 : Fin n → MasterSeed)
    (A : MuAdversary n) : QComp romSpec (QReg.of Unit) (QReg.of Unit) Bool :=
  ((generateAll xmssRom n S0).toQuantumAt (SufCma.romImpl _)).bind fun keys ↦
    (muMemoFrom (fun i ↦ (keys i).2) (fun _ _ ↦ none) (withMuSignLog (A fun i ↦ (keys i).1))).bind
      fun run ↦
        ((xmssRom.verify (keys run.1.1).1 run.1.2).toQuantumAt (SufCma.romImpl _)).bind
          fun verified ↦ QuantumComp₂.pure (xmssRom.winningCondition (run.2.user run.1.1) run.1.2 &&
            run.2.allValid valid && verified)

/-- The winning probability of the memo game. -/
noncomputable def muWinProbMemo (valid : SignLog → Bool) (n : ℕ) (A : MuAdversary n) : ℝ≥0∞ :=
  ∑ S0 : Fin n → MasterSeed, (∏ i, Pr{let s ← xmssRom.sampleSeed}[s = S0 i]) *
    qromEvalDistMap .instruments (muGameMemo valid S0 A) (SubState.basis ()) (fun _ p ↦ p.2.2)
      {true}

/-! ## Exactness against a fixed function -/

/-- A computation that hashes only, against `H`, returns its value. -/
theorem simulateQ_eager_eq_pure (H : HashDomain → HashOutput) {α : Type}
    (oa : OracleComp RomOracles α) (hoa : QueriesSatisfy (romAnswers H) IsHash oa) :
    simulateQ (eagerFunOracles H) oa = pure ((ev H) oa) :=
  simulateQ_eq_pure_of_queriesSatisfy (fun _ ↦ rfl) not_isHash_inl oa hoa

section Weight

variable {A : Type*} [Fintype A] {ι : Type*} {B : ι → Type*} [∀ i, Fintype (B i)]

/-- The weight depends on the substate's matrix only. -/
theorem obsWeight_congr_matrix (p : DSubInstrument A ι B) {ρ σ : SubState A}
    (h : ρ.matrix = σ.matrix) (g : ι → ℝ≥0∞) : obsWeight p ρ g = obsWeight p σ g := by
  unfold obsWeight
  rw [h]

/-- The weight of the zero substate vanishes. -/
theorem obsWeight_eq_zero_of_matrix (p : DSubInstrument A ι B) {ρ : SubState A}
    (h : ρ.matrix = 0) (g : ι → ℝ≥0∞) : obsWeight p ρ g = 0 := by
  unfold obsWeight
  simp [h]

end Weight

/-- **A classical algorithm that hashes only, against `H`**: run by classical calls and continued
by `K`, it has the weights of `K` at its value. -/
theorem obsWeight_run_toQuantumAt_bind (H : HashDomain → HashOutput) {B C : QReg} {α β : Type}
    (oa : OracleComp RomOracles α) (hoa : QueriesSatisfy (romAnswers H) IsHash oa)
    (K : α → QComp romSpec B C β) (σ : SubState (B × (additiveOracleRuntime H).D))
    (g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞) :
    obsWeight ((additiveOracleRuntime H).run .instruments
        ((oa.toQuantumAt (SufCma.romImpl B)).bind K)) σ g =
      obsWeight ((additiveOracleRuntime H).run .instruments (K ((ev H) oa))) σ g := by
  classical
  have hc := classicalOn_toQuantumAt_funImpl B H oa
  rw [simulateQ_eager_eq_pure H oa hoa, ← SufCma.romImpl_eq_funImpl] at hc
  rw [obsWeight_run_bind₂, tsum_eq_single ((ev H) oa)]
  · refine obsWeight_congr_matrix _ ?_ _
    rw [DSubInstrument.matrix_post, hc]
    simp
  · intro a ha
    refine obsWeight_eq_zero_of_matrix _ ?_ _
    rw [DSubInstrument.matrix_post, hc]
    simp [Ne.symm ha]

/-- The answer program of a classical algorithm that hashes only, against `H`: the relabel, then
the continuation at the algorithm's value. -/
theorem obsWeight_answerTree_bind (H : HashDomain → HashOutput) {β γ : Type} {C : QReg}
    (oa : OracleComp RomOracles β) (hoa : QueriesSatisfy (romAnswers H) IsHash oa)
    (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E)
    (K : β → QComp romSpec
      (QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E)) C γ)
    (ρ : SubState (A × (additiveOracleRuntime H).D))
    (g : (Σ u, QuantumComp₂.Leaf C γ u) → ℝ≥0∞) :
    obsWeight ((additiveOracleRuntime H).run .instruments ((answerTree oa r E ℓ).bind K)) ρ g =
      ∑' u, obsWeight ((additiveOracleRuntime H).run .instruments (K ((ev H) oa)))
        (((additiveOracleRuntime H).run₂ .instruments (QComp.act (spec := romSpec)
          (B := QReg.of ((SufCma.advSpec SigningRequest (Option Signature)).Out (.sign r) × E))
          (SubInstrument.relabel ℓ))).post ρ u) g := by
  unfold answerTree
  rw [QuantumComp₂.bind_assoc, obsWeight_run_bind₂]
  exact tsum_congr fun u ↦ obsWeight_run_toQuantumAt_bind H oa hoa K _ g

/-- The challenged program at a signing request: the signer's answer program, then the
challenged continuation. -/
theorem muChallenged_liftBind_sign (sks : Fin n → SecretKey) {B : QReg} {α : Type} {A : QReg}
    (i : Fin n) (r : SigningRequest) (E : QReg)
    (ℓ : A ≃ (muAdvSpec n SigningRequest (Option Signature)).In (.sign i r) × E)
    (next : (b : (MuP n).B A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ)) →
      IFreeM (MuP n) (QuantumComp₂.Leaf B α)
        ((MuP n).src A (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) b)) :
    muChallenged xmssRom sks (IFreeM.liftBind (QuantumComp.Cmd.query (MuPort.sign i r) E ℓ) next) =
      QuantumComp₂.bind (answerTree (xmssRom.sign (sks i) r) r E ℓ) fun resp ↦
        muChallenged xmssRom sks (next (ULift.up resp)) := by
  refine (IFreeM.bind_assoc _ _ _).trans
    (congrArg (IFreeM.bind _) (funext fun u ↦ funext fun l ↦ ?_))
  obtain ⟨rfl, a⟩ := l
  rfl

variable (H : HashDomain → HashOutput) (sks : Fin n → SecretKey)

/-- The weights of the challenged commands below a common first command, a local operation or a
hash call, agree when they agree below each of its answers. -/
theorem obsWeight_muChallenge_bind_congr {A B C : QReg} {γ β : Type} (c : (MuP n).A A)
    {y y' : (b : (MuP n).B A c) → QComp romSpec ((MuP n).src A c b) B γ}
    {k : γ → QComp romSpec B C β} {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞}
    (h : ∀ b σ,
      obsWeight ((additiveOracleRuntime H).run .instruments ((y b).bind k)) σ g =
        obsWeight ((additiveOracleRuntime H).run .instruments ((y' b).bind k)) σ g)
    (ρ : SubState (A × (additiveOracleRuntime H).D)) :
    obsWeight ((additiveOracleRuntime H).run .instruments (QuantumComp₂.bind
        (IFreeM.bind (Y := QuantumComp₂.Leaf B γ) (muChallenge xmssRom sks A c)
          fun _ ans ↦ ans.2 ▸ y ans.1) k)) ρ g =
      obsWeight ((additiveOracleRuntime H).run .instruments (QuantumComp₂.bind
        (IFreeM.bind (Y := QuantumComp₂.Leaf B γ) (muChallenge xmssRom sks A c)
          fun _ ans ↦ ans.2 ▸ y' ans.1) k)) ρ g := by
  simp only [QuantumComp₂.bind, FreeM₂.bind, IFreeM.bind_assoc]
  rw [obsWeight_run_bind, obsWeight_run_bind]
  refine tsum_congr fun p ↦ ?_
  obtain ⟨t, b, rfl⟩ := p
  exact h b _

/-- **The memo is exact against `H`**: from a memo that agrees with `H`, the memo challenger
gives the challenged program's weights. -/
theorem obsWeight_muMemoFrom_eq {B C : QReg} {α β : Type} {k : α → QComp romSpec B C β}
    {g : (Σ u, QuantumComp₂.Leaf C β u) → ℝ≥0∞} {A : QReg}
    (x : IFreeM (MuP n) (QuantumComp₂.Leaf B α) A) (M : TopMemo n) (hM : MemoOK H sks M)
    (ρ : SubState (A × (additiveOracleRuntime H).D)) :
    obsWeight ((additiveOracleRuntime H).run .instruments ((muChallenged xmssRom sks x).bind k))
        ρ g =
      obsWeight ((additiveOracleRuntime H).run .instruments
        (QuantumComp₂.bind (muMemoFrom sks M x) k)) ρ g := by
  induction x using IFreeM.inductionOn generalizing M with
  | pure _ _ => rfl
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact obsWeight_muChallenge_bind_congr H sks (.prim o)
        (y := fun b ↦ muChallenged xmssRom sks (next b))
        (y' := fun b ↦ muMemoFrom sks M (next b)) (fun b σ ↦ ih b M hM σ) ρ
    · exact obsWeight_muChallenge_bind_congr H sks (.query .hash E ℓ)
        (y := fun b ↦ muChallenged xmssRom sks (next b))
        (y' := fun b ↦ muMemoFrom sks M (next b)) (fun b σ ↦ ih b M hM σ) ρ
    · rw [muChallenged_liftBind_sign, QuantumComp₂.bind_assoc,
        obsWeight_answerTree_bind H _ (isHash_sign _ _)]
      cases hm : M i (topKeyOf r) with
      | some top =>
        simp only [muMemoFrom, hm]
        rw [QuantumComp₂.bind_assoc, obsWeight_answerTree_bind H _ (isHash_signHit _ _ _)]
        refine tsum_congr fun u ↦ ?_
        rw [hM i _ top hm, ← eval_sign_eq_signHit]
        exact ih _ M hM _
      | none =>
        simp only [muMemoFrom, hm]
        rw [QuantumComp₂.bind_assoc, obsWeight_answerTree_bind H _ (isHash_signRecord _ _)]
        refine tsum_congr fun u ↦ ?_
        rw [eval_signRecord_fst]
        exact ih _ _ (hM.record i _ fun top h ↦ eval_signRecord_snd _ _ _ top h) _

/-- **Per function `H`, the memo game has the game's weights.** -/
theorem obsWeight_muGameMemo_eq (valid : SignLog → Bool) (S0 : Fin n → MasterSeed)
    (A : MuAdversary n) (σ : SubState (QReg.of Unit × (additiveOracleRuntime H).D)) :
    obsWeight ((additiveOracleRuntime H).run .instruments (muGame xmssRom valid S0 A)) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) =
      obsWeight ((additiveOracleRuntime H).run .instruments (muGameMemo valid S0 A)) σ
        (fun p ↦ ({true} : Set Bool).indicator 1 p.2.2) := by
  unfold muGame muGameMemo
  rw [obsWeight_run_bind₂, obsWeight_run_bind₂]
  exact tsum_congr fun keys ↦ obsWeight_muMemoFrom_eq H _ _ _ (memoOK_empty H _) _

/-- **The memo challenger is exact**: the multi-user winning probability is the memo game's. -/
theorem muWinProb_eq_muWinProbMemo (valid : SignLog → Bool) (A : MuAdversary n) :
    muWinProb xmssRom valid n A = muWinProbMemo valid n A := by
  unfold muWinProb muWinProbMemo
  refine Finset.sum_congr rfl fun S0 _ ↦ congrArg _ (le_antisymm ?_ ?_)
  · exact qromEvalDistMap_true_le _ _ _ _ fun H ↦ (obsWeight_muGameMemo_eq H valid S0 A _).le
  · exact qromEvalDistMap_true_le _ _ _ _ fun H ↦ (obsWeight_muGameMemo_eq H valid S0 A _).ge

/-- **Refusal, then the memo**: the multi-user winning probability is at most the memo game's of
the adversary that never reuses a leaf of a user. -/
theorem muWinProb_le_muWinProbMemo_refuseMu (A : MuAdversary n) :
    muWinProb xmssRom xmssValid n A ≤ muWinProbMemo xmssValid n (refuseMu A) :=
  (muWinProb_le_refuseMu A).trans_eq (muWinProb_eq_muWinProbMemo xmssValid _)

/-! ## Call budgets -/

/-- The answer program makes the algorithm's calls. -/
theorem isTotalQueryBound_answerTree {β : Type} {oa : OracleComp RomOracles β} {c : ℕ}
    (h : Common.QueryCostAtMost oa hashCallCost c) (r : SigningRequest) (E : QReg) {A : QReg}
    (ℓ : A ≃ (SufCma.advSpec SigningRequest (Option Signature)).In (.sign r) × E) :
    (answerTree oa r E ℓ).IsTotalQueryBound (0 + c) :=
  FreeM₂.isChargeBound_bind (Quantum.SufCma.isTotalQueryBound_act _ 0) fun _ ↦
    SufCma.isTotalQueryBound_toQuantumAt_romImpl _ h

/-- **The memo challenger's calls.** An adversary making at most `q` hash calls and at most
`total` signing requests on every path, against memo signers making at most `sc` hash calls per
answer, makes at most `q + sc * total` calls of `H` on every path. -/
theorem isTotalQueryBound_muMemoFrom {sc : ℕ}
    (hhit : ∀ sk r top, Common.QueryCostAtMost (signHit sk r top) hashCallCost sc)
    (hrec : ∀ sk r, Common.QueryCostAtMost (signRecord sk r) hashCallCost sc) {B : QReg}
    {α : Type}
    {A : QReg} (x : IFreeM (MuP n) (QuantumComp₂.Leaf B α) A) (M : TopMemo n) {q total : ℕ}
    (hh : IFreeM.IsChargeBound x (cmdCharge hashCharge) q)
    (hs : IFreeM.IsChargeBound x (cmdCharge signCharge) total) :
    (muMemoFrom sks M x).IsTotalQueryBound (q + sc * total) := by
  induction x using IFreeM.inductionOn generalizing M q total with
  | pure _ _ => trivial
  | liftBind A c next ih =>
    rcases c with o | ⟨_ | ⟨i, r⟩, E, ℓ⟩
    · exact ⟨Nat.zero_le _, fun b ↦ ih b M (hh.2 b) (hs.2 b)⟩
    · have h1 : 1 ≤ q := hh.1
      refine ⟨by simp only [QuantumComp.Cmd.queryCharge]; omega, fun b ↦ ?_⟩
      refine (ih b M (hh.2 b) (hs.2 b)).mono ?_
      simp only [cmdCharge, hashCharge, signCharge, QuantumComp.Cmd.queryCharge, Nat.sub_zero]
      omega
    · have h1 : 1 ≤ total := hs.1
      obtain ⟨t, rfl⟩ : ∃ t, total = t + 1 := ⟨total - 1, by omega⟩
      have hle : 0 + sc + (q + sc * t) ≤ q + sc * (t + 1) := by
        rw [Nat.mul_succ]
        omega
      cases hm : M i (topKeyOf r) with
      | some top =>
        simp only [muMemoFrom, hm]
        refine (FreeM₂.isChargeBound_bind (isTotalQueryBound_answerTree (hhit _ _ _) r E ℓ)
          fun resp ↦ ih (ULift.up resp) M (hh.2 _) (hs.2 _)).mono ?_
        simpa [cmdCharge, hashCharge, signCharge] using hle
      | none =>
        simp only [muMemoFrom, hm]
        refine (FreeM₂.isChargeBound_bind (isTotalQueryBound_answerTree (hrec _ _) r E ℓ)
          fun (w : Option Signature × Option (Option LayerSignature)) ↦
            ih (ULift.up w.1) _ (hh.2 _) (hs.2 _)).mono ?_
        simpa [cmdCharge, hashCharge, signCharge] using hle

end Quantum.Qrom.Xmss.Multi

end
