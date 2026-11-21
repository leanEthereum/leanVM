module

public import Quantum.StdModel.Formats
public import Quantum.StdModel.Sphincs.Events
public import Quantum.Sphincs.HonestTable.Values

@[expose] public section

/-!
# leanSPHINCS at a fixed hash: the honest table of a key

* `Over.simulateQ_sign`, `Over.simulateQ_keygenFromSeed`, `Over.simulateQ_verify`, ...: answering
  the oracles of the scheme over any hash `hash` by `impl` runs the scheme over the hash
  `simulateQ impl ∘ hash`.
* `verify_eq_pure_of_hash`: over a hash answering purely by `h`, the verifier returns its
  evaluation with `h`.
* `mkTable h prfKeyOut pkSeedOut sec rnd`: the table with the given secrets and every other
  position the hash of its honest input; it is honest (`honest_mkTable`) and every honest table
  is it up to the second components outside the digest cells (`fst_eq_mkTable_of_honest`,
  `digest_eq_mkTable_of_honest`, `eq_mkTable_of_honest`).
* `answersTable_of_honest`, `answersDigest_of_honest`, `answersEnc_of_honest`: a hash answering
  the secrets by the table and every other input by `h` answers an honest table, so the scheme
  returns the table's keys and signatures (`keygenFromSeed_eq_pure_of_honest`,
  `sign_eq_pure_of_honest`).
* `digTable h P sec rnd`: the table of given digests. Only digests matter: an honest table has
  the public key and signatures of the table of its digests (`publicKey_eq_digTable_of_honest`,
  `signature_eq_digTable_of_honest`); the public key reads no randomizer and the signature of
  `M` only the randomizer of `M` (`publicKey_digTable_congr`, `signature_digTable_congr`).
* `routeHash P sec rnd hash`: the secrets' inputs under `SK.seed = 0` answered by `sec` and
  `rnd`, every other input by `hash`; the routed scheme returns the keys and signatures of
  `digTable` (`keygenFromSeed_routeHash`, `sign_routeHash`).
* `sum_truncateHash`: every digest is the truncation of `2^128` hash outputs.
* `seedTable h S0`, `realTable W tab S0`: the table of `SK.seed = S0` under `h` (every secret
  the hash of its input); at a fixed table of a world the scheme returns its keys and signatures
  (`simulateQ_generateKeys_eager`, `simulateQ_sign_eager`) and verifies by evaluation
  (`simulateQ_verify_eager`).
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Common.SufCma (SchemeHashSpec)
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Sphincs (messageDigestInput prfMessageInput)
open Quantum.Qrom.Sphincs

namespace Quantum.StdModel.Sphincs

/-! ## Answering the scheme's oracles -/

namespace Over

section Sim

variable {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n] [LawfulMonad n]
  (impl : QueryImpl O n) (hash : HashInput → OracleComp O HashOutput)

theorem simulateQ_addressedHash (seed : PublicParameter) (address : Address)
    (payload : HashInput) :
    simulateQ impl (LeanSphincsOver.addressedHash hash seed address payload) =
      LeanSphincsOver.addressedHash (fun x ↦ simulateQ impl (hash x)) seed address payload := by
  simp only [LeanSphincsOver.addressedHash, simulateQ_bind, simulateQ_pure]

theorem simulateQ_chainWalk (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) (start steps : ℕ) (value : Digest) :
    simulateQ impl (LeanSphincsOver.chainWalk hash seed l τ e i start steps value) =
      LeanSphincsOver.chainWalk (fun x ↦ simulateQ impl (hash x)) seed l τ e i start steps
        value := by
  simp only [LeanSphincsOver.chainWalk, Quantum.Sphincs.WithHash.simulateQ_walkChain,
    simulateQ_addressedHash]

theorem simulateQ_encode (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    simulateQ impl (LeanSphincsOver.encode hash seed l τ e message counter) =
      LeanSphincsOver.encode (fun x ↦ simulateQ impl (hash x)) seed l τ e message counter := by
  simp only [LeanSphincsOver.encode, simulateQ_bind, simulateQ_pure, simulateQ_addressedHash]

theorem simulateQ_otsLeaf (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) :
    simulateQ impl (LeanSphincsOver.otsLeaf hash seed l τ e message counter values) =
      LeanSphincsOver.otsLeaf (fun x ↦ simulateQ impl (hash x)) seed l τ e message counter
        values := by
  simp only [LeanSphincsOver.otsLeaf, simulateQ_bind, simulateQ_encode]
  refine bind_congr fun x ↦ ?_
  cases x with
  | none => rfl
  | some encoding =>
    simp only [simulateQ_bind, simulateQ_pure, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
      LeanSphincsOver.recoverChain, simulateQ_chainWalk, LeanSphincsOver.leafHash,
      simulateQ_addressedHash]

theorem simulateQ_treeFold (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (path : ℕ → Digest) (levels : ℕ) (value : Digest) :
    simulateQ impl (LeanSphincsOver.treeFold hash seed l τ e path levels value) =
      LeanSphincsOver.treeFold (fun x ↦ simulateQ impl (hash x)) seed l τ e path levels value := by
  simp only [LeanSphincsOver.treeFold, Quantum.Sphincs.WithHash.simulateQ_foldPath,
    simulateQ_addressedHash]

theorem simulateQ_forsRecover (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    simulateQ impl (LeanSphincsOver.forsRecover hash seed idx leaves opening) =
      LeanSphincsOver.forsRecover (fun x ↦ simulateQ impl (hash x)) seed idx leaves opening := by
  simp only [LeanSphincsOver.forsRecover, LeanSphincsOver.forsTreeRecover,
    LeanSphincsOver.forsLeafHash, LeanSphincsOver.forsPublicKey, simulateQ_bind,
    Quantum.Sphincs.WithHash.simulateQ_sequenceFin, Quantum.Sphincs.WithHash.simulateQ_foldPath,
    simulateQ_addressedHash]

theorem simulateQ_messageDigest (pk : PublicKey) (randomizer : Randomizer) (message : Message) :
    simulateQ impl (LeanSphincsOver.messageDigest hash pk randomizer message) =
      LeanSphincsOver.messageDigest (fun x ↦ simulateQ impl (hash x)) pk randomizer message := by
  simp only [LeanSphincsOver.messageDigest, LeanSphincsOver.messageDigestCall, simulateQ_bind,
    simulateQ_pure, Quantum.Sphincs.WithHash.simulateQ_sequenceFin]

theorem simulateQ_verifyLayers (seed : PublicParameter) (idx : Index) (σ : Signature) :
    ∀ (layersLeft : ℕ) (message : Digest),
      simulateQ impl (LeanSphincsOver.verifyLayers hash seed idx σ layersLeft message) =
        LeanSphincsOver.verifyLayers (fun x ↦ simulateQ impl (hash x)) seed idx σ layersLeft
          message
  | 0, _ => rfl
  | layersLeft + 1, message => by
    simp only [LeanSphincsOver.verifyLayers]
    split
    · simp only [simulateQ_bind, simulateQ_otsLeaf]
      refine bind_congr fun x ↦ ?_
      cases x with
      | none => rfl
      | some value =>
        simp only [simulateQ_bind, simulateQ_treeFold]
        refine bind_congr fun root ↦ ?_
        split
        · rfl
        · exact simulateQ_verifyLayers seed idx σ layersLeft root
    · rfl

/-- **The verifier**, its oracles answered by `impl`, is the verifier over `simulateQ impl ∘
hash`. -/
theorem simulateQ_verify (pk : PublicKey) (message : Message) (σ : Signature) :
    simulateQ impl (LeanSphincsOver.verify hash pk message σ) =
      LeanSphincsOver.verify (fun x ↦ simulateQ impl (hash x)) pk message σ := by
  simp only [LeanSphincsOver.verify, simulateQ_bind, simulateQ_messageDigest,
    simulateQ_forsRecover]
  refine bind_congr fun digest ↦ bind_congr fun forsKey ↦ ?_
  rw [simulateQ_verifyLayers]
  refine bind_congr fun x ↦ ?_
  cases x <;> rfl

theorem simulateQ_prf (key : ExpandedKey) (domain : KeygenDomain) :
    simulateQ impl (LeanSphincsOver.prf hash key domain) =
      LeanSphincsOver.prf (fun x ↦ simulateQ impl (hash x)) key domain :=
  simulateQ_addressedHash impl hash _ _ _

theorem simulateQ_otsSecrets (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) :
    simulateQ impl (LeanSphincsOver.otsSecrets hash key l τ e) =
      LeanSphincsOver.otsSecrets (fun x ↦ simulateQ impl (hash x)) key l τ e := by
  simp only [LeanSphincsOver.otsSecrets, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
    simulateQ_prf]

theorem simulateQ_otsPublicLeaf (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) :
    simulateQ impl (LeanSphincsOver.otsPublicLeaf hash key l τ e) =
      LeanSphincsOver.otsPublicLeaf (fun x ↦ simulateQ impl (hash x)) key l τ e := by
  simp only [LeanSphincsOver.otsPublicLeaf, simulateQ_bind, simulateQ_otsSecrets,
    Quantum.Sphincs.WithHash.simulateQ_sequenceFin, simulateQ_chainWalk,
    LeanSphincsOver.leafHash, simulateQ_addressedHash]

theorem simulateQ_otsSignFrom (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) : ∀ attempts counter : ℕ,
      simulateQ impl (LeanSphincsOver.otsSignFrom hash key l τ e message attempts counter) =
        LeanSphincsOver.otsSignFrom (fun x ↦ simulateQ impl (hash x)) key l τ e message attempts
          counter
  | 0, _ => by simp [LeanSphincsOver.otsSignFrom]
  | attempts + 1, counter => by
    simp only [LeanSphincsOver.otsSignFrom, simulateQ_bind, simulateQ_encode]
    refine bind_congr fun x ↦ ?_
    cases x with
    | none => exact simulateQ_otsSignFrom key l τ e message attempts (counter + 1)
    | some encoding =>
      simp only [simulateQ_bind, simulateQ_pure, simulateQ_otsSecrets,
        Quantum.Sphincs.WithHash.simulateQ_sequenceFin, simulateQ_chainWalk]

theorem simulateQ_treeLevels (key : ExpandedKey) (l : Layer) (τ : TreeIndex) :
    simulateQ impl (LeanSphincsOver.treeLevels hash key l τ) =
      LeanSphincsOver.treeLevels (fun x ↦ simulateQ impl (hash x)) key l τ := by
  simp only [LeanSphincsOver.treeLevels, Sphincs.KeyGenerationAndSigning.merkleLevels,
    simulateQ_bind, Quantum.Sphincs.WithHash.simulateQ_mapM, simulateQ_otsPublicLeaf,
    Quantum.Sphincs.WithHash.simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_forsOpen (key : ExpandedKey) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    simulateQ impl (LeanSphincsOver.forsOpen hash key idx lv) =
      LeanSphincsOver.forsOpen (fun x ↦ simulateQ impl (hash x)) key idx lv := by
  simp only [LeanSphincsOver.forsOpen, LeanSphincsOver.forsTreeOpen, LeanSphincsOver.forsSecret,
    LeanSphincsOver.forsLeafHash, LeanSphincsOver.forsPublicKey,
    Sphincs.KeyGenerationAndSigning.merkleLevels, simulateQ_bind, simulateQ_pure,
    Quantum.Sphincs.WithHash.simulateQ_sequenceFin, Quantum.Sphincs.WithHash.simulateQ_mapM,
    simulateQ_prf, Quantum.Sphincs.WithHash.simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_expandKey (secretSeed : SecretKey) :
    simulateQ impl (LeanSphincsOver.expandKey hash secretSeed) =
      LeanSphincsOver.expandKey (fun x ↦ simulateQ impl (hash x)) secretSeed := by
  simp only [LeanSphincsOver.expandKey, simulateQ_bind, simulateQ_pure]

theorem simulateQ_keygenInternal (key : ExpandedKey) :
    simulateQ impl (LeanSphincsOver.keygenInternal hash key) =
      LeanSphincsOver.keygenInternal (fun x ↦ simulateQ impl (hash x)) key := by
  simp only [LeanSphincsOver.keygenInternal, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

/-- **Key generation**, its oracles answered by `impl`, is key generation over
`simulateQ impl ∘ hash`. -/
theorem simulateQ_keygenFromSeed (secretSeed : SecretKey) :
    simulateQ impl (LeanSphincsOver.keygenFromSeed hash secretSeed) =
      LeanSphincsOver.keygenFromSeed (fun x ↦ simulateQ impl (hash x)) secretSeed := by
  simp only [LeanSphincsOver.keygenFromSeed, simulateQ_bind, simulateQ_expandKey,
    simulateQ_keygenInternal]
  refine bind_congr fun key ↦ bind_congr fun x ↦ ?_
  rfl

theorem simulateQ_signLayer (key : ExpandedKey) (top : List (List Digest)) (idx : Index)
    (layer : Layer) (message : Digest) :
    simulateQ impl (LeanSphincsOver.signLayer hash key top idx layer message) =
      LeanSphincsOver.signLayer (fun x ↦ simulateQ impl (hash x)) key top idx layer message := by
  simp only [LeanSphincsOver.signLayer, LeanSphincsOver.otsSign, simulateQ_bind,
    simulateQ_otsSignFrom]
  refine bind_congr fun x ↦ ?_
  rcases x with _ | ⟨counter, values⟩
  · rfl
  · by_cases h : layer = topLayer
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

theorem simulateQ_prfMessage (secretPrfKey : HashOutput) (optionalRandomness : Digest)
    (message : Message) :
    simulateQ impl (LeanSphincsOver.prfMessage hash secretPrfKey optionalRandomness message) =
      LeanSphincsOver.prfMessage (fun x ↦ simulateQ impl (hash x)) secretPrfKey
        optionalRandomness message := by
  simp only [LeanSphincsOver.prfMessage, simulateQ_bind, simulateQ_pure]

/-- **The signer**, its oracles answered by `impl`, is the signer over `simulateQ impl ∘ hash`. -/
theorem simulateQ_sign (secretKey : SecretKey) (message : Message) :
    simulateQ impl (LeanSphincsOver.sign hash secretKey message) =
      LeanSphincsOver.sign (fun x ↦ simulateQ impl (hash x)) secretKey message := by
  simp only [LeanSphincsOver.sign, LeanSphincsOver.signWithExpandedKey, simulateQ_bind,
    simulateQ_expandKey, simulateQ_keygenInternal]
  refine bind_congr fun key ↦ bind_congr fun x ↦ ?_
  rcases x with ⟨publicKey, top⟩
  erw [simulateQ_prfMessage]
  simp only [simulateQ_messageDigest, simulateQ_forsOpen, simulateQ_signLayer]
  refine bind_congr fun y ↦ bind_congr fun digest ↦ bind_congr fun f ↦ bind_congr fun b ↦ ?_
  rcases b with _ | ⟨bottom, bottomRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun c ↦ ?_
  rcases c with _ | ⟨middle, middleRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun d ↦ ?_
  rcases d with _ | ⟨topSignature, _⟩ <;> rfl

end Sim

/-- **Pure answers**: answering every query purely by `f` returns the evaluation with `f`. -/
theorem simulateQ_pureAnswers {ι : Type} {spec : OracleSpec.{0, 0} ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (f : QueryImpl spec Id) {α : Type} (x : OracleComp spec α) :
    simulateQ (fun t ↦ pure (f t) : QueryImpl spec m) x = pure (simulateQ f x) := by
  induction x using OracleComp.inductionOn with
  | pure a => exact (simulateQ_pure _ a).trans (congrArg pure (simulateQ_pure f a).symm)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, pure_bind, ih]
    rfl

end Over

/-! ## Evaluation over a pure hash -/

section Pure

variable {m : Type → Type} [Monad m] [LawfulMonad m] {h : HashInput → HashOutput}
  {hash : HashInput → m HashOutput}

/-- **Verification over a pure hash** returns its evaluation with the hash. -/
theorem verify_eq_pure_of_hash (hh : ∀ l, hash l = pure (h l)) (pk : PublicKey) (M : Message)
    (σ : Signature) :
    LeanSphincsOver.verify hash pk M σ =
      pure (LeanSphincsOver.verify (m := Id) (fun l ↦ h l) pk M σ) := by
  let f : QueryImpl SchemeHashSpec Id := fun t ↦ h t
  have e1 : hash = fun l ↦ simulateQ (fun t ↦ pure (f t) : QueryImpl SchemeHashSpec m)
      (Quantum.Sphincs.WithHash.hashQuery l) :=
    funext fun l ↦ (hh l).trans
      (Quantum.Sphincs.WithHash.simulateQ_hashQuery
        (fun t ↦ pure (f t) : QueryImpl SchemeHashSpec m) l).symm
  have e2 : (fun l ↦ h l : HashInput → Id HashOutput) = fun l ↦
      simulateQ f (Quantum.Sphincs.WithHash.hashQuery l) :=
    funext fun l ↦ (Quantum.Sphincs.WithHash.simulateQ_hashQuery f l).symm
  rw [e1, e2, ← Over.simulateQ_verify, ← Over.simulateQ_verify]
  exact Over.simulateQ_pureAnswers _ _

/-- **Verification over `pure ∘ h`** returns its evaluation with `h`. -/
theorem verify_pure (h : HashInput → HashOutput) (pk : PublicKey) (M : Message)
    (σ : Signature) :
    LeanSphincsOver.verify (m := m) (fun l ↦ pure (h l)) pk M σ =
      pure (LeanSphincsOver.verify (m := Id) (fun l ↦ h l) pk M σ) :=
  verify_eq_pure_of_hash (fun _ ↦ rfl) pk M σ

end Pure

/-! ## Inputs of the positions -/

/-- A table read through its first components (the honest values read only those). -/
def fstTab (v : QTable) : QTable :=
  fun p ↦ ((v p).1, 0)

theorem posInput_fstTab (S0 : MasterSeed) (v : QTable) (p : RawPos) :
    posInput S0 (fstTab v) p = posInput S0 v p := by
  cases p <;> rfl

theorem randomizer_fstTab (v : QTable) (M : Message) :
    (fstTab v).randomizer M = v.randomizer M :=
  rfl

theorem publicSeed_fstTab (v : QTable) : (fstTab v).publicSeed = v.publicSeed :=
  rfl

theorem root_fstTab (v : QTable) : (fstTab v).root = v.root :=
  rfl

theorem posInput_eq_decodeInput (S0 : MasterSeed) (v : QTable) (p : Pos) :
    posInput S0 v p.1 = Qrom.decodeInput (cellOf S0 p v) :=
  (Qrom.decodeInput_of_encodeInput_eq_some (encodeInput_posInput S0 v p)).symm

/-- **An input reads only the first components of lower rank.** -/
theorem posInput_congr_fst (S0 : MasterSeed) {v v' : QTable} (p : Pos)
    (h : ∀ q : Pos, q.1.rank < p.1.rank → (v q).1 = (v' q).1) :
    posInput S0 v p.1 = posInput S0 v' p.1 := by
  rw [← posInput_fstTab S0 v, ← posInput_fstTab S0 v', posInput_eq_decodeInput,
    posInput_eq_decodeInput,
    cellOf_congr S0 (v := fstTab v) (v' := fstTab v') fun q hq ↦
      congrArg (fun y ↦ (y, (0 : HashOutput))) (h q hq)]

/-- Distinct positions have distinct inputs. -/
theorem posInput_inj {S0 : MasterSeed} {v : QTable} {p q : Pos}
    (e : posInput S0 v p.1 = posInput S0 v q.1) : p = q :=
  (table S0).inj v (Option.some.inj ((encodeInput_posInput S0 v p).symm.trans
    ((congrArg Qrom.encodeInput e).trans (encodeInput_posInput S0 v q))))

/-- Only the secrets' inputs read `SK.seed`. -/
theorem posInput_seed (S0 S0' : MasterSeed) (v : QTable) {p : RawPos} (hs : ¬IsSecret p) :
    posInput S0 v p = posInput S0' v p := by
  cases p <;> first | exact (hs trivial).elim | rfl

theorem posInput_chainStart (S0 : MasterSeed) (v : QTable) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) :
    posInput S0 v (.chainStart l τ e i) = addressedHashInput v.publicSeed
      (keygenDomainFields (.oneTimeChain l τ e i)) (littleEndianBytes 32 S0) :=
  rfl

theorem posInput_forsSecret (S0 : MasterSeed) (v : QTable) (idx : Index) (κ : ForsTreeIndex)
    (s : ForsLeafIndex) :
    posInput S0 v (.forsSecret idx κ s) = addressedHashInput v.publicSeed
      (keygenDomainFields (.forsSecret idx κ s)) (littleEndianBytes 32 S0) :=
  rfl

theorem posInput_prfMsg (S0 : MasterSeed) (v : QTable) (M : Message) :
    posInput S0 v (.prfMsg M) = prfMessageInput v.prfKey v.publicSeed M :=
  rfl

/-- A secret's slot is a `PRF`, key expansion or `PRF_msg` slot. -/
theorem posSlot_ne_of_secret (v : QTable) {p : RawPos} (hs : IsSecret p)
    {s : Quantum.Sphincs.Slot} (h1 : ∀ d, s ≠ .prf d) (h2 : ∀ d, s ≠ .expand d)
    (h3 : ∀ M, s ≠ .prfMsg M) : posSlot v p ≠ s := by
  cases p <;>
    first
      | exact (hs : False).elim
      | exact (h1 _).symm
      | exact (h2 _).symm
      | exact (h3 _).symm

/-! ## The table of given secrets -/

/-- The value of a position given the values below: a secret's given value, else the hash of its
input (both `H_msg` calls at a digest cell). -/
def mkStep (h : HashInput → HashOutput) (prfKeyOut pkSeedOut : HashOutput)
    (sec : KeygenDomain → HashOutput) (rnd : Message → HashOutput) (v : QTable) :
    RawPos → HashOutput × HashOutput
  | .prfKey => (prfKeyOut, 0)
  | .publicSeed => (pkSeedOut, 0)
  | .chainStart l τ e i => (sec (.oneTimeChain l τ e i), 0)
  | .forsSecret idx κ s => (sec (.forsSecret idx κ s), 0)
  | .prfMsg message => (rnd message, 0)
  | .hmsg message => (h (posInput 0 v (.hmsg message)),
      h (messageDigestInput (v.randomizer message) v.publicSeed v.root message 1))
  | p => (h (posInput 0 v p), 0)

/-- **The table of given secrets**: `SK.prf`, the `PK.seed` output, the `PRF` secrets and the
randomizers given, every other position the hash of its honest input. -/
noncomputable def mkTable (h : HashInput → HashOutput) (prfKeyOut pkSeedOut : HashOutput)
    (sec : KeygenDomain → HashOutput) (rnd : Message → HashOutput) : QTable :=
  (measure fun p : Pos ↦ p.1.rank).wf.fix fun p ih ↦ mkStep h prfKeyOut pkSeedOut sec rnd
    (fun q ↦ @dite _ (q.1.rank < p.1.rank) (Classical.propDecidable _) (fun hq ↦ ih q hq)
      fun _ ↦ 0) p.1

section MkTable

variable (h : HashInput → HashOutput) (a b : HashOutput) (sec : KeygenDomain → HashOutput)
  (rnd : Message → HashOutput)

theorem mkStep_congr {v v' : QTable} (p : Pos)
    (hv : ∀ q : Pos, q.1.rank < p.1.rank → v q = v' q) :
    mkStep h a b sec rnd v p.1 = mkStep h a b sec rnd v' p.1 := by
  obtain ⟨p, hp⟩ := p
  have hI : posInput 0 v p = posInput 0 v' p :=
    posInput_congr_fst 0 ⟨p, hp⟩ fun q hq ↦ congrArg Prod.fst (hv q hq)
  have hc := two_le_chainLength
  cases p with
  | prfKey => rfl
  | publicSeed => rfl
  | chainStart => rfl
  | forsSecret => rfl
  | prfMsg => rfl
  | hmsg message =>
    have hR : v.randomizer message = v'.randomizer message :=
      QTable.dig_congr fun hq ↦
        hv ⟨_, hq⟩ (by show 1 < 2 + chainLength + layerHeight topLayer; omega)
    have hS : v.publicSeed = v'.publicSeed :=
      QTable.dig_congr fun hq ↦
        hv ⟨_, hq⟩ (by show 0 < 2 + chainLength + layerHeight topLayer; omega)
    have hroot : v.root = v'.root :=
      QTable.treeValue_congr (l := topLayer) (τ := 0) (level := layerHeight topLayer)
        (index := 0) fun q hq ↦ hv q hq
    show (h (posInput 0 v (.hmsg message)),
        h (messageDigestInput (v.randomizer message) v.publicSeed v.root message 1)) =
      (h (posInput 0 v' (.hmsg message)),
        h (messageDigestInput (v'.randomizer message) v'.publicSeed v'.root message 1))
    rw [hI, hR, hS, hroot]
  | chain => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI
  | leaf => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI
  | node => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI
  | forsLeaf => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI
  | forsNode => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI
  | forsRoots => exact congrArg (fun x ↦ (h x, (0 : HashOutput))) hI

theorem mkTable_eq (p : Pos) :
    mkTable h a b sec rnd p = mkStep h a b sec rnd (mkTable h a b sec rnd) p.1 :=
  (WellFounded.fix_eq _ _ p).trans (mkStep_congr h a b sec rnd p fun _ hq ↦ dite_eq_left hq)

theorem mkTable_prfKey (hp : RawPos.prfKey.InRange) :
    mkTable h a b sec rnd ⟨.prfKey, hp⟩ = (a, 0) :=
  mkTable_eq h a b sec rnd _

theorem mkTable_publicSeed (hp : RawPos.publicSeed.InRange) :
    mkTable h a b sec rnd ⟨.publicSeed, hp⟩ = (b, 0) :=
  mkTable_eq h a b sec rnd _

theorem mkTable_chainStart {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    (hp : (RawPos.chainStart l τ e i).InRange) :
    mkTable h a b sec rnd ⟨.chainStart l τ e i, hp⟩ = (sec (.oneTimeChain l τ e i), 0) :=
  mkTable_eq h a b sec rnd _

theorem mkTable_forsSecret {idx : Index} {κ : ForsTreeIndex} {s : ForsLeafIndex}
    (hp : (RawPos.forsSecret idx κ s).InRange) :
    mkTable h a b sec rnd ⟨.forsSecret idx κ s, hp⟩ = (sec (.forsSecret idx κ s), 0) :=
  mkTable_eq h a b sec rnd _

theorem mkTable_prfMsg {M : Message} (hp : (RawPos.prfMsg M).InRange) :
    mkTable h a b sec rnd ⟨.prfMsg M, hp⟩ = (rnd M, 0) :=
  mkTable_eq h a b sec rnd _

theorem prfKey_mkTable : (mkTable h a b sec rnd).prfKey = a :=
  ((mkTable h a b sec rnd).out_of_inRange (p := .prfKey) trivial).trans
    (congrArg Prod.fst (mkTable_prfKey h a b sec rnd trivial))

theorem publicSeed_mkTable : (mkTable h a b sec rnd).publicSeed = truncateHash b :=
  congrArg truncateHash (((mkTable h a b sec rnd).out_of_inRange (p := .publicSeed) trivial).trans
    (congrArg Prod.fst (mkTable_publicSeed h a b sec rnd trivial)))

theorem randomizer_mkTable (M : Message) :
    (mkTable h a b sec rnd).randomizer M = truncateHash (rnd M) :=
  congrArg truncateHash (((mkTable h a b sec rnd).out_of_inRange (p := .prfMsg M) trivial).trans
    (congrArg Prod.fst (mkTable_prfMsg h a b sec rnd trivial)))

/-- **The table of given secrets is honest.** -/
theorem honest_mkTable : Honest h (mkTable h a b sec rnd) where
  out p hs := by
    rw [mkTable_eq h a b sec rnd p]
    obtain ⟨p, hp⟩ := p
    cases p <;> first | exact absurd trivial hs | rfl
  call1 message := by
    rw [mkTable_eq h a b sec rnd (digPos message)]
    rfl

end MkTable

/-- The secrets of a table: the `PRF` outputs. -/
def secretOut (v : QTable) : KeygenDomain → HashOutput
  | .oneTimeChain l τ e i => v.out (.chainStart l τ e i)
  | .forsSecret idx κ s => v.out (.forsSecret idx κ s)

section Unique

variable {h : HashInput → HashOutput} {v : QTable}

/-- **An honest table is the table of its secrets** at the first components. -/
theorem fst_eq_mkTable_of_honest (hv : Honest h v) (p : Pos) :
    (v p).1 = (mkTable h (v.out .prfKey) (v.out .publicSeed) (secretOut v)
      (fun M ↦ v.out (.prfMsg M)) p).1 := by
  refine (measure fun p : Pos ↦ p.1.rank).wf.induction
    (C := fun p ↦ (v p).1 = (mkTable h (v.out .prfKey) (v.out .publicSeed) (secretOut v)
      (fun M ↦ v.out (.prfMsg M)) p).1) p fun p ih ↦ ?_
  by_cases hs : IsSecret p.1
  · rw [mkTable_eq]
    obtain ⟨p, hp⟩ := p
    cases p <;> first | exact (hs : False).elim | exact (v.out_of_inRange hp).symm
  · rw [hv.out p hs, (honest_mkTable h _ _ _ _).out p hs]
    exact congrArg h (posInput_congr_fst 0 p fun q hq ↦ ih q hq)

theorem fstTab_eq_mkTable_of_honest (hv : Honest h v) :
    fstTab v = fstTab (mkTable h (v.out .prfKey) (v.out .publicSeed) (secretOut v)
      (fun M ↦ v.out (.prfMsg M))) :=
  funext fun p ↦ congrArg (fun y ↦ (y, (0 : HashOutput))) (fst_eq_mkTable_of_honest hv p)

/-- **An honest table is the table of its secrets** at the digest cells. -/
theorem digest_eq_mkTable_of_honest (hv : Honest h v) (M : Message) :
    (v (digPos M)).2 = (mkTable h (v.out .prfKey) (v.out .publicSeed) (secretOut v)
      (fun M ↦ v.out (.prfMsg M)) (digPos M)).2 := by
  rw [hv.call1, (honest_mkTable h _ _ _ _).call1, ← randomizer_fstTab v, ← publicSeed_fstTab v,
    ← root_fstTab v, fstTab_eq_mkTable_of_honest hv, randomizer_fstTab, publicSeed_fstTab,
    root_fstTab]

/-- **An honest table is the table of its secrets**, its second components outside the digest
cells `0`. -/
theorem eq_mkTable_of_honest (hv : Honest h v)
    (h2 : ∀ p : Pos, (∀ M, p.1 ≠ .hmsg M) → (v p).2 = 0) :
    v = mkTable h (v.out .prfKey) (v.out .publicSeed) (secretOut v)
      (fun M ↦ v.out (.prfMsg M)) := by
  funext p
  refine Prod.ext (fst_eq_mkTable_of_honest hv p) ?_
  obtain ⟨p, hp⟩ := p
  cases p with
  | hmsg M => exact digest_eq_mkTable_of_honest hv M
  | _ =>
    rw [mkTable_eq]
    exact h2 _ fun _ e ↦ by cases e

end Unique

/-! ## Hashes answering an honest table -/

section Answers

variable {m : Type → Type} [Monad m] {h : HashInput → HashOutput} {S0 : MasterSeed}
  {v : QTable} {hash : HashInput → m HashOutput}

/-- The hash answers the secrets' inputs at `SK.seed = S0` by their values. -/
def AnswersSecrets (S0 : MasterSeed) (v : QTable) (hash : HashInput → m HashOutput) : Prop :=
  ∀ p : Pos, IsSecret p.1 → hash (posInput S0 v p.1) = pure (v p).1

/-- The hash answers every input other than the secrets' by `h`. -/
def AnswersElse (h : HashInput → HashOutput) (S0 : MasterSeed) (v : QTable)
    (hash : HashInput → m HashOutput) : Prop :=
  ∀ l, (∀ p : Pos, IsSecret p.1 → posInput S0 v p.1 ≠ l) → hash l = pure (h l)

theorem answersTable_of_honest (hv : Honest h v) (hS : AnswersSecrets S0 v hash)
    (hE : AnswersElse h S0 v hash) : AnswersTable S0 v hash := fun p hp ↦ by
  by_cases hs : IsSecret p
  · exact hS ⟨p, hp⟩ hs
  · rw [hE _ fun q hq e ↦ hs (by obtain rfl := posInput_inj (q := ⟨p, hp⟩) e; exact hq),
      posInput_seed S0 0 v hs]
    exact congrArg pure (hv.out ⟨p, hp⟩ hs).symm

theorem answersDigest_of_honest (hv : Honest h v) (hE : AnswersElse h S0 v hash) :
    AnswersDigest v hash := fun message ↦ by
  have hne : ∀ q : Pos, IsSecret q.1 → posInput S0 v q.1 ≠
      messageDigestInput (v.randomizer message) v.publicSeed v.root message 1 :=
    fun q hq e ↦ sphincs_slotInput_ne (v.expandedKey S0) v.root
      (slotInRange_posSlot v q) (s' := .hmsg (v.randomizer message) message 1) trivial
      (posSlot_ne_of_secret v hq (fun _ e' ↦ by cases e') (fun _ e' ↦ by cases e')
        fun _ e' ↦ by cases e') _ () e
  rw [hE _ hne]
  exact congrArg pure (hv.call1 message).symm

theorem answersEnc_of_honest (hE : AnswersElse h S0 v hash) : AnswersEnc v (cellHash h) hash :=
  fun l τ e message counter ↦ by
  have hne : ∀ q : Pos, IsSecret q.1 → posInput S0 v q.1 ≠
      addressedHashInput v.publicSeed (hashDomainFields (.encoding l τ e))
        (littleEndianBytes 16 message ++ bigEndianBytes 4 counter) :=
    fun q hq e' ↦ sphincs_slotInput_ne (v.expandedKey S0) v.root
      (slotInRange_posSlot v q) (s' := .enc l τ e) trivial
      (posSlot_ne_of_secret v hq (fun _ e'' ↦ by cases e'') (fun _ e'' ↦ by cases e'')
        fun _ e'' ↦ by cases e'') _ (message, counter) e'
  rw [hE _ hne]
  exact congrArg (fun x ↦ (pure (h x) : m HashOutput))
    (Qrom.decodeInput_of_encodeInput_eq_some (encodeInput_encCell _ _ _ _ _ _)).symm

variable [LawfulMonad m]

/-- **Key generation returns an honest table's public key**, over a hash answering its secrets
by the table and every other input by `h`. -/
theorem keygenFromSeed_eq_pure_of_honest (hv : Honest h v) (hS : AnswersSecrets S0 v hash)
    (hE : AnswersElse h S0 v hash) :
    LeanSphincsOver.keygenFromSeed hash S0 = pure (v.publicKey, S0) :=
  keygenFromSeed_eq_pure (answersTable_of_honest hv hS hE)

/-- **Signing returns an honest table's signature**, over a hash answering its secrets by the
table and every other input by `h`. -/
theorem sign_eq_pure_of_honest (hv : Honest h v) (hS : AnswersSecrets S0 v hash)
    (hE : AnswersElse h S0 v hash) (M : Message) :
    LeanSphincsOver.sign hash S0 M = pure (v.signature (cellHash h) M) :=
  sign_eq_pure (answersTable_of_honest hv hS hE) (answersDigest_of_honest hv hE)
    (answersEnc_of_honest hE) M

end Answers

/-! ## The table of a seed -/

/-- **The honest table of `SK.seed = S0` under `h`**: every secret the hash of its input. -/
noncomputable def seedTable (h : HashInput → HashOutput) (S0 : MasterSeed) : QTable :=
  mkTable h (h (keyDerivationInput S0 1)) (h (keyDerivationInput S0 0))
    (fun d ↦ h (addressedHashInput (truncateHash (h (keyDerivationInput S0 0)))
      (keygenDomainFields d) (littleEndianBytes 32 S0)))
    (fun M ↦ h (prfMessageInput (h (keyDerivationInput S0 1))
      (truncateHash (h (keyDerivationInput S0 0))) M))

theorem honest_seedTable (h : HashInput → HashOutput) (S0 : MasterSeed) :
    Honest h (seedTable h S0) :=
  honest_mkTable _ _ _ _ _

/-- Every secret of the seed's table is the hash of its input. -/
theorem seedTable_secret (h : HashInput → HashOutput) (S0 : MasterSeed) (p : Pos)
    (hs : IsSecret p.1) : (seedTable h S0 p).1 = h (posInput S0 (seedTable h S0) p.1) := by
  unfold seedTable
  obtain ⟨p, hp⟩ := p
  cases p with
  | prfKey =>
    rw [mkTable_prfKey]
    rfl
  | publicSeed =>
    rw [mkTable_publicSeed]
    rfl
  | chainStart l τ e i => rw [mkTable_chainStart, posInput_chainStart, publicSeed_mkTable]
  | forsSecret idx κ s => rw [mkTable_forsSecret, posInput_forsSecret, publicSeed_mkTable]
  | prfMsg M => rw [mkTable_prfMsg, posInput_prfMsg, prfKey_mkTable, publicSeed_mkTable]
  | _ => exact (hs : False).elim

section SeedTable

variable {m : Type → Type} [Monad m] [LawfulMonad m] {h : HashInput → HashOutput}
  {hash : HashInput → m HashOutput}

omit [LawfulMonad m] in
theorem answersSecrets_seedTable (hh : ∀ l, hash l = pure (h l)) (S0 : MasterSeed) :
    AnswersSecrets S0 (seedTable h S0) hash := fun p hs ↦ by
  rw [hh, seedTable_secret h S0 p hs]

/-- **Key generation over a pure hash** returns the seed's table's public key. -/
theorem keygenFromSeed_seedTable (hh : ∀ l, hash l = pure (h l)) (S0 : MasterSeed) :
    LeanSphincsOver.keygenFromSeed hash S0 = pure ((seedTable h S0).publicKey, S0) :=
  keygenFromSeed_eq_pure_of_honest (honest_seedTable h S0) (answersSecrets_seedTable hh S0)
    fun l _ ↦ hh l

/-- **Signing over a pure hash** returns the seed's table's signature. -/
theorem sign_seedTable (hh : ∀ l, hash l = pure (h l)) (S0 : MasterSeed) (M : Message) :
    LeanSphincsOver.sign hash S0 M = pure ((seedTable h S0).signature (cellHash h) M) :=
  sign_eq_pure_of_honest (honest_seedTable h S0) (answersSecrets_seedTable hh S0)
    (fun l _ ↦ hh l) M

end SeedTable

/-! ## Only digests matter -/

/-- A digest as a hash output: its low 128 bits. -/
def embedDigest (d : Digest) : HashOutput :=
  d.setWidth 256

theorem truncateHash_embedDigest (d : Digest) : truncateHash (embedDigest d) = d := by
  have hd : d.toNat < 2 ^ digestBits := d.isLt
  have h256 : d.toNat < 2 ^ 256 :=
    lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by simp [digestBits]))
  apply BitVec.eq_of_toNat_eq
  rw [truncateHash, embedDigest, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth,
    Nat.shiftRight_zero, Nat.mod_eq_of_lt h256, Nat.mod_eq_of_lt hd]

/-- The positions a non-secret input may read: all but `SK.prf`, the randomizers and the digest
cells. -/
def Plain : RawPos → Prop
  | .prfKey | .prfMsg _ | .hmsg _ => False
  | _ => True

theorem dig_congr_trunc {v v' : QTable} {p : RawPos}
    (h : ∀ hp : p.InRange, truncateHash (v ⟨p, hp⟩).1 = truncateHash (v' ⟨p, hp⟩).1) :
    v.dig p = v'.dig p := by
  unfold QTable.dig QTable.out
  split_ifs with hp
  · exact h hp
  · rfl

section DigCongr

variable {v v' : QTable}

theorem chainValue_congr_dig {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex}
    {j : ℕ} (hd : ∀ q : RawPos, Plain q → q.rank < 2 + j → v.dig q = v'.dig q) :
    v.chainValue l τ e i j = v'.chainValue l τ e i j := by
  cases j with
  | zero => exact hd (.chainStart l τ e i) trivial (by simp [RawPos.rank])
  | succ j =>
    simp only [QTable.chainValue]
    split_ifs with hj
    · exact hd (.chain l τ e i ⟨j, hj⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem treeValue_congr_dig {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (hd : ∀ q : RawPos, Plain q → q.rank < 2 + chainLength + level → v.dig q = v'.dig q) :
    v.treeValue l τ level index = v'.treeValue l τ level index := by
  cases level with
  | zero => exact hd (.leaf l τ (leafOfNat index)) trivial (by simp [RawPos.rank])
  | succ level =>
    simp only [QTable.treeValue]
    split_ifs with hl
    · exact hd (.node l τ ⟨level, hl.1⟩ ⟨index, hl.2⟩) trivial (by simp [RawPos.rank])
    · rfl

theorem forsValue_congr_dig {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hd : ∀ q : RawPos, Plain q → q.rank < 3 + height → v.dig q = v'.dig q) :
    v.forsValue idx κ height node = v'.forsValue idx κ height node := by
  cases height with
  | zero => exact hd (.forsLeaf idx κ (forsLeafOfNat node)) trivial (by simp [RawPos.rank])
  | succ height =>
    simp only [QTable.forsValue]
    split_ifs with hh
    · exact hd (.forsNode idx κ ⟨height, hh.1⟩ ⟨node, hh.2⟩) trivial (by simp [RawPos.rank])
    · rfl

/-- **A non-secret input reads only digests**: the plain positions' digests of lower rank, and
at a digest cell its randomizer. -/
theorem posInput_congr_dig (S0 : MasterSeed) {p : RawPos} (hs : ¬IsSecret p)
    (hd : ∀ q : RawPos, Plain q → q.rank < p.rank → v.dig q = v'.dig q)
    (hR : ∀ M, p = .hmsg M → v.randomizer M = v'.randomizer M) :
    posInput S0 v p = posInput S0 v' p := by
  have hc := two_le_chainLength
  have hS : 0 < p.rank → v.publicSeed = v'.publicSeed := fun h ↦ hd .publicSeed trivial h
  cases p with
  | chain l τ e i step =>
    have key : ∀ w : QTable, posInput S0 w (.chain l τ e i step) =
        slotInput (pubKey w.publicSeed) 0 (.chain l τ e i step)
          (w.chainValue l τ e i step.val) := fun _ ↦ rfl
    rw [key, key, hS (by show 0 < 2 + step.val; omega),
      chainValue_congr_dig (j := step.val) fun q hq hr ↦ hd q hq hr]
  | leaf l τ e =>
    have key : ∀ w : QTable, posInput S0 w (.leaf l τ e) =
        slotInput (pubKey w.publicSeed) 0 (.leaf l τ e) (w.endpoints l τ e) := fun _ ↦ rfl
    have he : v.endpoints l τ e = v'.endpoints l τ e := funext fun _ ↦
      chainValue_congr_dig (j := chainLength - 1) fun q hq hr ↦
        hd q hq (lt_of_lt_of_le hr (by show 2 + (chainLength - 1) ≤ 1 + chainLength; omega))
    rw [key, key, hS (by show 0 < 1 + chainLength; omega), he]
  | node l τ level index =>
    have key : ∀ w : QTable, posInput S0 w (.node l τ level index) =
        slotInput (pubKey w.publicSeed) 0 (.node l τ (level.val + 1) index.val)
          (w.treeValue l τ level.val (2 * index.val),
            w.treeValue l τ level.val (2 * index.val + 1)) := fun _ ↦ rfl
    have ht : ∀ j, v.treeValue l τ level.val j = v'.treeValue l τ level.val j := fun _ ↦
      treeValue_congr_dig fun q hq hr ↦ hd q hq hr
    rw [key, key, hS (by show 0 < 2 + chainLength + level.val; omega), ht, ht]
  | forsLeaf idx κ s =>
    have key : ∀ w : QTable, posInput S0 w (.forsLeaf idx κ s) =
        slotInput (pubKey w.publicSeed) 0 (.forsLeaf idx κ s) (w.forsSecret idx κ s) :=
      fun _ ↦ rfl
    have hf : v.forsSecret idx κ s = v'.forsSecret idx κ s :=
      hd (.forsSecret idx κ s) trivial (by show 1 < 2; omega)
    rw [key, key, hS (by show 0 < 2; omega), hf]
  | forsNode idx κ level node =>
    have key : ∀ w : QTable, posInput S0 w (.forsNode idx κ level node) =
        slotInput (pubKey w.publicSeed) 0 (.forsNode idx κ (level.val + 1) node.val)
          (w.forsValue idx κ level.val (2 * node.val),
            w.forsValue idx κ level.val (2 * node.val + 1)) := fun _ ↦ rfl
    have hf : ∀ j, v.forsValue idx κ level.val j = v'.forsValue idx κ level.val j := fun _ ↦
      forsValue_congr_dig fun q hq hr ↦ hd q hq hr
    rw [key, key, hS (by show 0 < 3 + level.val; omega), hf, hf]
  | forsRoots idx =>
    have key : ∀ w : QTable, posInput S0 w (.forsRoots idx) =
        slotInput (pubKey w.publicSeed) 0 (.forsRoots idx) (w.forsRoot idx) := fun _ ↦ rfl
    have hr : v.forsRoot idx = v'.forsRoot idx := funext fun _ ↦
      forsValue_congr_dig fun q hq hr ↦ hd q hq hr
    rw [key, key, hS (by show 0 < 3 + forsTreeHeight; omega), hr]
  | hmsg M =>
    have key : ∀ w : QTable, posInput S0 w (.hmsg M) =
        messageDigestInput (w.randomizer M) w.publicSeed w.root M 0 := fun _ ↦ rfl
    have hroot : v.root = v'.root :=
      treeValue_congr_dig (l := topLayer) (τ := 0) (level := layerHeight topLayer) (index := 0)
        fun q hq hr ↦ hd q hq hr
    rw [key, key, hS (by show 0 < 2 + chainLength + layerHeight topLayer; omega), hR M rfl,
      hroot]
  | _ => exact (hs trivial).elim

theorem publicSeed_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.publicSeed = v'.publicSeed :=
  hd .publicSeed trivial

theorem chainValue_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.chainValue = v'.chainValue := by
  funext l τ e i j
  exact chainValue_congr_dig fun q hq _ ↦ hd q hq

theorem treeValue_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.treeValue = v'.treeValue := by
  funext l τ level index
  exact treeValue_congr_dig fun q hq _ ↦ hd q hq

theorem forsValue_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.forsValue = v'.forsValue := by
  funext idx κ height node
  exact forsValue_congr_dig fun q hq _ ↦ hd q hq

theorem forsSecret_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.forsSecret = v'.forsSecret := by
  funext idx κ s
  exact hd (.forsSecret idx κ s) trivial

theorem forsKey_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.forsKey = v'.forsKey :=
  funext fun idx ↦ hd (.forsRoots idx) trivial

theorem root_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) : v.root = v'.root :=
  treeValue_congr_dig (l := topLayer) (τ := 0) (level := layerHeight topLayer) (index := 0)
    fun q hq _ ↦ hd q hq

theorem authPath_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.authPath = v'.authPath := by
  funext l τ e z
  exact treeValue_congr_dig fun q hq _ ↦ hd q hq

theorem forsOpening_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.forsOpening = v'.forsOpening := by
  funext idx lv
  unfold QTable.forsOpening
  rw [forsSecret_eq_of_dig hd, forsValue_eq_of_dig hd]

/-- **The public key reads only the plain digests.** -/
theorem publicKey_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q) :
    v.publicKey = v'.publicKey := by
  simp only [QTable.publicKey, publicSeed_eq_of_dig hd, root_eq_of_dig hd]

theorem selectFrom_eq_of_publicSeed (H : Qrom.HashDomain → HashOutput)
    (hS : v.publicSeed = v'.publicSeed) : v.selectFrom H = v'.selectFrom H := by
  funext l τ e message attempts
  induction attempts with
  | zero => rfl
  | succ k ih =>
    funext counter
    rw [QTable.selectFrom, QTable.selectFrom, QTable.encDigest, QTable.encDigest, hS, ih]

/-- **A signature reads only the plain digests**, the message's randomizer and its digest
cell. -/
theorem signature_eq_of_dig (hd : ∀ q : RawPos, Plain q → v.dig q = v'.dig q)
    (H : Qrom.HashDomain → HashOutput) {M : Message} (hR : v.randomizer M = v'.randomizer M)
    (hm : v (digPos M) = v' (digPos M)) : v.signature H M = v'.signature H M := by
  have hmd : v.messageDigest M = v'.messageDigest M := by
    unfold QTable.messageDigest QTable.digestOutput
    rw [hm]
  have hsel := selectFrom_eq_of_publicSeed H (publicSeed_eq_of_dig hd)
  simp only [QTable.signature, QTable.layerSig, QTable.layerSignature, QTable.select,
    QTable.layerMessage, QTable.treeRoot, QTable.index, QTable.leaves]
  rw [hsel, hmd, hR, chainValue_eq_of_dig hd, authPath_eq_of_dig hd, treeValue_eq_of_dig hd,
    forsKey_eq_of_dig hd, forsOpening_eq_of_dig hd]

end DigCongr

section MkTableTrunc

variable (h : HashInput → HashOutput) {a a' b b' : HashOutput}
  {sec sec' : KeygenDomain → HashOutput} {rnd rnd' : Message → HashOutput}

/-- **Two tables of secrets with the same digests** have the same plain digests. -/
theorem dig_mkTable_congr (hb : truncateHash b = truncateHash b')
    (hsec : ∀ d, truncateHash (sec d) = truncateHash (sec' d)) (p : RawPos) (hp : Plain p) :
    (mkTable h a b sec rnd).dig p = (mkTable h a' b' sec' rnd').dig p := by
  refine (measure RawPos.rank).wf.induction
    (C := fun p ↦ Plain p → (mkTable h a b sec rnd).dig p = (mkTable h a' b' sec' rnd').dig p)
    p (fun p ih hp ↦ ?_) hp
  refine dig_congr_trunc fun hin ↦ ?_
  by_cases hs : IsSecret p
  · cases p with
    | publicSeed =>
      rw [mkTable_publicSeed h a b sec rnd hin, mkTable_publicSeed h a' b' sec' rnd' hin]
      exact hb
    | chainStart l τ e i =>
      rw [mkTable_chainStart h a b sec rnd hin, mkTable_chainStart h a' b' sec' rnd' hin]
      exact hsec _
    | forsSecret idx κ s =>
      rw [mkTable_forsSecret h a b sec rnd hin, mkTable_forsSecret h a' b' sec' rnd' hin]
      exact hsec _
    | _ => first | exact (hs : False).elim | exact (hp : False).elim
  · exact congrArg truncateHash (((honest_mkTable h a b sec rnd).out ⟨p, hin⟩ hs).trans
      ((congrArg h (posInput_congr_dig 0 hs (fun q hq hr ↦ ih q hr hq)
        fun M e ↦ by subst e; exact (hp : False).elim)).trans
        ((honest_mkTable h a' b' sec' rnd').out ⟨p, hin⟩ hs).symm))

/-- **Two tables of secrets with the same digests** have the same digest cell at a message with
the same randomizer digest. -/
theorem digest_mkTable_congr (hb : truncateHash b = truncateHash b')
    (hsec : ∀ d, truncateHash (sec d) = truncateHash (sec' d)) (M : Message)
    (hrnd : truncateHash (rnd M) = truncateHash (rnd' M)) :
    mkTable h a b sec rnd (digPos M) = mkTable h a' b' sec' rnd' (digPos M) := by
  have hd : ∀ q : RawPos, Plain q →
      (mkTable h a b sec rnd).dig q = (mkTable h a' b' sec' rnd').dig q :=
    dig_mkTable_congr h hb hsec
  have hR : (mkTable h a b sec rnd).randomizer M = (mkTable h a' b' sec' rnd').randomizer M := by
    rw [randomizer_mkTable, randomizer_mkTable]
    exact hrnd
  refine Prod.ext ?_ ?_
  · rw [(honest_mkTable h a b sec rnd).out (digPos M) id,
      (honest_mkTable h a' b' sec' rnd').out (digPos M) id]
    exact congrArg h (posInput_congr_dig (p := .hmsg M) 0 id (fun q hq _ ↦ hd q hq)
      fun M' e ↦ by cases e; exact hR)
  · rw [(honest_mkTable h a b sec rnd).call1, (honest_mkTable h a' b' sec' rnd').call1, hR,
      publicSeed_eq_of_dig hd, root_eq_of_dig hd]

end MkTableTrunc

/-- **The table of given digests**: `PK.seed = P`, the `PRF` secrets `sec`, the randomizers
`rnd`, `SK.prf = 0`. -/
noncomputable def digTable (h : HashInput → HashOutput) (P : PublicParameter)
    (sec : KeygenDomain → Digest) (rnd : Message → Digest) : QTable :=
  mkTable h 0 (embedDigest P) (embedDigest ∘ sec) (embedDigest ∘ rnd)

section DigTable

variable (h : HashInput → HashOutput) (P : PublicParameter) (sec : KeygenDomain → Digest)
  (rnd : Message → Digest)

theorem honest_digTable : Honest h (digTable h P sec rnd) :=
  honest_mkTable _ _ _ _ _

theorem publicSeed_digTable : (digTable h P sec rnd).publicSeed = P :=
  (publicSeed_mkTable h _ _ _ _).trans (truncateHash_embedDigest P)

theorem randomizer_digTable (M : Message) : (digTable h P sec rnd).randomizer M = rnd M :=
  (randomizer_mkTable h _ _ _ _ M).trans (truncateHash_embedDigest _)

theorem dig_chainStart_digTable {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    {i : ChainIndex} (hp : (RawPos.chainStart l τ e i).InRange) :
    (digTable h P sec rnd).dig (.chainStart l τ e i) = sec (.oneTimeChain l τ e i) :=
  (congrArg truncateHash (((digTable h P sec rnd).out_of_inRange hp).trans
    (congrArg Prod.fst (mkTable_chainStart h _ _ _ _ hp)))).trans (truncateHash_embedDigest _)

theorem dig_forsSecret_digTable (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
    (digTable h P sec rnd).dig (.forsSecret idx κ s) = sec (.forsSecret idx κ s) :=
  (congrArg truncateHash (((digTable h P sec rnd).out_of_inRange (p := .forsSecret idx κ s)
    trivial).trans (congrArg Prod.fst (mkTable_forsSecret h _ _ _ _ trivial)))).trans
    (truncateHash_embedDigest _)

/-- **Randomizer locality**: the public key does not read the randomizers. -/
theorem publicKey_digTable_congr (rnd' : Message → Digest) :
    (digTable h P sec rnd).publicKey = (digTable h P sec rnd').publicKey :=
  publicKey_eq_of_dig (dig_mkTable_congr h rfl fun _ ↦ rfl)

/-- **Randomizer locality**: the signature of `M` reads only the randomizer of `M`. -/
theorem signature_digTable_congr {rnd' : Message → Digest} (H : Qrom.HashDomain → HashOutput)
    {M : Message} (hM : rnd M = rnd' M) :
    (digTable h P sec rnd).signature H M = (digTable h P sec rnd').signature H M := by
  have hd : ∀ q : RawPos, Plain q →
      (digTable h P sec rnd).dig q = (digTable h P sec rnd').dig q :=
    dig_mkTable_congr h rfl fun _ ↦ rfl
  refine signature_eq_of_dig hd H ?_ ?_
  · rw [randomizer_digTable, randomizer_digTable, hM]
  · exact digest_mkTable_congr h rfl (fun _ ↦ rfl) M
      (congrArg (fun d ↦ truncateHash (embedDigest d)) hM)

end DigTable

/-- The digests of a table's `PRF` secrets. -/
def secDig (v : QTable) : KeygenDomain → Digest
  | .oneTimeChain l τ e i => v.dig (.chainStart l τ e i)
  | .forsSecret idx κ s => v.dig (.forsSecret idx κ s)

section HonestDig

variable {h : HashInput → HashOutput} {v : QTable}

theorem dig_eq_digTable_of_honest (hv : Honest h v) (q : RawPos) (hq : Plain q) :
    v.dig q = (digTable h v.publicSeed (secDig v) v.randomizer).dig q := by
  refine (dig_congr_trunc fun hp ↦
    congrArg truncateHash (fst_eq_mkTable_of_honest hv ⟨q, hp⟩)).trans ?_
  refine dig_mkTable_congr h (truncateHash_embedDigest _).symm (fun d ↦ ?_) q hq
  cases d <;> exact (truncateHash_embedDigest _).symm

theorem digPos_eq_digTable_of_honest (hv : Honest h v) (M : Message) :
    v (digPos M) = digTable h v.publicSeed (secDig v) v.randomizer (digPos M) := by
  refine (Prod.ext (fst_eq_mkTable_of_honest hv _) (digest_eq_mkTable_of_honest hv M)).trans ?_
  refine digest_mkTable_congr h (truncateHash_embedDigest _).symm (fun d ↦ ?_) M
    (truncateHash_embedDigest _).symm
  cases d <;> exact (truncateHash_embedDigest _).symm

/-- **Only digests matter**: an honest table has the public key of the table of its digests. -/
theorem publicKey_eq_digTable_of_honest (hv : Honest h v) :
    v.publicKey = (digTable h v.publicSeed (secDig v) v.randomizer).publicKey :=
  publicKey_eq_of_dig (dig_eq_digTable_of_honest hv)

/-- **Only digests matter**: an honest table has the signatures of the table of its digests. -/
theorem signature_eq_digTable_of_honest (hv : Honest h v) (H : Qrom.HashDomain → HashOutput)
    (M : Message) :
    v.signature H M = (digTable h v.publicSeed (secDig v) v.randomizer).signature H M :=
  signature_eq_of_dig (dig_eq_digTable_of_honest hv) H
    (randomizer_digTable h _ _ _ M).symm (digPos_eq_digTable_of_honest hv M)

end HonestDig

/-! ## The routed signer -/

/-- The input of a secret position under `SK.seed = 0`, `SK.prf = 0` and `PK.seed = P` (no table
read). -/
def secInput (P : PublicParameter) : RawPos → HashInput
  | .prfKey => keyDerivationInput 0 1
  | .publicSeed => keyDerivationInput 0 0
  | .chainStart l τ e i =>
      addressedHashInput P (keygenDomainFields (.oneTimeChain l τ e i))
        (littleEndianBytes 32 (0 : MasterSeed))
  | .forsSecret idx κ s =>
      addressedHashInput P (keygenDomainFields (.forsSecret idx κ s))
        (littleEndianBytes 32 (0 : MasterSeed))
  | .prfMsg M => prfMessageInput 0 P M
  | _ => []

/-- The routed answer at a secret position: `SK.prf = 0`, the `PK.seed` output `P`, the `PRF`
secrets from `sec`, the randomizers from `rnd`. -/
def secAnswer {m : Type → Type} [Monad m] (P : PublicParameter) (sec : KeygenDomain → m Digest)
    (rnd : Message → m Digest) : RawPos → m HashOutput
  | .prfKey => pure 0
  | .publicSeed => pure (embedDigest P)
  | .chainStart l τ e i => embedDigest <$> sec (.oneTimeChain l τ e i)
  | .forsSecret idx κ s => embedDigest <$> sec (.forsSecret idx κ s)
  | .prfMsg M => embedDigest <$> rnd M
  | _ => pure 0

/-- **The routed hash**: the inputs of the secret positions in use under `SK.seed = 0`,
`SK.prf = 0` and `PK.seed = P` answered by the routed secrets, every other input by `hash`. -/
noncomputable def routeHash {m : Type → Type} [Monad m] (P : PublicParameter)
    (sec : KeygenDomain → m Digest) (rnd : Message → m Digest) (hash : HashInput → m HashOutput)
    (l : HashInput) : m HashOutput :=
  @dite _ (∃ p : Pos, IsSecret p.1 ∧ secInput P p.1 = l) (Classical.propDecidable _)
    (fun hx ↦ secAnswer P sec rnd hx.choose.1) fun _ ↦ hash l

theorem prfKey_digTable (h : HashInput → HashOutput) (P : PublicParameter)
    (s : KeygenDomain → Digest) (r : Message → Digest) : (digTable h P s r).prfKey = 0 :=
  prfKey_mkTable h _ _ _ _

/-- A secret's input is its routed input when `PK.seed = P` and `SK.prf = 0`. -/
theorem posInput_eq_secInput {P : PublicParameter} (v : QTable) (hP : v.publicSeed = P)
    (hK : v.prfKey = 0) {p : RawPos} (hs : IsSecret p) : posInput 0 v p = secInput P p := by
  cases p with
  | prfKey => rfl
  | publicSeed => rfl
  | chainStart l τ e i =>
    exact (posInput_chainStart 0 v l τ e i).trans
      (congrArg (fun P' ↦ addressedHashInput P' (keygenDomainFields (.oneTimeChain l τ e i))
        (littleEndianBytes 32 (0 : MasterSeed))) hP)
  | forsSecret idx κ s =>
    exact (posInput_forsSecret 0 v idx κ s).trans
      (congrArg (fun P' ↦ addressedHashInput P' (keygenDomainFields (.forsSecret idx κ s))
        (littleEndianBytes 32 (0 : MasterSeed))) hP)
  | prfMsg M =>
    exact (posInput_prfMsg 0 v M).trans (congrArg₂ (fun K P' ↦ prfMessageInput K P' M) hK hP)
  | _ => exact (hs : False).elim

/-- Distinct secret positions have distinct routed inputs. -/
theorem secInput_inj (P : PublicParameter) {p q : Pos} (hp : IsSecret p.1) (hq : IsSecret q.1)
    (e : secInput P p.1 = secInput P q.1) : p = q := by
  let v := digTable (fun _ ↦ 0) P (fun _ ↦ 0) (fun _ ↦ 0)
  have hP : v.publicSeed = P := publicSeed_digTable _ _ _ _
  have hK : v.prfKey = 0 := prfKey_digTable _ _ _ _
  exact posInput_inj (S0 := 0) (v := v)
    ((posInput_eq_secInput v hP hK hp).trans (e.trans (posInput_eq_secInput v hP hK hq).symm))

theorem simulateQ_secAnswer {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] (impl : QueryImpl O n) (P : PublicParameter)
    (sec : KeygenDomain → OracleComp O Digest) (rnd : Message → OracleComp O Digest)
    (p : RawPos) :
    simulateQ impl (secAnswer P sec rnd p) =
      secAnswer P (fun d ↦ simulateQ impl (sec d)) (fun M ↦ simulateQ impl (rnd M)) p := by
  cases p <;> first | exact simulateQ_pure impl _ | exact simulateQ_map impl _ _

/-- **The routed hash**, its oracles answered by `impl`, routes the answered sources. -/
theorem simulateQ_routeHash {ι : Type} {O : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n]
    [LawfulMonad n] (impl : QueryImpl O n) (P : PublicParameter)
    (sec : KeygenDomain → OracleComp O Digest) (rnd : Message → OracleComp O Digest)
    (hash : HashInput → OracleComp O HashOutput) (l : HashInput) :
    simulateQ impl (routeHash P sec rnd hash l) =
      routeHash P (fun d ↦ simulateQ impl (sec d)) (fun M ↦ simulateQ impl (rnd M))
        (fun l ↦ simulateQ impl (hash l)) l := by
  unfold routeHash
  by_cases hx : ∃ p : Pos, IsSecret p.1 ∧ secInput P p.1 = l
  · rw [dite_eq_left hx, dite_eq_left hx]
    exact simulateQ_secAnswer impl P sec rnd _
  · rw [dite_eq_right hx, dite_eq_right hx]

section Route

variable {m : Type → Type} [Monad m] [LawfulMonad m] {P : PublicParameter}
  {sec : KeygenDomain → m Digest} {rnd : Message → m Digest} {hash : HashInput → m HashOutput}
  {h : HashInput → HashOutput} {s : KeygenDomain → Digest} {r : Message → Digest}

theorem secAnswer_eq (hs : ∀ d, sec d = pure (s d)) (hr : ∀ M, rnd M = pure (r M)) (p : Pos)
    (hsec : IsSecret p.1) : secAnswer P sec rnd p.1 = pure (digTable h P s r p).1 := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | prfKey =>
    rw [show digTable h P s r ⟨.prfKey, hp⟩ = (0, 0) from mkTable_prfKey h _ _ _ _ hp]
    rfl
  | publicSeed =>
    rw [show digTable h P s r ⟨.publicSeed, hp⟩ = (embedDigest P, 0) from
      mkTable_publicSeed h _ _ _ _ hp]
    rfl
  | chainStart l τ e i =>
    rw [show digTable h P s r ⟨.chainStart l τ e i, hp⟩ =
      (embedDigest (s (.oneTimeChain l τ e i)), 0) from mkTable_chainStart h _ _ _ _ hp]
    exact (congrArg (embedDigest <$> ·) (hs _)).trans (map_pure _ _)
  | forsSecret idx κ s' =>
    rw [show digTable h P s r ⟨.forsSecret idx κ s', hp⟩ =
      (embedDigest (s (.forsSecret idx κ s')), 0) from mkTable_forsSecret h _ _ _ _ hp]
    exact (congrArg (embedDigest <$> ·) (hs _)).trans (map_pure _ _)
  | prfMsg M =>
    rw [show digTable h P s r ⟨.prfMsg M, hp⟩ = (embedDigest (r M), 0) from
      mkTable_prfMsg h _ _ _ _ hp]
    exact (congrArg (embedDigest <$> ·) (hr _)).trans (map_pure _ _)
  | _ => exact (hsec : False).elim

theorem answersSecrets_routeHash (hs : ∀ d, sec d = pure (s d)) (hr : ∀ M, rnd M = pure (r M)) :
    AnswersSecrets 0 (digTable h P s r) (routeHash P sec rnd hash) := fun p hsec ↦ by
  rw [posInput_eq_secInput (digTable h P s r) (publicSeed_digTable h P s r)
    (prfKey_digTable h P s r) hsec]
  have hx : ∃ q : Pos, IsSecret q.1 ∧ secInput P q.1 = secInput P p.1 := ⟨p, hsec, rfl⟩
  unfold routeHash
  rw [dite_eq_left hx, secInput_inj P hx.choose_spec.1 hsec hx.choose_spec.2]
  exact secAnswer_eq hs hr p hsec

omit [LawfulMonad m] in
theorem answersElse_routeHash (hh : ∀ l, hash l = pure (h l)) :
    AnswersElse h 0 (digTable h P s r) (routeHash P sec rnd hash) := fun l hl ↦ by
  unfold routeHash
  refine (dite_eq_right ?_).trans (hh l)
  rintro ⟨q, hq, e⟩
  exact hl q hq ((posInput_eq_secInput (digTable h P s r) (publicSeed_digTable h P s r)
    (prfKey_digTable h P s r) hq).trans e)

/-- **The routed signer** returns the signature of the table of the routed digests. -/
theorem sign_routeHash (hs : ∀ d, sec d = pure (s d)) (hr : ∀ M, rnd M = pure (r M))
    (hh : ∀ l, hash l = pure (h l)) (M : Message) :
    LeanSphincsOver.sign (routeHash P sec rnd hash) 0 M =
      pure ((digTable h P s r).signature (cellHash h) M) :=
  sign_eq_pure_of_honest (honest_digTable h P s r) (answersSecrets_routeHash hs hr)
    (answersElse_routeHash hh) M

/-- **Routed key generation** returns the public key of the table of the routed digests. -/
theorem keygenFromSeed_routeHash (hs : ∀ d, sec d = pure (s d)) (hr : ∀ M, rnd M = pure (r M))
    (hh : ∀ l, hash l = pure (h l)) :
    LeanSphincsOver.keygenFromSeed (routeHash P sec rnd hash) 0 =
      pure ((digTable h P s r).publicKey, 0) :=
  keygenFromSeed_eq_pure_of_honest (honest_digTable h P s r) (answersSecrets_routeHash hs hr)
    (answersElse_routeHash hh)

end Route

/-! ## The truncation law -/

/-- A hash output as its high 128 bits and its digest. -/
def hashSplit : HashOutput ≃ BitVec 128 × Digest :=
  BitVec.equivFin.toEquiv.trans ((finCongr (by simp only [digestBits, ← pow_add])).trans
    (finProdFinEquiv.symm.trans
      (Equiv.prodCongr BitVec.equivFin.toEquiv.symm BitVec.equivFin.toEquiv.symm)))

theorem hashSplit_snd (o : HashOutput) : (hashSplit o).2 = truncateHash o := by
  apply BitVec.eq_of_toNat_eq
  change BitVec.toNat o % 2 ^ digestBits = _
  rw [truncateHash, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- Summing over a product's second factor through an equivalence. -/
theorem sum_comp_snd_equiv {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (e : α ≃ β × γ) (Φ : γ → M) :
    ∑ a, Φ (e a).2 = Fintype.card β • ∑ c, Φ c := by
  calc ∑ a, Φ (e a).2 = ∑ p : β × γ, Φ p.2 := e.sum_comp fun p ↦ Φ p.2
    _ = ∑ _b : β, ∑ c, Φ c := Fintype.sum_prod_type _
    _ = Fintype.card β • ∑ c, Φ c := by rw [Finset.sum_const, Finset.card_univ]

/-- **The truncation law**: every digest is the truncation of `2^128` hash outputs. -/
theorem sum_truncateHash {M : Type*} [AddCommMonoid M] (Φ : Digest → M) :
    ∑ o : HashOutput, Φ (truncateHash o) = (2 ^ 128 : ℕ) • ∑ d : Digest, Φ d := by
  have hc : Fintype.card (BitVec 128) = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  calc ∑ o : HashOutput, Φ (truncateHash o) = ∑ o : HashOutput, Φ (hashSplit o).2 :=
        Finset.sum_congr rfl fun o _ ↦ by rw [hashSplit_snd]
    _ = Fintype.card (BitVec 128) • ∑ d : Digest, Φ d := sum_comp_snd_equiv hashSplit Φ
    _ = (2 ^ 128 : ℕ) • ∑ d : Digest, Φ d := by rw [hc]

/-! ## The real scheme at a fixed table -/

/-- **The honest table of `SK.seed = S0` at the table `tab` of the world `W`.** -/
noncomputable def realTable (W : OracleWorld) (tab : W.Tab) (S0 : MasterSeed) : QTable :=
  seedTable (W.hashOf tab) S0

variable (W : OracleWorld) (tab : W.Tab)

/-- **Key generation at a fixed table** returns the real table's public key. -/
theorem simulateQ_generateKeys_eager (S0 : MasterSeed) :
    simulateQ (W.eager tab) ((sphincsOver W.hash).generateKeys S0) =
      pure ((realTable W tab S0).publicKey, S0) := by
  change simulateQ (W.eager tab) (LeanSphincsOver.keygenFromSeed W.hash S0) = _
  rw [Over.simulateQ_keygenFromSeed]
  exact keygenFromSeed_seedTable (W.simulateQ_hash tab) S0

/-- **Signing at a fixed table** returns the real table's signature. -/
theorem simulateQ_sign_eager (S0 : MasterSeed) (M : Message) :
    simulateQ (W.eager tab) ((sphincsOver W.hash).sign S0 M) =
      pure ((realTable W tab S0).signature (cellHash (W.hashOf tab)) M) := by
  change simulateQ (W.eager tab) (LeanSphincsOver.sign W.hash S0 M) = _
  rw [Over.simulateQ_sign]
  exact sign_seedTable (W.simulateQ_hash tab) S0 M

/-- **Verification at a fixed table** is the evaluation of the verifier with the table's hash. -/
theorem simulateQ_verify_eager (pk : PublicKey) (forgery : Forgery) :
    simulateQ (W.eager tab) ((sphincsOver W.hash).verify pk forgery) =
      pure (LeanSphincsOver.verify (m := Id) (fun l ↦ W.hashOf tab l) pk forgery.message
        forgery.signature) := by
  change simulateQ (W.eager tab)
    (LeanSphincsOver.verify W.hash pk forgery.message forgery.signature) = _
  rw [Over.simulateQ_verify]
  exact verify_eq_pure_of_hash (W.simulateQ_hash tab) _ _ _

end Quantum.StdModel.Sphincs

end
