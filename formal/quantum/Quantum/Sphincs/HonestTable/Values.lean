module

public import Quantum.Sphincs.Keccak
public import Quantum.SufCma.Trace

@[expose] public section

/-!
# leanSPHINCS's honest computations and values

For a fixed sponge view, the keys `t = (h, k, k')` and the inner permutation `π` (so
`φ = spongePerm t π`), and the secret key `SK.seed`, leanSPHINCS's key generation and signing are
deterministic classical computations.

* `WithHash`: the statement's algorithms (`Sphincs.Verification`, `Sphincs.KeyGenerationAndSigning`)
  with the hash a parameter `H : HashInput → m HashOutput` instead of Keccak-256 over `π`, function
  for function; at `H = keccakHash π` they are the statement's (`WithHash.sign_keccakHash`, ...,
  definitionally). `WithHash.simulateQ_sign` (and one such lemma per algorithm): answering the
  hash-query form (`H = hashQuery`) by an implementation `impl` is the form at `H = impl`. So the
  statement's scheme is the hash-query scheme `schemeWithHash` over `π`
  (`overPermutation_schemeWithHash`; `simulateQ_schemeHash_sign`, ...), and over `statePerm φ` it
  returns what `honestEval t π` returns (`simulateQ_sign`, ...), whose reads
  `Quantum.SufCma.honestEval_congr` controls (`honestEval_congr_sign`, `honestEval_congr_keygen`).
* `HonestTable`: the keys, `π` and `SK.seed`. Its values (`chainValue`, `treeValue`, `forsSecret`,
  `forsValue`, `forsKey`, `randomizer`, `digestOutput`, `select`, `signature`) are functions, never
  an enumeration; `eval_keygen`, `eval_sign`: they are what key generation and signing return, so
  `simulateQ_generateKeys_eq`, `simulateQ_sign_eq`: the statement's algorithms return them.
* `layerMessage idx l`: what the key `K_l(idx)` signs in every signature of index `idx`: the FORS
  key of `idx` at the bottom, the root of the tree below above it.
-/

open OracleComp OracleSpec
open Quantum.Sponge Sphincs Common Common.SufCma
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed ChainStep
  WinternitzDigit chainLength littleEndianBytes truncateHash digestsPayload)
open HashSig.OverPermutation (keccakHash sequenceFin walkChain foldPath nodePayload)
open Sphincs.KeyGenerationAndSigning (ExpandedKey levelNode merkleLevelsFrom merkleLevels
  layerSignatures keyDerivationInput)
open Quantum.Xmss (X Z)
open Quantum.SufCma (spongeOut statePerm honestEval readHash)
open LeanVM.Semantics (KeccakState)

namespace Quantum.Sphincs

/-! ## The algorithms with the hash a parameter -/

namespace WithHash

section Algorithms

variable {m : Type → Type} [Monad m] (H : HashInput → m HashOutput)

/-- `Trunc_16(H(PK.seed ‖ ADRS ‖ M))` at an address. -/
def addressedHash (publicSeed : PublicParameter) (address : Address) (payload : HashInput) :
    m Digest := do
  return truncateHash (← H (addressedHashInput publicSeed address payload))

/-- `F`, `H` and `T_l` at a hash domain's address. -/
abbrev tweakableHash (publicSeed : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  addressedHash H publicSeed (hashDomainFields domain) payload

/-- Chain `i` of the one-time key `(layer, tree, leaf)`. -/
def chainWalk (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) : ℕ → ℕ → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash H publicSeed (.chain layer tree leaf chainIndex step) (littleEndianBytes 16 value)

/-- The verifier's half of a chain. -/
def recoverChain (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    m Digest :=
  chainWalk H publicSeed layer tree leaf chainIndex digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf. -/
def leafHash (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash H publicSeed (.leaf layer tree leaf) (digestsPayload endpoints)

/-- `Enc(K, M, c)`, decoded. -/
def encode (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    m (Option Encoding) := do
  let digest ← tweakableHash H publicSeed (.encoding layer tree leaf)
    (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- The leaf a claimed one-time signature recovers. -/
def otsLeaf (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode H publicSeed layer tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain H publicSeed layer tree leaf chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash H publicSeed layer tree leaf endpoints
  return some value

/-- Fold a leaf value and a path into its tree's root. -/
def treeFold (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : ℕ → Digest) : ℕ → Digest → m Digest :=
  foldPath
    (fun level nodeIndex ↦ tweakableHash H publicSeed (.node layer tree (level + 1) nodeIndex))
    leaf.val path

/-- A FORS leaf. -/
def forsLeafHash (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (secret : Digest) : m Digest :=
  tweakableHash H publicSeed (.forsLeaf index forsTree leaf) (littleEndianBytes 16 secret)

/-- The root of a FORS tree an opening reaches. -/
def forsTreeRecover (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) : m Digest := do
  let value ← forsLeafHash H publicSeed index forsTree leaf opening.secret
  foldPath
    (fun level node ↦ tweakableHash H publicSeed (.forsNode index forsTree (level + 1) node))
    leaf.val (fun level ↦ if h : level < forsTreeHeight then opening.path ⟨level, h⟩ else 0)
    forsTreeHeight value

/-- `T_k` of the roots. -/
def forsPublicKey (publicSeed : PublicParameter) (index : Index)
    (roots : ForsTreeIndex → Digest) : m Digest :=
  tweakableHash H publicSeed (.forsRoots index) (digestsPayload roots)

/-- The FORS public key an opening reaches. -/
def forsRecover (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    m Digest := do
  let roots ← sequenceFin fun forsTree =>
    forsTreeRecover H publicSeed index forsTree (leaves forsTree) (opening forsTree)
  forsPublicKey H publicSeed index roots

/-- Digest call `i`. -/
def messageDigestCall (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) (call : DigestCall) : m HashOutput :=
  H (messageDigestInput randomizer publicSeed root message call)

/-- `H_msg(R, PK.seed, PK.root, M)`. -/
def messageDigest (publicKey : PublicKey) (randomizer : Randomizer) (message : Message) :
    m MessageDigest := do
  let outputs ← sequenceFin fun call =>
    messageDigestCall H randomizer publicKey.publicSeed publicKey.root message call
  return truncateMessageDigest outputs

/-- The walk up the hypertree. -/
def verifyLayers (publicSeed : PublicParameter) (index : Index) (signature : Signature) :
    ℕ → Digest → m (Option Digest)
  | 0, _ => pure none
  | layersLeft + 1, message => do
      if hlayer : layersLeft < layerCount then
        let layer : Layer := ⟨layerCount - 1 - layersLeft, by omega⟩
        let tree := treeOfIndex layer index
        let leaf := leafOfIndex layer index
        let some value ← otsLeaf H publicSeed layer tree leaf message
            (signature.layers layer).counter (signature.layers layer).chainValues
          | return none
        let root ← treeFold H publicSeed layer tree leaf (Verification.layerPath signature layer)
          (layerHeight layer) value
        if layersLeft = 0 then
          return some root
        else
          verifyLayers publicSeed index signature layersLeft root
      else
        pure none

/-- `Ver(pk, m, σ)`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest H publicKey signature.randomizer message
  let index := digestIndex digest
  let forsKey ← forsRecover H publicKey.publicSeed index (digestForsLeaves digest)
    signature.forsOpening
  let some root ← verifyLayers H publicKey.publicSeed index signature layerCount forsKey
    | return false
  return decide (root = publicKey.root)

/-- `SK.prf`, then `PK.seed`. -/
def expandKey (secretSeed : SecretKey) : m ExpandedKey := do
  let secretPrfKey ← H (keyDerivationInput secretSeed 1)
  let publicSeedOutput ← H (keyDerivationInput secretSeed 0)
  return ⟨secretSeed, secretPrfKey, truncateHash publicSeedOutput⟩

/-- A secret, one `PRF` call on `SK.seed`. -/
def prf (key : ExpandedKey) (domain : KeygenDomain) : m Digest :=
  addressedHash H key.publicSeed (keygenDomainFields domain) (littleEndianBytes 32 key.secretSeed)

/-- `PRF_msg`. -/
def prfMessage (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    m Randomizer := do
  return truncateHash (← H (prfMessageInput secretPrfKey optionalRandomness message))

/-- The chain starts of a one-time key. -/
def otsSecrets (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chainIndex ↦ prf H key (.oneTimeChain layer tree leaf chainIndex)

/-- The leaf of a one-time key from its secrets. -/
def otsPublicLeaf (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m Digest := do
  let secrets ← otsSecrets H key layer tree leaf
  let endpoints ← sequenceFin fun chainIndex =>
    chainWalk H key.publicSeed layer tree leaf chainIndex 0 (chainLength - 1) (secrets chainIndex)
  leafHash H key.publicSeed layer tree leaf endpoints

/-- The counter search from `counter`, at most `attempts` counters. -/
def otsSignFrom (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : ℕ → ℕ → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode H key.publicSeed layer tree leaf message
          (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets H key layer tree leaf
          let values ← sequenceFin fun chainIndex =>
            chainWalk H key.publicSeed layer tree leaf chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom key layer tree leaf message attempts (counter + 1)

/-- The one-time signature. -/
def otsSign (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom H key layer tree leaf message encodingAttemptLimit 0

/-- The levels of a tree of the hypertree. -/
def treeLevels (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    m (List (List Digest)) := do
  let leaves ← (List.range (2 ^ layerHeight layer)).mapM fun leaf ↦
    otsPublicLeaf H key layer tree (leafOfNat leaf)
  merkleLevels
    (fun height nodeIndex ↦ tweakableHash H key.publicSeed (.node layer tree height nodeIndex))
    leaves (layerHeight layer)

/-- The secret of a FORS leaf. -/
def forsSecret (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m Digest :=
  prf H key (.forsSecret index forsTree leaf)

/-- A FORS tree built once: its root and its opening at `leaf`. -/
def forsTreeOpen (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m (Digest × ForsTreeOpening) := do
  let secrets ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsSecret H key index forsTree (forsLeafOfNat s)
  let leafHashes ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsLeafHash H key.publicSeed index forsTree (forsLeafOfNat s) (secrets.getD s 0)
  let levels ← merkleLevels
    (fun height node ↦ tweakableHash H key.publicSeed (.forsNode index forsTree height node))
    leafHashes forsTreeHeight
  return (levelNode levels forsTreeHeight 0,
    ⟨secrets.getD leaf.val 0, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩)

/-- The FORS instance built once: its key and its opening. -/
def forsOpen (key : ExpandedKey) (index : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    m (Digest × (ForsTreeIndex → ForsTreeOpening)) := do
  let trees ← sequenceFin fun forsTree => forsTreeOpen H key index forsTree (leaves forsTree)
  let forsKey ← forsPublicKey H key.publicSeed index fun forsTree => (trees forsTree).1
  return (forsKey, fun forsTree => (trees forsTree).2)

/-- The public key and the top tree's levels. -/
def keygenInternal (key : ExpandedKey) : m (PublicKey × List (List Digest)) := do
  let top ← treeLevels H key topLayer 0
  return (⟨key.publicSeed, levelNode top (layerHeight topLayer) 0⟩, top)

/-- `Gen`. -/
def keygenFromSeed (secretSeed : SecretKey) : m (PublicKey × SecretKey) := do
  let key ← expandKey H secretSeed
  let (publicKey, _) ← keygenInternal H key
  return (publicKey, secretSeed)

/-- Layer `l`'s one-time signature and its tree's root. -/
def signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index) (layer : Layer)
    (message : Digest) : m (Option (LayerSignature layer × Digest)) := do
  let tree := treeOfIndex layer index
  let leaf := leafOfIndex layer index
  let some (counter, values) ← otsSign H key layer tree leaf message | return none
  let levels ← if layer = topLayer then pure top else treeLevels H key layer tree
  return some (⟨counter, values, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩,
    levelNode levels (layerHeight layer) 0)

/-- `slh_sign_internal`, deterministic. -/
def signWithExpandedKey (key : ExpandedKey) (message : Message) : m (Option Signature) := do
  let (publicKey, top) ← keygenInternal H key
  let randomizer ← prfMessage H key.secretPrfKey key.publicSeed message
  let digest ← messageDigest H publicKey randomizer message
  let index := digestIndex digest
  let (forsKey, forsOpening) ← forsOpen H key index (digestForsLeaves digest)
  let some (bottom, bottomRoot) ← signLayer H key top index 0 forsKey | return none
  let some (middle, middleRoot) ← signLayer H key top index 1 bottomRoot | return none
  let some (topSignature, _) ← signLayer H key top index 2 middleRoot | return none
  return some ⟨randomizer, forsOpening, layerSignatures bottom middle topSignature⟩

/-- `Sign`. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let key ← expandKey H secretKey
  signWithExpandedKey H key message

end Algorithms

/-! ### At Keccak-256 over `π`, the statement's algorithms -/

section Keccak

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

theorem keygenFromSeed_keccakHash (secretSeed : SecretKey) :
    keygenFromSeed (keccakHash π) secretSeed =
      KeyGenerationAndSigning.keygenFromSeed π secretSeed :=
  rfl

theorem otsSignFrom_keccakHash (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) : ∀ attempts counter : ℕ,
      otsSignFrom (keccakHash π) key layer tree leaf message attempts counter =
        KeyGenerationAndSigning.otsSignFrom π key layer tree leaf message attempts counter
  | 0, _ => rfl
  | attempts + 1, counter => by
    rw [otsSignFrom, KeyGenerationAndSigning.otsSignFrom]
    refine congrArg (_ >>= ·) (funext fun x ↦ ?_)
    cases x with
    | none => exact otsSignFrom_keccakHash key layer tree leaf message attempts (counter + 1)
    | some encoding => rfl

theorem signLayer_keccakHash (key : ExpandedKey) (top : List (List Digest)) (index : Index)
    (layer : Layer) (message : Digest) :
    signLayer (keccakHash π) key top index layer message =
      KeyGenerationAndSigning.signLayer π key top index layer message := by
  rw [signLayer, KeyGenerationAndSigning.signLayer, otsSign, KeyGenerationAndSigning.otsSign,
    otsSignFrom_keccakHash]
  rfl

theorem signWithExpandedKey_keccakHash (key : ExpandedKey) (message : Message) :
    signWithExpandedKey (keccakHash π) key message =
      KeyGenerationAndSigning.signWithExpandedKey π key message := by
  simp only [signWithExpandedKey, signLayer_keccakHash]
  rfl

theorem sign_keccakHash (secretKey : SecretKey) (message : Message) :
    sign (keccakHash π) secretKey message = KeyGenerationAndSigning.sign π secretKey message := by
  simp only [sign, signWithExpandedKey_keccakHash]
  rfl

theorem verify_keccakHash (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (keccakHash π) publicKey message signature =
      Verification.verify π publicKey message signature :=
  rfl

end Keccak

/-! ### Answering the hash queries -/

/-- One query of the hash. -/
def hashQuery (input : HashInput) : OracleComp SchemeHashSpec HashOutput :=
  HasQuery.query (spec := SchemeHashSpec) (m := OracleComp SchemeHashSpec) input

section Natural

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {n : Type → Type} [Monad n] [LawfulMonad n]
  (impl : QueryImpl spec n)

theorem simulateQ_sequenceFin {β : Type} :
    ∀ {k : ℕ} (c : Fin k → OracleComp spec β),
      simulateQ impl (sequenceFin c) = sequenceFin fun i ↦ simulateQ impl (c i)
  | 0, _ => rfl
  | k + 1, c => by
    simp only [sequenceFin, simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin]

theorem simulateQ_walkChain {k : ℕ} (step : Fin k → Digest → OracleComp spec Digest)
    (start : ℕ) : ∀ (steps : ℕ) (value : Digest),
      simulateQ impl (walkChain step start steps value) =
        walkChain (fun s v ↦ simulateQ impl (step s v)) start steps value
  | 0, _ => rfl
  | steps + 1, value => by
    simp only [walkChain, simulateQ_bind, simulateQ_walkChain step start steps value]
    refine bind_congr fun x ↦ ?_
    by_cases h : start + steps < k <;> simp [h]

theorem simulateQ_foldPath (node : ℕ → ℕ → HashInput → OracleComp spec Digest) (leafIndex : ℕ)
    (sibling : ℕ → Digest) : ∀ (levels : ℕ) (value : Digest),
      simulateQ impl (foldPath node leafIndex sibling levels value) =
        foldPath (fun a b c ↦ simulateQ impl (node a b c)) leafIndex sibling levels value
  | 0, _ => rfl
  | levels + 1, value => by
    simp only [foldPath, simulateQ_bind, simulateQ_foldPath node leafIndex sibling levels value]

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp spec β) :
    ∀ l : List α, simulateQ impl (l.mapM f) = l.mapM fun a ↦ simulateQ impl (f a)
  | [] => by simp
  | a :: l => by simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, simulateQ_mapM f l]

theorem simulateQ_merkleLevelsFrom (node : ℕ → ℕ → HashInput → OracleComp spec Digest) :
    ∀ (remaining height : ℕ) (below : List Digest),
      simulateQ impl (merkleLevelsFrom node height below remaining) =
        merkleLevelsFrom (fun a b c ↦ simulateQ impl (node a b c)) height below remaining
  | 0, _, _ => rfl
  | remaining + 1, height, below => by
    simp only [merkleLevelsFrom, simulateQ_bind, simulateQ_pure, simulateQ_mapM,
      simulateQ_merkleLevelsFrom node remaining]

end Natural

section HashNatural

variable {n : Type → Type} [Monad n] [LawfulMonad n] (impl : QueryImpl SchemeHashSpec n)

theorem simulateQ_hashQuery (input : HashInput) : simulateQ impl (hashQuery input) = impl input :=
  simulateQ_HasQuery_query impl input

theorem simulateQ_addressedHash (publicSeed : PublicParameter) (address : Address)
    (payload : HashInput) :
    simulateQ impl (addressedHash hashQuery publicSeed address payload) =
      addressedHash impl publicSeed address payload := by
  simp only [addressedHash, simulateQ_bind, simulateQ_pure, simulateQ_hashQuery]

theorem simulateQ_chainWalk (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (start steps : ℕ) (value : Digest) :
    simulateQ impl (chainWalk hashQuery publicSeed layer tree leaf chainIndex start steps value) =
      chainWalk impl publicSeed layer tree leaf chainIndex start steps value := by
  simp only [chainWalk, simulateQ_walkChain, simulateQ_addressedHash]

theorem simulateQ_encode (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    simulateQ impl (encode hashQuery publicSeed layer tree leaf message counter) =
      encode impl publicSeed layer tree leaf message counter := by
  simp only [encode, simulateQ_bind, simulateQ_pure, simulateQ_addressedHash]

theorem simulateQ_otsLeaf (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) :
    simulateQ impl (otsLeaf hashQuery publicSeed layer tree leaf message counter values) =
      otsLeaf impl publicSeed layer tree leaf message counter values := by
  simp only [otsLeaf, simulateQ_bind, simulateQ_encode]
  refine bind_congr fun x ↦ ?_
  cases x with
  | none => rfl
  | some encoding =>
    simp only [simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin, recoverChain,
      simulateQ_chainWalk, leafHash, simulateQ_addressedHash]

theorem simulateQ_treeFold (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : ℕ → Digest) (levels : ℕ) (value : Digest) :
    simulateQ impl (treeFold hashQuery publicSeed layer tree leaf path levels value) =
      treeFold impl publicSeed layer tree leaf path levels value := by
  simp only [treeFold, simulateQ_foldPath, simulateQ_addressedHash]

theorem simulateQ_forsRecover (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    simulateQ impl (forsRecover hashQuery publicSeed index leaves opening) =
      forsRecover impl publicSeed index leaves opening := by
  simp only [forsRecover, forsTreeRecover, forsLeafHash, forsPublicKey, simulateQ_bind,
    simulateQ_sequenceFin, simulateQ_foldPath, simulateQ_addressedHash]

theorem simulateQ_messageDigest (publicKey : PublicKey) (randomizer : Randomizer)
    (message : Message) :
    simulateQ impl (messageDigest hashQuery publicKey randomizer message) =
      messageDigest impl publicKey randomizer message := by
  simp only [messageDigest, messageDigestCall, simulateQ_bind, simulateQ_pure,
    simulateQ_sequenceFin, simulateQ_hashQuery]

theorem simulateQ_verifyLayers (publicSeed : PublicParameter) (index : Index)
    (signature : Signature) : ∀ (layersLeft : ℕ) (message : Digest),
      simulateQ impl (verifyLayers hashQuery publicSeed index signature layersLeft message) =
        verifyLayers impl publicSeed index signature layersLeft message
  | 0, _ => rfl
  | layersLeft + 1, message => by
    simp only [verifyLayers]
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
        · exact simulateQ_verifyLayers publicSeed index signature layersLeft root
    · rfl

theorem simulateQ_verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    simulateQ impl (verify hashQuery publicKey message signature) =
      verify impl publicKey message signature := by
  simp only [verify, simulateQ_bind, simulateQ_messageDigest, simulateQ_forsRecover]
  refine bind_congr fun digest ↦ bind_congr fun forsKey ↦ ?_
  rw [simulateQ_verifyLayers]
  refine bind_congr fun x ↦ ?_
  cases x <;> rfl

theorem simulateQ_expandKey (secretSeed : SecretKey) :
    simulateQ impl (expandKey hashQuery secretSeed) = expandKey impl secretSeed := by
  simp only [expandKey, simulateQ_bind, simulateQ_pure, simulateQ_hashQuery]

theorem simulateQ_prf (key : ExpandedKey) (domain : KeygenDomain) :
    simulateQ impl (prf hashQuery key domain) = prf impl key domain :=
  simulateQ_addressedHash impl _ _ _

theorem simulateQ_otsSecrets (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) :
    simulateQ impl (otsSecrets hashQuery key layer tree leaf) =
      otsSecrets impl key layer tree leaf := by
  simp only [otsSecrets, simulateQ_sequenceFin, simulateQ_prf]

theorem simulateQ_otsPublicLeaf (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) :
    simulateQ impl (otsPublicLeaf hashQuery key layer tree leaf) =
      otsPublicLeaf impl key layer tree leaf := by
  simp only [otsPublicLeaf, simulateQ_bind, simulateQ_otsSecrets, simulateQ_sequenceFin,
    simulateQ_chainWalk, leafHash, simulateQ_addressedHash]

theorem simulateQ_otsSignFrom (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) : ∀ attempts counter : ℕ,
      simulateQ impl (otsSignFrom hashQuery key layer tree leaf message attempts counter) =
        otsSignFrom impl key layer tree leaf message attempts counter
  | 0, _ => rfl
  | attempts + 1, counter => by
    simp only [otsSignFrom, simulateQ_bind, simulateQ_encode]
    refine bind_congr fun x ↦ ?_
    cases x with
    | none => exact simulateQ_otsSignFrom key layer tree leaf message attempts (counter + 1)
    | some encoding =>
      simp only [simulateQ_bind, simulateQ_pure, simulateQ_otsSecrets, simulateQ_sequenceFin,
        simulateQ_chainWalk]

theorem simulateQ_treeLevels (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    simulateQ impl (treeLevels hashQuery key layer tree) = treeLevels impl key layer tree := by
  simp only [treeLevels, merkleLevels, simulateQ_bind, simulateQ_mapM, simulateQ_otsPublicLeaf,
    simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_forsOpen (key : ExpandedKey) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) :
    simulateQ impl (forsOpen hashQuery key index leaves) = forsOpen impl key index leaves := by
  simp only [forsOpen, forsTreeOpen, forsSecret, forsLeafHash, forsPublicKey, merkleLevels,
    simulateQ_bind, simulateQ_pure, simulateQ_sequenceFin, simulateQ_mapM, simulateQ_prf,
    simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_keygenInternal (key : ExpandedKey) :
    simulateQ impl (keygenInternal hashQuery key) = keygenInternal impl key := by
  simp only [keygenInternal, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

theorem simulateQ_keygenFromSeed (secretSeed : SecretKey) :
    simulateQ impl (keygenFromSeed hashQuery secretSeed) = keygenFromSeed impl secretSeed := by
  simp only [keygenFromSeed, simulateQ_bind, simulateQ_expandKey, simulateQ_keygenInternal]
  refine bind_congr fun key ↦ bind_congr fun x ↦ ?_
  rfl

theorem simulateQ_signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index)
    (layer : Layer) (message : Digest) :
    simulateQ impl (signLayer hashQuery key top index layer message) =
      signLayer impl key top index layer message := by
  simp only [signLayer, otsSign, simulateQ_bind, simulateQ_otsSignFrom]
  refine bind_congr fun x ↦ ?_
  rcases x with _ | ⟨counter, values⟩
  · rfl
  · by_cases h : layer = topLayer
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

theorem simulateQ_signWithExpandedKey (key : ExpandedKey) (message : Message) :
    simulateQ impl (signWithExpandedKey hashQuery key message) =
      signWithExpandedKey impl key message := by
  simp only [signWithExpandedKey, prfMessage, simulateQ_bind, simulateQ_pure,
    simulateQ_keygenInternal, simulateQ_hashQuery, simulateQ_messageDigest, simulateQ_forsOpen,
    simulateQ_signLayer]
  refine bind_congr fun x ↦ bind_congr fun y ↦ bind_congr fun digest ↦ bind_congr fun f ↦
    bind_congr fun b ↦ ?_
  rcases b with _ | ⟨bottom, bottomRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun c ↦ ?_
  rcases c with _ | ⟨middle, middleRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun d ↦ ?_
  rcases d with _ | ⟨topSignature, _⟩ <;> rfl

theorem simulateQ_sign (secretKey : SecretKey) (message : Message) :
    simulateQ impl (sign hashQuery secretKey message) = sign impl secretKey message := by
  simp only [sign, simulateQ_bind, simulateQ_expandKey, simulateQ_signWithExpandedKey]

end HashNatural

end WithHash

/-! ## The hash-query scheme -/

local notation "σ" => schemeHashOverPermutation

/-- **leanSPHINCS with a hash oracle**: the statement's scheme with each hash a query. -/
noncomputable def schemeWithHash :
    SchemeWithHash MasterSeed PublicKey SecretKey Message (Option Signature) Forgery where
  sample := HashSig.sampleMasterSeed
  keygen := WithHash.keygenFromSeed WithHash.hashQuery
  sign := WithHash.sign WithHash.hashQuery
  verify pk forgery := WithHash.verify WithHash.hashQuery pk forgery.message forgery.signature
  win := RandomPermutationModel.sufCmaScheme.winningCondition

theorem schemeWithHash_keygen (secretSeed : MasterSeed) :
    schemeWithHash.keygen secretSeed = WithHash.keygenFromSeed WithHash.hashQuery secretSeed :=
  rfl

theorem schemeWithHash_sign (secretKey : SecretKey) (message : Message) :
    schemeWithHash.sign secretKey message = WithHash.sign WithHash.hashQuery secretKey message :=
  rfl

theorem schemeWithHash_verify (publicKey : PublicKey) (forgery : Forgery) :
    schemeWithHash.verify publicKey forgery =
      WithHash.verify WithHash.hashQuery publicKey forgery.message forgery.signature :=
  rfl

theorem schemeHashOverPermutation_eq : (σ : HashInput → _) = keccakHash queryPermutation :=
  funext Quantum.SufCma.schemeHashOverPermutation_apply

/-- **The statement's key generation is the hash-query form's** with the hash Keccak-256 over
`π`. -/
theorem simulateQ_schemeHash_generateKeys (secretSeed : MasterSeed) :
    simulateQ σ (schemeWithHash.keygen secretSeed) =
      RandomPermutationModel.sufCmaScheme.generateKeys secretSeed := by
  change simulateQ σ (WithHash.keygenFromSeed WithHash.hashQuery secretSeed) = _
  rw [WithHash.simulateQ_keygenFromSeed, schemeHashOverPermutation_eq]
  rfl

/-- **The statement's signer is the hash-query form's.** -/
theorem simulateQ_schemeHash_sign (secretKey : SecretKey) (message : Message) :
    simulateQ σ (schemeWithHash.sign secretKey message) =
      RandomPermutationModel.sufCmaScheme.sign secretKey message := by
  change simulateQ σ (WithHash.sign WithHash.hashQuery secretKey message) = _
  rw [WithHash.simulateQ_sign, schemeHashOverPermutation_eq]
  exact WithHash.sign_keccakHash _ _ _

/-- **The statement's verifier is the hash-query form's.** -/
theorem simulateQ_schemeHash_verify (publicKey : PublicKey) (forgery : Forgery) :
    simulateQ σ (schemeWithHash.verify publicKey forgery) =
      RandomPermutationModel.sufCmaScheme.verify publicKey forgery := by
  change simulateQ σ (WithHash.verify WithHash.hashQuery publicKey forgery.message
    forgery.signature) = _
  rw [WithHash.simulateQ_verify, schemeHashOverPermutation_eq]
  rfl

/-- **The statement's scheme is the hash-query scheme over `π`.** -/
theorem overPermutation_schemeWithHash :
    schemeWithHash.overPermutation = RandomPermutationModel.sufCmaScheme := by
  unfold SchemeWithHash.overPermutation RandomPermutationModel.sufCmaScheme
  congr 1
  · funext secretSeed
    exact simulateQ_schemeHash_generateKeys secretSeed
  · funext secretKey message
    exact simulateQ_schemeHash_sign secretKey message
  · funext publicKey forgery
    exact simulateQ_schemeHash_verify publicKey forgery

section Honest

variable (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) {r : Type → Type} [Monad r]
  [LawfulMonad r] (impl : QueryImpl RandomPermutationOracles r)
  (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm (spongePerm t π) s))

include himpl

/-- **Key generation, the honest evaluation**: over `statePerm (spongePerm t π)`, the statement's
key generation returns what `honestEval` of the hash-query form returns. -/
theorem simulateQ_generateKeys (secretSeed : MasterSeed) :
    simulateQ impl (RandomPermutationModel.sufCmaScheme.generateKeys secretSeed) =
      pure (honestEval t π (schemeWithHash.keygen secretSeed)).1 := by
  rw [← simulateQ_schemeHash_generateKeys]
  exact Quantum.SufCma.simulateQ_schemeHash t π impl himpl _

/-- **Signing, the honest evaluation.** -/
theorem simulateQ_sign (secretKey : SecretKey) (message : Message) :
    simulateQ impl (RandomPermutationModel.sufCmaScheme.sign secretKey message) =
      pure (honestEval t π (schemeWithHash.sign secretKey message)).1 := by
  rw [← simulateQ_schemeHash_sign]
  exact Quantum.SufCma.simulateQ_schemeHash t π impl himpl _

/-- **Verification, the honest evaluation.** -/
theorem simulateQ_verify (publicKey : PublicKey) (forgery : Forgery) :
    simulateQ impl (RandomPermutationModel.sufCmaScheme.verify publicKey forgery) =
      pure (honestEval t π (schemeWithHash.verify publicKey forgery)).1 := by
  rw [← simulateQ_schemeHash_verify]
  exact Quantum.SufCma.simulateQ_schemeHash t π impl himpl _

end Honest

/-! ## Computations in `Id` -/

section IdEval

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x :=
  rfl

theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a :=
  rfl

theorem mapM_id {α β : Type} (f : α → Id β) : ∀ l : List α, l.mapM f = l.map f
  | [] => rfl
  | a :: l => by rw [List.mapM_cons, mapM_id f l]; rfl

theorem sequenceFin_id {β : Type} : ∀ {k : ℕ} (c : Fin k → Id β), sequenceFin c = c
  | 0, _ => funext fun i ↦ i.elim0
  | k + 1, c => by
    simp only [sequenceFin, id_bind, sequenceFin_id, id_pure]
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i

theorem getD_map_range {β : Type} (g : ℕ → β) (n i : ℕ) (d : β) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem levelNode_cons_zero (below : List Digest) (rest : List (List Digest)) (j : ℕ) :
    levelNode (below :: rest) 0 j = below.getD j 0 :=
  rfl

theorem levelNode_cons_succ (below : List Digest) (rest : List (List Digest)) (z j : ℕ) :
    levelNode (below :: rest) (z + 1) j = levelNode rest z j :=
  rfl

/-- **Levels built from honest nodes are the honest nodes**: node `j` of level `z` of the levels
over the nodes at height `height` is the value `T (height + z) j`. -/
theorem levelNode_merkleLevelsFrom (node : ℕ → ℕ → HashInput → Id Digest) (T : ℕ → ℕ → Digest)
    (top : ℕ) (hnode : ∀ h j, h < top →
      node (h + 1) j (nodePayload (T h (2 * j)) (T h (2 * j + 1))) = T (h + 1) j) :
    ∀ (remaining height : ℕ) (below : List Digest), height + remaining ≤ top →
      below.length = 2 ^ remaining → (∀ i < below.length, below.getD i 0 = T height i) →
      ∀ z ≤ remaining, ∀ j < 2 ^ (remaining - z),
        levelNode (merkleLevelsFrom node height below remaining) z j = T (height + z) j := by
  intro remaining
  induction remaining with
  | zero =>
    intro height below _ hlen hbelow z hz j hj
    obtain rfl : z = 0 := by omega
    rw [merkleLevelsFrom, id_pure, levelNode_cons_zero, Nat.add_zero]
    exact hbelow j (by simp at hj; omega)
  | succ remaining ih =>
    intro height below hH hlen hbelow z hz j hj
    rw [merkleLevelsFrom, id_bind, mapM_id, id_bind, id_pure]
    cases z with
    | zero =>
      rw [levelNode_cons_zero, Nat.add_zero]
      exact hbelow j (by rw [hlen]; exact hj)
    | succ z =>
      rw [levelNode_cons_succ]
      have hhalf : below.length / 2 = 2 ^ remaining := by rw [hlen, pow_succ]; omega
      rw [show height + (z + 1) = height + 1 + z by omega]
      refine ih (height + 1) _ (by omega) (by simp [hhalf]) (fun i hi ↦ ?_) z (by omega) j
        (by simpa [Nat.add_sub_add_right] using hj)
      simp only [List.length_map, List.length_range] at hi
      rw [getD_map_range _ _ _ _ hi]
      have h1 : 2 * i < below.length := by omega
      have h2 : 2 * i + 1 < below.length := by omega
      rw [hbelow _ h1, hbelow _ h2]
      exact hnode height i (by omega)

theorem levelNode_merkleLevels (node : ℕ → ℕ → HashInput → Id Digest) (T : ℕ → ℕ → Digest)
    (top : ℕ) (hnode : ∀ h j, h < top →
      node (h + 1) j (nodePayload (T h (2 * j)) (T h (2 * j + 1))) = T (h + 1) j)
    (leaves : List Digest) (hlen : leaves.length = 2 ^ top)
    (hleaves : ∀ i < leaves.length, leaves.getD i 0 = T 0 i) (z : ℕ) (hz : z ≤ top) (j : ℕ)
    (hj : j < 2 ^ (top - z)) :
    levelNode (merkleLevels node leaves top) z j = T z j := by
  have h :=
    levelNode_merkleLevelsFrom node T top hnode top 0 leaves (by omega) hlen hleaves z hz j hj
  rwa [Nat.zero_add] at h

theorem shiftRight_xor_lt {leaf top z : ℕ} (hleaf : leaf < 2 ^ top) (hz : z < top) :
    (leaf >>> z) ^^^ 1 < 2 ^ (top - z) := by
  refine Nat.xor_lt_two_pow ?_ (Nat.one_lt_two_pow (by omega))
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    Nat.sub_add_cancel hz.le]
  exact hleaf

end IdEval

/-! ## Index arithmetic -/

theorem layerHeight_le (l : Layer) : layerHeight l ≤ 10 := by
  unfold layerHeight
  split <;> norm_num

theorem leafOfIndex_lt (l : Layer) (idx : Index) : (leafOfIndex l idx).val < 2 ^ layerHeight l :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem treeOfIndex_topLayer (idx : Index) : treeOfIndex topLayer idx = 0 :=
  Fin.ext (Nat.div_eq_of_lt (lt_of_lt_of_le idx.isLt (by decide)))

theorem forsLeafOfNat_val (s : ForsLeafIndex) : forsLeafOfNat s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem leafOfNat_val (e : TreeLeafIndex) : leafOfNat e.val = e :=
  Fin.ext (Nat.mod_eq_of_lt e.isLt)

/-! ## The honest table -/

/-- **The honest table**: the keys `h, k, k'` and the inner permutation `π` of the sponge view, and
the secret key `SK.seed`. Every value of leanSPHINCS's honest computations is a function of
these. -/
structure HonestTable where
  /-- The keys `t = (h, k, k')`. -/
  keys : SpongeKeys X Z
  /-- The inner permutation `π`. -/
  perm : Equiv.Perm (X × Z)
  /-- The secret key `SK.seed`. -/
  secretSeed : MasterSeed

namespace HonestTable

variable (L : HonestTable)

/-- The sponge view `φ = spongePerm t π`. -/
def view : Equiv.Perm (X × Z) :=
  spongePerm L.keys L.perm

/-- The honest hash `H`. -/
def hash : QueryImpl SchemeHashSpec Id :=
  spongeOut L.view

/-- `Trunc_16` of the honest hash. -/
def digest (input : HashInput) : Digest :=
  truncateHash (L.hash input)

/-- `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)`. -/
def prfKey : HashOutput :=
  L.hash (keyDerivationInput L.secretSeed 1)

/-- `PK.seed = Trunc_16(H(leanSPHINCS ‖ SK.seed ‖ 0))`. -/
def publicSeed : PublicParameter :=
  L.digest (keyDerivationInput L.secretSeed 0)

/-- The expanded key. -/
def expandedKey : ExpandedKey :=
  ⟨L.secretSeed, L.prfKey, L.publicSeed⟩

@[simp]
theorem expandedKey_secretSeed : L.expandedKey.secretSeed = L.secretSeed :=
  rfl

@[simp]
theorem expandedKey_secretPrfKey : L.expandedKey.secretPrfKey = L.prfKey :=
  rfl

@[simp]
theorem expandedKey_publicSeed : L.expandedKey.publicSeed = L.publicSeed :=
  rfl

/-- The tweakable hash at a hash domain under `PK.seed`. -/
def th (domain : HashDomain) (payload : HashInput) : Digest :=
  L.digest (addressedHashInput L.publicSeed (hashDomainFields domain) payload)

/-- A secret, `PRF(PK.seed, SK.seed, ADRS)`. -/
def secret (domain : KeygenDomain) : Digest :=
  L.digest (addressedHashInput L.publicSeed (keygenDomainFields domain)
    (littleEndianBytes 32 L.secretSeed))

/-- Position `j` of chain `i` of the one-time key `(l, τ, e)` (`0` past the end, as `walkChain`):
the start at `0`. -/
def chainValue (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : ℕ → Digest
  | 0 => L.secret (.oneTimeChain l τ e i)
  | j + 1 => if h : j < chainLength - 1 then
      L.th (.chain l τ e i ⟨j, h⟩) (littleEndianBytes 16 (chainValue l τ e i j))
    else 0

/-- The chain ends of a one-time key. -/
def endpoints (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : Digest :=
  L.chainValue l τ e i (chainLength - 1)

/-- The value of tree `τ` of layer `l` at `level`, index `index`: the one-time leaf of key
`leafOfNat index` at level `0`, else the node. -/
def treeValue (l : Layer) (τ : TreeIndex) : ℕ → ℕ → Digest
  | 0, index =>
      L.th (.leaf l τ (leafOfNat index)) (digestsPayload (L.endpoints l τ (leafOfNat index)))
  | level + 1, index => L.th (.node l τ (level + 1) index)
      (nodePayload (treeValue l τ level (2 * index)) (treeValue l τ level (2 * index + 1)))

/-- The root of tree `τ` of layer `l`. -/
def treeRoot (l : Layer) (τ : TreeIndex) : Digest :=
  L.treeValue l τ (layerHeight l) 0

/-- `PK.root`, the root of the top tree. -/
def root : Digest :=
  L.treeRoot topLayer 0

/-- The public key. -/
def publicKey : PublicKey :=
  ⟨L.publicSeed, L.root⟩

/-- The secret of leaf `s` of FORS tree `κ` of instance `idx`. -/
def forsSecret (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) : Digest :=
  L.secret (.forsSecret idx κ s)

/-- The value of FORS tree `κ` of instance `idx` at `height`, node `j`: the FORS leaf (the hash of
the secret of leaf `forsLeafOfNat j`) at height `0`, else the node. -/
def forsValue (idx : Index) (κ : ForsTreeIndex) : ℕ → ℕ → Digest
  | 0, j => L.th (.forsLeaf idx κ (forsLeafOfNat j))
      (littleEndianBytes 16 (L.forsSecret idx κ (forsLeafOfNat j)))
  | h + 1, j => L.th (.forsNode idx κ (h + 1) j)
      (nodePayload (forsValue idx κ h (2 * j)) (forsValue idx κ h (2 * j + 1)))

/-- The root of FORS tree `κ` of instance `idx`. -/
def forsRoot (idx : Index) (κ : ForsTreeIndex) : Digest :=
  L.forsValue idx κ forsTreeHeight 0

/-- The FORS public key of instance `idx`: `T_k` of its roots. -/
def forsKey (idx : Index) : Digest :=
  L.th (.forsRoots idx) (digestsPayload (L.forsRoot idx))

/-- The randomizer `R(M) = PRF_msg(SK.prf, PK.seed, M')`. -/
def randomizer (message : Message) : Randomizer :=
  L.digest (prfMessageInput L.prfKey L.publicSeed message)

/-- Call `i` of `H_msg(R(M), PK.seed, PK.root, M)`. -/
def digestOutput (message : Message) (call : DigestCall) : HashOutput :=
  L.hash (messageDigestInput (L.randomizer message) L.publicSeed L.root message call)

/-- The message digest of `M`. -/
def messageDigest (message : Message) : MessageDigest :=
  truncateMessageDigest (L.digestOutput message)

/-- The index of `M`'s signature. -/
def index (message : Message) : Index :=
  digestIndex (L.messageDigest message)

/-- The FORS leaves of `M`'s signature. -/
def leaves (message : Message) : ForsTreeIndex → ForsLeafIndex :=
  digestForsLeaves (L.messageDigest message)

/-- The FORS opening of instance `idx` at the leaves `lv`. -/
def forsOpening (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ForsTreeIndex → ForsTreeOpening :=
  fun κ ↦ ⟨L.forsSecret idx κ (lv κ),
    fun z ↦ L.forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)⟩

/-- The encoding digest of the one-time key `(l, τ, e)` on `message` at `counter`. -/
def encDigest (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest)
    (counter : EncodingCounter) : Digest :=
  L.th (.encoding l τ e) (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)

/-- The counter search from `counter`, `attempts` counters: the first codeword's counter and
word. -/
def selectFrom (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    ℕ → ℕ → Option (EncodingCounter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
    match TargetSum.decodeDigest (L.encDigest l τ e message (BitVec.ofNat counterBits counter)) with
    | some x => some (BitVec.ofNat counterBits counter, x)
    | none => selectFrom l τ e message attempts (counter + 1)

/-- **The selection** of the one-time key `(l, τ, e)` on `message`: the least counter below
`2^32` whose encoding is a codeword, with the codeword. -/
def select (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    Option (EncodingCounter × Encoding) :=
  L.selectFrom l τ e message encodingAttemptLimit 0

/-- The authentication path of key `e` in tree `τ` of layer `l`. -/
def authPath (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (z : Fin (layerHeight l)) : Digest :=
  L.treeValue l τ z.val ((e.val >>> z.val) ^^^ 1)

/-- The one-time signature of `message` by `(l, τ, e)`, with the key's path. -/
def layerSignature (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    Option (LayerSignature l) :=
  (L.select l τ e message).map fun sel ↦
    ⟨sel.1, fun i ↦ L.chainValue l τ e i (sel.2 i).val, L.authPath l τ e⟩

/-- **What `K_l(idx)` signs** in every signature of index `idx`: the FORS key of `idx` at the
bottom, the root of the tree below above it. -/
def layerMessage (idx : Index) (l : Layer) : Digest :=
  if h : l.val = 0 then L.forsKey idx
  else L.treeRoot ⟨l.val - 1, by omega⟩ (treeOfIndex ⟨l.val - 1, by omega⟩ idx)

theorem layerMessage_zero (idx : Index) : L.layerMessage idx 0 = L.forsKey idx :=
  rfl

theorem layerMessage_one (idx : Index) :
    L.layerMessage idx 1 = L.treeRoot 0 (treeOfIndex 0 idx) :=
  rfl

theorem layerMessage_two (idx : Index) :
    L.layerMessage idx 2 = L.treeRoot 1 (treeOfIndex 1 idx) :=
  rfl

/-- The signature of layer `l` in a signature of index `idx`. -/
def layerSig (idx : Index) (l : Layer) : Option (LayerSignature l) :=
  L.layerSignature l (treeOfIndex l idx) (leafOfIndex l idx) (L.layerMessage idx l)

/-- **The honest signature** of a message. -/
def signature (message : Message) : Option Signature :=
  match L.layerSig (L.index message) 0, L.layerSig (L.index message) 1,
    L.layerSig (L.index message) 2 with
  | some bottom, some middle, some top =>
      some ⟨L.randomizer message, L.forsOpening (L.index message) (L.leaves message),
        layerSignatures bottom middle top⟩
  | _, _, _ => none

theorem chainValue_succ (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex)
    (step : ChainStep) :
    L.chainValue l τ e i (step.val + 1) =
      L.th (.chain l τ e i step) (littleEndianBytes 16 (L.chainValue l τ e i step.val)) := by
  rw [chainValue, dite_eq_left step.isLt]

theorem treeValue_zero (l : Layer) (τ : TreeIndex) (index : ℕ) :
    L.treeValue l τ 0 index =
      L.th (.leaf l τ (leafOfNat index)) (digestsPayload (L.endpoints l τ (leafOfNat index))) := by
  rw [treeValue]

theorem treeValue_succ (l : Layer) (τ : TreeIndex) (level index : ℕ) :
    L.treeValue l τ (level + 1) index = L.th (.node l τ (level + 1) index)
      (nodePayload (L.treeValue l τ level (2 * index))
        (L.treeValue l τ level (2 * index + 1))) := by
  rw [treeValue]

theorem forsValue_zero (idx : Index) (κ : ForsTreeIndex) (j : ℕ) :
    L.forsValue idx κ 0 j = L.th (.forsLeaf idx κ (forsLeafOfNat j))
      (littleEndianBytes 16 (L.forsSecret idx κ (forsLeafOfNat j))) := by
  rw [forsValue]

theorem forsValue_succ (idx : Index) (κ : ForsTreeIndex) (h j : ℕ) :
    L.forsValue idx κ (h + 1) j = L.th (.forsNode idx κ (h + 1) j)
      (nodePayload (L.forsValue idx κ h (2 * j)) (L.forsValue idx κ h (2 * j + 1))) := by
  rw [forsValue]

/-! ### The honest computations return the table's values -/

open WithHash

theorem eval_addressedHash (seed : PublicParameter) (address : Address) (payload : HashInput) :
    addressedHash (m := Id) L.hash seed address payload =
      L.digest (addressedHashInput seed address payload) :=
  rfl

theorem eval_tweakableHash (domain : HashDomain) (payload : HashInput) :
    tweakableHash (m := Id) L.hash L.expandedKey.publicSeed domain payload = L.th domain payload :=
  rfl

theorem eval_encode (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest)
    (counter : EncodingCounter) :
    encode (m := Id) L.hash L.expandedKey.publicSeed l τ e message counter =
      TargetSum.decodeDigest (L.encDigest l τ e message counter) := by
  rw [encode, id_bind, eval_tweakableHash]
  rfl

theorem eval_chainWalk (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) :
    ∀ j, chainWalk (m := Id) L.hash L.publicSeed l τ e i 0 j (L.chainValue l τ e i 0) =
      L.chainValue l τ e i j
  | 0 => rfl
  | j + 1 => by
    have ih := eval_chainWalk l τ e i j
    rw [chainWalk] at ih ⊢
    rw [walkChain, id_bind, ih, chainValue]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (by omega), dite_eq_left h]
      simp only [Nat.zero_add]
      rfl
    · rw [dite_eq_right (by omega), dite_eq_right h]
      rfl

theorem eval_otsSecrets (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    otsSecrets (m := Id) L.hash L.expandedKey l τ e = fun i ↦ L.chainValue l τ e i 0 := by
  rw [otsSecrets, sequenceFin_id]
  rfl

theorem eval_otsPublicLeaf (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    otsPublicLeaf (m := Id) L.hash L.expandedKey l τ e =
      L.th (.leaf l τ e) (digestsPayload (L.endpoints l τ e)) := by
  simp only [otsPublicLeaf, id_bind, eval_otsSecrets, sequenceFin_id, expandedKey_publicSeed,
    eval_chainWalk]
  rfl

theorem levelNode_treeLevels (l : Layer) (τ : TreeIndex) (z : ℕ) (hz : z ≤ layerHeight l) (j : ℕ)
    (hj : j < 2 ^ (layerHeight l - z)) :
    levelNode (treeLevels (m := Id) L.hash L.expandedKey l τ) z j = L.treeValue l τ z j := by
  rw [treeLevels, id_bind, mapM_id]
  refine levelNode_merkleLevels
    (fun height nodeIndex ↦
      tweakableHash (m := Id) L.hash L.expandedKey.publicSeed (.node l τ height nodeIndex))
    (L.treeValue l τ) (layerHeight l)
    (fun h j _ ↦ (L.eval_tweakableHash _ _).trans (L.treeValue_succ l τ h j).symm)
    _ (by simp) (fun i hi ↦ ?_) z hz j hj
  simp only [List.length_map, List.length_range] at hi
  rw [getD_map_range _ _ _ _ hi, eval_otsPublicLeaf, treeValue_zero]

/-- The path and the root a tree's levels give. -/
theorem treeLevels_fields (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (he : e.val < 2 ^ layerHeight l) :
    (fun z : Fin (layerHeight l) ↦
        levelNode (treeLevels (m := Id) L.hash L.expandedKey l τ) z.val ((e.val >>> z.val) ^^^ 1)) =
      L.authPath l τ e ∧
    levelNode (treeLevels (m := Id) L.hash L.expandedKey l τ) (layerHeight l) 0 =
      L.treeRoot l τ := by
  refine ⟨funext fun z ↦ ?_, ?_⟩
  · exact L.levelNode_treeLevels l τ z.val z.isLt.le _ (shiftRight_xor_lt he z.isLt)
  · exact L.levelNode_treeLevels l τ _ le_rfl 0 (by simp)

theorem eval_forsTreeOpen (idx : Index) (κ : ForsTreeIndex) (leaf : ForsLeafIndex) :
    forsTreeOpen (m := Id) L.hash L.expandedKey idx κ leaf =
      (L.forsRoot idx κ, ⟨L.forsSecret idx κ leaf,
        fun z ↦ L.forsValue idx κ z.val ((leaf.val >>> z.val) ^^^ 1)⟩) := by
  rw [forsTreeOpen, id_bind, mapM_id, id_bind, mapM_id, id_bind, id_pure]
  have hlevels : ∀ z ≤ forsTreeHeight, ∀ j < 2 ^ (forsTreeHeight - z),
      levelNode (merkleLevels (fun height node ↦
          tweakableHash (m := Id) L.hash L.expandedKey.publicSeed (.forsNode idx κ height node))
        ((List.range (2 ^ forsTreeHeight)).map fun s ↦
          forsLeafHash (m := Id) L.hash L.expandedKey.publicSeed idx κ (forsLeafOfNat s)
            (((List.range (2 ^ forsTreeHeight)).map fun s ↦
              WithHash.forsSecret (m := Id) L.hash L.expandedKey idx κ (forsLeafOfNat s)).getD s 0))
        forsTreeHeight) z j = L.forsValue idx κ z j := by
    intro z hz j hj
    refine levelNode_merkleLevels
      (fun height node ↦
        tweakableHash (m := Id) L.hash L.expandedKey.publicSeed (.forsNode idx κ height node))
      (L.forsValue idx κ) forsTreeHeight
      (fun h j _ ↦ (L.eval_tweakableHash _ _).trans (L.forsValue_succ idx κ h j).symm)
      _ (by simp) (fun i hi ↦ ?_) z hz j hj
    simp only [List.length_map, List.length_range] at hi
    rw [getD_map_range _ _ _ _ hi, getD_map_range _ _ _ _ hi, forsValue_zero]
    exact L.eval_tweakableHash _ _
  refine Prod.ext (hlevels _ le_rfl 0 (by simp)) ?_
  dsimp only
  refine congrArg₂ ForsTreeOpening.mk ?_
    (funext fun z ↦ hlevels z.val z.isLt.le _ (shiftRight_xor_lt leaf.isLt z.isLt))
  rw [getD_map_range _ _ _ _ leaf.isLt, forsLeafOfNat_val]
  rfl

theorem eval_forsOpen (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    forsOpen (m := Id) L.hash L.expandedKey idx lv = (L.forsKey idx, L.forsOpening idx lv) := by
  simp only [forsOpen, id_bind, sequenceFin_id, eval_forsTreeOpen, id_pure]
  rfl

theorem eval_otsSignFrom (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    ∀ attempts counter, otsSignFrom (m := Id) L.hash L.expandedKey l τ e message attempts counter =
      (L.selectFrom l τ e message attempts counter).map fun sel ↦
        (sel.1, fun i ↦ L.chainValue l τ e i (sel.2 i).val)
  | 0, _ => rfl
  | attempts + 1, counter => by
    rw [otsSignFrom, selectFrom, id_bind, eval_encode]
    cases TargetSum.decodeDigest (L.encDigest l τ e message (BitVec.ofNat counterBits counter)) with
    | none => exact eval_otsSignFrom l τ e message attempts (counter + 1)
    | some x =>
      simp only [id_bind, eval_otsSecrets, sequenceFin_id, expandedKey_publicSeed, eval_chainWalk,
        id_pure, Option.map_some]

theorem eval_signLayer (idx : Index) (layer : Layer) (message : Digest) :
    signLayer (m := Id) L.hash L.expandedKey (treeLevels L.hash L.expandedKey topLayer 0) idx layer
        message =
      (L.layerSignature layer (treeOfIndex layer idx) (leafOfIndex layer idx) message).map
        fun sig ↦ (sig, L.treeRoot layer (treeOfIndex layer idx)) := by
  obtain ⟨hpath, hroot⟩ := L.treeLevels_fields layer (treeOfIndex layer idx) (leafOfIndex layer idx)
    (leafOfIndex_lt layer idx)
  rw [signLayer, otsSign, id_bind, eval_otsSignFrom, layerSignature, select]
  cases L.selectFrom layer (treeOfIndex layer idx) (leafOfIndex layer idx) message
      encodingAttemptLimit 0 with
  | none => rfl
  | some sel =>
    simp only [Option.map_some]
    by_cases h : layer = topLayer
    · subst h
      rw [ite_eq_left rfl]
      simp only [id_bind, id_pure]
      rw [treeOfIndex_topLayer] at hpath hroot ⊢
      rw [hpath, hroot]
    · simp only [h, ↓reduceIte, id_bind, id_pure]
      rw [hpath, hroot]

theorem eval_keygenInternal :
    keygenInternal (m := Id) L.hash L.expandedKey =
      (L.publicKey, treeLevels L.hash L.expandedKey topLayer 0) := by
  rw [keygenInternal, id_bind, id_pure, (L.treeLevels_fields topLayer 0 0 (by simp)).2]
  rfl

/-- **Key generation returns the table's keys.** -/
theorem eval_keygen :
    keygenFromSeed (m := Id) L.hash L.secretSeed = (L.publicKey, L.secretSeed) := by
  rw [keygenFromSeed, id_bind,
    show expandKey (m := Id) L.hash L.secretSeed = L.expandedKey from rfl,
    id_bind, eval_keygenInternal]
  rfl

/-- **Signing returns the table's signature.** -/
theorem eval_sign (message : Message) :
    sign (m := Id) L.hash L.secretSeed message = L.signature message := by
  have hR : prfMessage (m := Id) L.hash L.expandedKey.secretPrfKey L.expandedKey.publicSeed
      message = L.randomizer message := rfl
  have hD : WithHash.messageDigest (m := Id) L.hash L.publicKey (L.randomizer message) message =
      L.messageDigest message := by
    rw [WithHash.messageDigest, id_bind, sequenceFin_id]
    rfl
  have hI : digestIndex (L.messageDigest message) = L.index message := rfl
  have hV : digestForsLeaves (L.messageDigest message) = L.leaves message := rfl
  rw [sign, id_bind, show expandKey (m := Id) L.hash L.secretSeed = L.expandedKey from rfl,
    signWithExpandedKey, id_bind, eval_keygenInternal]
  simp only [id_bind, hR, hD, hI, hV, eval_forsOpen, eval_signLayer]
  simp only [signature, layerSig, layerMessage_zero, layerMessage_one, layerMessage_two]
  cases L.layerSignature 0 (treeOfIndex 0 (L.index message)) (leafOfIndex 0 (L.index message))
      (L.forsKey (L.index message)) with
  | none => rfl
  | some bottom =>
    simp only [Option.map_some]
    cases L.layerSignature 1 (treeOfIndex 1 (L.index message)) (leafOfIndex 1 (L.index message))
        (L.treeRoot 0 (treeOfIndex 0 (L.index message))) with
    | none => rfl
    | some middle =>
      simp only [Option.map_some]
      cases L.layerSignature 2 (treeOfIndex 2 (L.index message)) (leafOfIndex 2 (L.index message))
          (L.treeRoot 1 (treeOfIndex 1 (L.index message))) with
      | none => rfl
      | some top => rfl

/-! ### The statement's algorithms return the table's values -/

variable {r : Type → Type} [Monad r] [LawfulMonad r] (impl : QueryImpl RandomPermutationOracles r)

theorem fst_honestEval_eq {α : Type} (x : OracleComp SchemeHashSpec α) :
    (honestEval L.keys L.perm x).1 = simulateQ L.hash x :=
  Quantum.SufCma.fst_honestEval L.keys L.perm x

theorem fst_honestEval_keygen :
    (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed)).1 =
      (L.publicKey, L.secretSeed) := by
  rw [L.fst_honestEval_eq, schemeWithHash_keygen, WithHash.simulateQ_keygenFromSeed, L.eval_keygen]

theorem fst_honestEval_sign (message : Message) :
    (honestEval L.keys L.perm (schemeWithHash.sign L.secretSeed message)).1 =
      L.signature message := by
  rw [L.fst_honestEval_eq, schemeWithHash_sign, WithHash.simulateQ_sign, L.eval_sign]

/-- **`honest_eq_scheme`, key generation**: over `statePerm φ` the statement's key generation from
`SK.seed` returns the table's keys. -/
theorem simulateQ_generateKeys_eq
    (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm L.view s)) :
    simulateQ impl (RandomPermutationModel.sufCmaScheme.generateKeys L.secretSeed) =
      pure (L.publicKey, L.secretSeed) := by
  rw [simulateQ_generateKeys L.keys L.perm impl himpl, L.fst_honestEval_keygen]

/-- **`honest_eq_scheme`, signing**: over `statePerm φ` the statement's signer with `SK.seed`
returns the table's signature. -/
theorem simulateQ_sign_eq (himpl : ∀ s, impl (.inr (.forward s)) = pure (statePerm L.view s))
    (message : Message) :
    simulateQ impl (RandomPermutationModel.sufCmaScheme.sign L.secretSeed message) =
      pure (L.signature message) := by
  rw [simulateQ_sign L.keys L.perm impl himpl, L.fst_honestEval_sign]

/-- **The honest signer depends on the keys only through what it reads**: keys answering every read
of the signer of `M` as the table's do give the same evaluation (the table's signature,
`fst_honestEval_sign`). The reads are stated as `(honestEval ...).2`: a definition naming them
would make the kernel evaluate the whole signer when it is unfolded against that projection. -/
theorem honestEval_congr_sign {t' : SpongeKeys X Z} (message : Message)
    (h : ∀ e ∈ (honestEval L.keys L.perm (schemeWithHash.sign L.secretSeed message)).2,
      e.AnsweredBy t') :
    honestEval t' L.perm (schemeWithHash.sign L.secretSeed message) =
      honestEval L.keys L.perm (schemeWithHash.sign L.secretSeed message) :=
  Quantum.SufCma.honestEval_congr (t := L.keys) (t' := t') L.perm
    (schemeWithHash.sign L.secretSeed message) h

/-- **Key generation depends on the keys only through what it reads.** -/
theorem honestEval_congr_keygen {t' : SpongeKeys X Z}
    (h : ∀ e ∈ (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed)).2,
      e.AnsweredBy t') :
    honestEval t' L.perm (schemeWithHash.keygen L.secretSeed) =
      honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed) :=
  Quantum.SufCma.honestEval_congr (t := L.keys) (t' := t') L.perm
    (schemeWithHash.keygen L.secretSeed) h

end HonestTable

end Quantum.Sphincs

end
