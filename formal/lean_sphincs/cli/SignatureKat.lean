module

public import Statement.Fast.Schemes

@[expose] public section

/-!
# The crates' known answers against the statement's signature schemes

`signature-kat DIR` runs the statement's key generation, signer and verifier, compiled over
Keccak-f[1600], on the EthLib test vectors the crates vendor (`DIR` is this repository's `crates`,
the vectors `lean_xmss/tests/lean_xmss/ethlib` and `lean_sphincs/tests/lean_sphincs/ethlib`: the
`key_gen`, `sign` and `verify` cases of each scheme) and on leanSPHINCS's known answer
(`crates/lean_sphincs/src/known_answer.hex`, given as a second
argument): the bytes must match. An input of the wrong length is rejected (`null`). Each case
prints `ok` or `MISMATCH`; the exit code is the number of mismatches. `--sphincs` and `--xmss` run
one scheme's cases; `--skip-xmss-sign` leaves out leanXMSS's signing cases, four tree builds of
`2^16` leaves each (the key's top tree, then the signer's).
-/

/-!
# The signers, compiled fast

Speed only, as `Statement/Fast/Schemes.lean` does for the verifiers: compiled, `sequenceFin`'s
`Fin.cases` looks up an index at a cost exponential in it, so the key generation and signing
functions above it are restated here word for word, each equal to its definition (`rfl`, by
induction for the counter search), and swapped in by `@[csimp]`, which acts where code is compiled:
in this module. (`scripts/signature-kat-fast.py` writes this section from the statement.)
-/

namespace Sphincs.KeyGenerationAndSigning

open Verification HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

def otsSecretsFast (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chainIndex ↦ prf π key (.oneTimeChain layer tree leaf chainIndex)

@[csimp] theorem otsSecrets_eq_fast : @otsSecrets = @otsSecretsFast := rfl

def otsPublicLeafFast (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m Digest := do
  let secrets ← otsSecrets π key layer tree leaf
  let endpoints ← sequenceFin fun chainIndex =>
    chainWalk π key.publicSeed layer tree leaf chainIndex 0 (chainLength - 1) (secrets chainIndex)
  leafHash π key.publicSeed layer tree leaf endpoints

@[csimp] theorem otsPublicLeaf_eq_fast : @otsPublicLeaf = @otsPublicLeafFast := rfl

def otsSignFromFast (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode π key.publicSeed layer tree leaf message
          (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets π key layer tree leaf
          let values ← sequenceFin fun chainIndex =>
            chainWalk π key.publicSeed layer tree leaf chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFromFast key layer tree leaf message attempts (counter + 1)

@[csimp] theorem otsSignFrom_eq_fast : @otsSignFrom = @otsSignFromFast := by
  funext m _ π key layer tree leaf message attempts start
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      simp only [otsSignFrom, otsSignFromFast]
      congr 1
      funext result
      cases result <;> simp [ih]

def otsSignFast (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom π key layer tree leaf message encodingAttemptLimit 0

@[csimp] theorem otsSign_eq_fast : @otsSign = @otsSignFast := rfl

def treeLevelsFast (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    m (List (List Digest)) := do
  let leaves ← (List.range (2 ^ layerHeight layer)).mapM fun leaf ↦
    otsPublicLeaf π key layer tree (leafOfNat leaf)
  merkleLevels
    (fun height nodeIndex ↦ tweakableHash π key.publicSeed (.node layer tree height nodeIndex))
    leaves (layerHeight layer)

@[csimp] theorem treeLevels_eq_fast : @treeLevels = @treeLevelsFast := rfl

def forsOpenFast (key : ExpandedKey) (index : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    m (Digest × (ForsTreeIndex → ForsTreeOpening)) := do
  let trees ← sequenceFin fun forsTree => forsTreeOpen π key index forsTree (leaves forsTree)
  let forsKey ← forsPublicKey π key.publicSeed index fun forsTree => (trees forsTree).1
  return (forsKey, fun forsTree => (trees forsTree).2)

@[csimp] theorem forsOpen_eq_fast : @forsOpen = @forsOpenFast := rfl

def keygenInternalFast (key : ExpandedKey) : m (PublicKey × List (List Digest)) := do
  let top ← treeLevels π key topLayer 0
  return (⟨key.publicSeed, levelNode top (layerHeight topLayer) 0⟩, top)

@[csimp] theorem keygenInternal_eq_fast : @keygenInternal = @keygenInternalFast := rfl

def keygenFromSeedFast (secretSeed : SecretKey) : m (PublicKey × SecretKey) := do
  let key ← expandKey π secretSeed
  let (publicKey, _) ← keygenInternal π key
  return (publicKey, secretSeed)

@[csimp] theorem keygenFromSeed_eq_fast : @keygenFromSeed = @keygenFromSeedFast := rfl

def signLayerFast (key : ExpandedKey) (top : List (List Digest)) (index : Index) (layer : Layer)
    (message : Digest) : m (Option (LayerSignature layer × Digest)) := do
  let tree := treeOfIndex layer index
  let leaf := leafOfIndex layer index
  let some (counter, values) ← otsSign π key layer tree leaf message | return none
  let levels ← if layer = topLayer then pure top else treeLevels π key layer tree
  return some (⟨counter, values, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩,
    levelNode levels (layerHeight layer) 0)

@[csimp] theorem signLayer_eq_fast : @signLayer = @signLayerFast := rfl

def signWithExpandedKeyFast (key : ExpandedKey) (message : Message) : m (Option Signature) := do
  let (publicKey, top) ← keygenInternal π key
  let randomizer ← prfMessage π key.secretPrfKey key.publicSeed message
  let digest ← messageDigest π publicKey randomizer message
  let index := digestIndex digest
  let (forsKey, forsOpening) ← forsOpen π key index (digestForsLeaves digest)
  let some (bottom, bottomRoot) ← signLayer π key top index 0 forsKey | return none
  let some (middle, middleRoot) ← signLayer π key top index 1 bottomRoot | return none
  let some (topSignature, _) ← signLayer π key top index 2 middleRoot | return none
  return some ⟨randomizer, forsOpening, layerSignatures bottom middle topSignature⟩

@[csimp] theorem signWithExpandedKey_eq_fast : @signWithExpandedKey = @signWithExpandedKeyFast := rfl

def signFast (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let key ← expandKey π secretKey
  signWithExpandedKey π key message

@[csimp] theorem sign_eq_fast : @sign = @signFast := rfl

end Sphincs.KeyGenerationAndSigning

namespace LeanXmss.KeyGenerationAndSigning

open Verification HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

def otsSecretsFast (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun chainPairIndex : ChainPairIndex =>
    thPair π parameter (keygenDomainFields (.oneTimeChainPair layer key chainPairIndex))
      (littleEndianBytes 32 seed)
  return fun chainIndex => hashHalfForChain chainIndex.val (outputs (chainPair chainIndex))

@[csimp] theorem otsSecrets_eq_fast : @otsSecrets = @otsSecretsFast := rfl

def oneTimePublicKeyFast (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets π parameter layer key seed
  sequenceFin fun chainIndex =>
    chainWalk π parameter layer key chainIndex 0 (chainLength - 1) (secrets chainIndex)

@[csimp] theorem oneTimePublicKey_eq_fast : @oneTimePublicKey = @oneTimePublicKeyFast := rfl

def otsSignFromFast (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) (randomizerBase : Randomizer) :
    Nat → Nat → m (Option (Randomizer × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomizer := randomizerBase + BitVec.ofNat digestBits trial
      let digest ← messageDigest π parameter layer key message randomizer
      match Codeword.decode digest with
      | some encoding => do
          let secrets ← otsSecrets π parameter layer key seed
          let values ← sequenceFin fun chainIndex =>
            chainWalk π parameter layer key chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (randomizer, values)
      | none => otsSignFromFast parameter layer key seed message randomizerBase attempts (trial + 1)

@[csimp] theorem otsSignFrom_eq_fast : @otsSignFrom = @otsSignFromFast := by
  funext m _ π parameter layer a b c d attempts start
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      simp only [otsSignFrom, otsSignFromFast]
      congr 1
      funext result
      cases Codeword.decode result <;> simp [ih]

def otsSignFast (parameter : PublicParameter) (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) : m (Option (Randomizer × (ChainIndex → Digest))) := do
  -- `R0`, the randomizer base (`TWEAK_RANDOMIZER = 7`)
  let randomizerBase ← th π parameter (tweakFields 7 0 (layerHi layer 0) key)
    (littleEndianBytes 32 seed ++ message)
  otsSignFrom π parameter layer key seed message randomizerBase randomizerAttemptLimit 0

@[csimp] theorem otsSign_eq_fast : @otsSign = @otsSignFast := rfl

def treeNodeFast (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) : Nat → Nat
    → m Digest :=
  buildTree (fun nodeIndex ↦ do
      let key : KeyIndex := ⟨nodeIndex % lifetime, Nat.mod_lt _ (by decide)⟩
      leafHash π parameter layer key (← oneTimePublicKey π parameter layer key seed))
    fun level nodeIndex ↦ tweakableHash π parameter (.node layer (level + 1) nodeIndex)

@[csimp] theorem treeNode_eq_fast : @treeNode = @treeNodeFast := rfl

def treePathFast (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed) (key : KeyIndex) :
    m (Fin layerHeight → Digest) :=
  sequenceFin fun level =>
    treeNode π parameter layer seed level.val (Nat.xor (key.val / 2 ^ level.val) 1)

@[csimp] theorem treePath_eq_fast : @treePath = @treePathFast := rfl

def keygenFromSeedFast (masterSeed : MasterSeed) : m (PublicKey × SecretKey) := do
  let seed ← schemeSeedOf π masterSeed
  let parameter ← publicParameterOf π seed
  let root ← treeNode π parameter topLayer seed layerHeight 0
  return (⟨root, parameter⟩, ⟨masterSeed, parameter⟩)

@[csimp] theorem keygenFromSeed_eq_fast : @keygenFromSeed = @keygenFromSeedFast := rfl

def signLayerFast (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) : m (Option LayerSignature) := do
  let some (randomizer, values) ← otsSign π parameter layer key seed message | return none
  let path ← treePath π parameter layer seed key
  return some ⟨randomizer, values, path⟩

@[csimp] theorem signLayer_eq_fast : @signLayer = @signLayerFast := rfl

def signWithSchemeSeedFast (seed : MasterSeed) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) : m (Option Signature) := do
  let bottomKey := keyIndexOnLayer leafIndex bottomLayer
  let topKey := keyIndexOnLayer leafIndex topLayer
  let some bottom ← signLayer π seed parameter bottomLayer bottomKey (littleEndianBytes 32 message)
    | return none
  let bottomRoot ← treeNode π parameter bottomLayer seed layerHeight topKey.val
  let some top ← signLayer π seed parameter topLayer topKey (littleEndianBytes 16 bottomRoot)
    | return none
  return some ⟨leafIndex, fun layer => if layer = bottomLayer then bottom else top⟩

@[csimp] theorem signWithSchemeSeed_eq_fast : @signWithSchemeSeed = @signWithSchemeSeedFast := rfl

def signFast (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    m (Option Signature) := do
  let seed ← schemeSeedOf π secretKey.keySeed
  signWithSchemeSeed π seed secretKey.parameter leafIndex message

@[csimp] theorem sign_eq_fast : @sign = @signFast := rfl

end LeanXmss.KeyGenerationAndSigning

open HashSig

namespace SignatureKat

/-- Keccak-f[1600] as a computation of the state monad: under `Id` the compiler duplicates the pure
bindings of the schemes' `do` blocks (each derivation recomputed at each use), so the
cases run the statement's definitions over `StateM Unit`, whose binds it keeps. -/
def keccak (state : LeanVM.Semantics.KeccakState) : StateM Unit LeanVM.Semantics.KeccakState :=
  pure (LeanVM.Semantics.keccakF1600 state)

/-! ## Bytes -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

partial def hexBytes (s : String) : Option (List UInt8) :=
  let s : String := if s.startsWith "0x" then (s.drop 2).toString else s
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
        let hi ← hexDigit a
        let lo ← hexDigit b
        return (UInt8.ofNat (16 * hi + lo)) :: (← go rest)
    | [_] => none
  go s.toList

def hexOf (bytes : List UInt8) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  "0x" ++ String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

/-- Bytes read little endian. -/
def leNat (bytes : List UInt8) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

def bitVecOf (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n)) :=
  if bytes.length = n then some (BitVec.ofNat (8 * n) (leNat bytes)) else none

/-- A cursor over bytes. -/
abbrev Reader := StateT (List UInt8) Option

def take (n : Nat) : Reader (BitVec (8 * n)) := do
  let bytes ← get
  if bytes.length < n then failure
  set (bytes.drop n)
  return BitVec.ofNat (8 * n) (leNat (bytes.take n))

/-- `n` bytes read big endian. -/
def takeBigEndian (n : Nat) : Reader (BitVec (8 * n)) := do
  let bytes ← get
  if bytes.length < n then failure
  set (bytes.drop n)
  return BitVec.ofNat (8 * n) (leNat (bytes.take n).reverse)

def readFin {n : Nat} {α : Type} [Inhabited α] (read : Fin n → Reader α) : Reader (Fin n → α) := do
  let values ← (List.finRange n).mapM read
  return fun i => values.getD i.val default

/-! ## leanSPHINCS -/

namespace Sphincs
open _root_.Sphincs

/-- `LeanSphincsPublicKey::to_bytes`: `PK.seed ‖ PK.root`. -/
def publicKeyBytes (publicKey : _root_.Sphincs.PublicKey) : List UInt8 :=
  publicKey.toBytes

/-- A layer: its counter, big endian, its chain values and its path (`to_bytes`). -/
def layerBytes (layer : Layer) (signature : LayerSignature layer) : List UInt8 :=
  bigEndianBytes 4 signature.counter ++
    (List.ofFn fun chain => littleEndianBytes 16 (signature.chainValues chain)).flatten ++
    (List.ofFn fun level => littleEndianBytes 16 (signature.authenticationPath level)).flatten

/-- `LeanSphincsSignature::to_bytes`: the randomizer, the FORS openings, each layer bottom first. -/
def signatureBytes (signature : Signature) : List UInt8 :=
  littleEndianBytes 16 signature.randomizer ++
    (List.ofFn fun tree => littleEndianBytes 16 (signature.forsOpening tree).secret ++
      (List.ofFn fun level => littleEndianBytes 16 ((signature.forsOpening tree).path level)).flatten
      ).flatten ++
    (List.ofFn fun layer : Layer => layerBytes layer (signature.layers layer)).flatten

instance : Inhabited ForsTreeOpening := ⟨⟨0, fun _ => 0⟩⟩

def readLayer (layer : Layer) : Reader (LayerSignature layer) := do
  let counter ← takeBigEndian 4
  let chainValues ← readFin fun _ : ChainIndex => take 16
  let path ← readFin fun _ : Fin (layerHeight layer) => take 16
  return ⟨counter, chainValues, path⟩

def readSignature : Reader Signature := do
  let randomizer ← take 16
  let fors ← readFin fun _ : ForsTreeIndex => do
    let secret ← take 16
    let path ← readFin fun _ : Fin forsTreeHeight => take 16
    return (⟨secret, path⟩ : ForsTreeOpening)
  let bottom ← readLayer 0
  let middle ← readLayer 1
  let top ← readLayer 2
  return ⟨randomizer, fors, KeyGenerationAndSigning.layerSignatures bottom middle top⟩

def signatureOf (bytes : List UInt8) : Option Signature :=
  match readSignature.run bytes with
  | some (signature, []) => some signature
  | _ => none

/-- `LeanSphincsPublicKey::from_bytes`: `PK.seed`, then `PK.root`. -/
def publicKeyOf (bytes : List UInt8) : Option _root_.Sphincs.PublicKey :=
  if bytes.length = 32 then
    some ⟨BitVec.ofNat 128 (leNat (bytes.take 16)), BitVec.ofNat 128 (leNat (bytes.drop 16))⟩
  else none

def keygen (seed : MasterSeed) : _root_.Sphincs.PublicKey :=
  ((KeyGenerationAndSigning.keygenFromSeed (m := StateM Unit) keccak seed).run' ()).1

def sign (seed : MasterSeed) (message : Message) : Option Signature :=
  (KeyGenerationAndSigning.sign (m := StateM Unit) keccak seed message).run' ()

def verify (publicKey : _root_.Sphincs.PublicKey) (message : Message) (signature : Signature) :
    Bool :=
  (Verification.verify (m := StateM Unit) keccak publicKey message signature).run' ()

end Sphincs

/-! ## leanXMSS -/

namespace Xmss
open LeanXmss

def publicKeyBytes (publicKey : PublicKey) : List UInt8 :=
  littleEndianBytes 16 publicKey.root ++ littleEndianBytes 16 publicKey.parameter

/-- `LeanXmssPublicKey::from_bytes`: the root, then the parameter. -/
def publicKeyOf (bytes : List UInt8) : Option PublicKey :=
  if bytes.length = 32 then
    some ⟨BitVec.ofNat 128 (leNat (bytes.take 16)), BitVec.ofNat 128 (leNat (bytes.drop 16))⟩
  else none

def layerBytes (signature : LayerSignature) : List UInt8 :=
  littleEndianBytes 16 signature.randomizer ++
    (List.ofFn fun chain => littleEndianBytes 16 (signature.chainValues chain)).flatten ++
    (List.ofFn fun level => littleEndianBytes 16 (signature.authenticationPath level)).flatten

/-- `LeanXmssSignature::to_bytes`: the leaf index, the bottom layer, the top layer. -/
def signatureBytes (signature : Signature) : List UInt8 :=
  littleEndianBytes 4 (BitVec.ofNat 32 signature.leafIndex.val) ++
    layerBytes (signature.layers bottomLayer) ++ layerBytes (signature.layers topLayer)

def readLayer : Reader LayerSignature := do
  let randomizer ← take 16
  let chainValues ← readFin fun _ : ChainIndex => take 16
  let path ← readFin fun _ : Fin layerHeight => take 16
  return ⟨randomizer, chainValues, path⟩

def readSignature : Reader Signature := do
  let index ← take 4
  let bottom ← readLayer
  let top ← readLayer
  return ⟨⟨index.toNat, index.isLt⟩, fun layer => if layer = bottomLayer then bottom else top⟩

def signatureOf (bytes : List UInt8) : Option Signature :=
  match readSignature.run bytes with
  | some (signature, []) => some signature
  | _ => none

def keygen (seed : MasterSeed) : PublicKey :=
  ((KeyGenerationAndSigning.keygenFromSeed (m := StateM Unit) keccak seed).run' ()).1

/-- The key of the seed, as the crate's (`key_gen_from_seed`), then its signature. -/
def sign (seed : MasterSeed) (leafIndex : LeafIndex) (message : Message) : Option Signature :=
  (do
    let (_, secretKey) ← KeyGenerationAndSigning.keygenFromSeed (m := StateM Unit) keccak seed
    KeyGenerationAndSigning.sign (m := StateM Unit) keccak secretKey leafIndex message).run' ()

def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : Bool :=
  (Verification.verify (m := StateM Unit) keccak publicKey message signature).run' ()

end Xmss

/-! ## The cases -/

/-- The value of `key: value` in a case file, quotes removed. -/
def field (lines : List String) (key : String) : Option String :=
  lines.findSome? fun line =>
    let line := line.trimAsciiStart.toString
    if line.startsWith (key ++ ":") then
      some ((((line.drop (key.length + 1)).trimAscii.toString).replace "'" "").replace "\"" "")
    else none

/-- The expected output: some bytes, `true`/`false`, or `none` for `null`. -/
def expected (lines : List String) : Option String :=
  match field lines "output" with
  | some "null" => none
  | other => other

def outputOf (bytes : Option (List UInt8)) : Option String := bytes.map hexOf

def bool (b : Option Bool) : Option String := b.map fun b => if b then "true" else "false"

def runCase (scheme kind : String) (lines : List String) : Option String :=
  let bytes (key : String) : Option (List UInt8) := (field lines key).bind hexBytes
  match scheme, kind with
  | "sphincs", "key_gen" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      return hexOf (Sphincs.publicKeyBytes (Sphincs.keygen seed))
  | "sphincs", "sign" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      let message ← (bytes "message").bind (bitVecOf 32)
      let signature ← Sphincs.sign seed message
      return hexOf (Sphincs.signatureBytes signature)
  | "sphincs", "verify" => do
      let publicKey ← (bytes "public_key").bind Sphincs.publicKeyOf
      let message ← (bytes "message").bind (bitVecOf 32)
      let signature ← (bytes "signature").bind Sphincs.signatureOf
      bool (some (Sphincs.verify publicKey message signature))
  | "xmss", "key_gen" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      return hexOf (Xmss.publicKeyBytes (Xmss.keygen seed))
  | "xmss", "sign" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      let message ← (bytes "message").bind (bitVecOf 32)
      let index ← (field lines "leaf_index").bind String.toNat?
      if h : index < LeanXmss.lifetime then
        let signature ← Xmss.sign seed ⟨index, h⟩ message
        return hexOf (Xmss.signatureBytes signature)
      else none
  | "xmss", "verify" => do
      let publicKey ← (bytes "public_key").bind Xmss.publicKeyOf
      let message ← (bytes "message").bind (bitVecOf 32)
      let signature ← (bytes "signature").bind Xmss.signatureOf
      bool (some (Xmss.verify publicKey message signature))
  | _, _ => none

/-- leanSPHINCS's known answer (`known_answer`, `lean_sphincs/scheme.rs`): the public key
and the signature of `SK.seed[i] = 37 i + 11` and the message `m[i] = 7 i + 3`, `sign_with` on the
expanded key, and its verification. -/
def knownAnswer (path : System.FilePath) : IO Bool := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  -- the constants from the file's length, so that the compiler does not evaluate the known answer
  -- as a closed term at start-up
  let (a, b) := if lines.length = 2 then (37, 7) else (0, 0)
  let seedBytes : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (a * i + 11)
  let messageBytes : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (b * i + 3)
  let seed : MasterSeed := BitVec.ofNat 256 (leNat seedBytes)
  let message : Message := BitVec.ofNat 256 (leNat messageBytes)
  let (publicKey, signature) := (do
      let key ← _root_.Sphincs.KeyGenerationAndSigning.expandKey (m := StateM Unit) keccak seed
      let (publicKey, _) ←
        _root_.Sphincs.KeyGenerationAndSigning.keygenInternal (m := StateM Unit) keccak key
      let signature ←
        _root_.Sphincs.KeyGenerationAndSigning.signWithExpandedKey (m := StateM Unit) keccak key
          message
      return (publicKey, signature) : StateM Unit _).run' ()
  let publicKeyOk := hexOf (Sphincs.publicKeyBytes publicKey) == "0x" ++ lines[0]!
  let signatureOk :=
    (signature.map fun s => hexOf (Sphincs.signatureBytes s)) == some ("0x" ++ lines[1]!)
  let verifyOk := signature.map (Sphincs.verify publicKey message) == some true
  IO.println s!"sphincs known_answer: public key {publicKeyOk}, signature {signatureOk}, verify {verifyOk}"
  return publicKeyOk && signatureOk && verifyOk

end SignatureKat

open SignatureKat in
def main (args : List String) : IO UInt32 := do
  let skipXmssSign := args.contains "--skip-xmss-sign"
  let onlySphincs := args.contains "--sphincs"
  let onlyXmss := args.contains "--xmss"
  let args := args.filter fun arg => !arg.startsWith "--"
  let some (dir : String) := args.head? | do
    IO.eprintln "usage: signature-kat CRATES_DIR [KNOWN_ANSWER_HEX] [--skip-xmss-sign]"
    return 2
  let mut mismatches : UInt32 := 0
  for scheme in ["sphincs", "xmss"] do
    for kind in ["key_gen", "sign", "verify"] do
      if skipXmssSign && scheme == "xmss" && kind == "sign" then continue
      if onlySphincs && scheme != "sphincs" then continue
      if onlyXmss && scheme != "xmss" then continue
      let kindDir : System.FilePath :=
        System.FilePath.mk dir / s!"lean_{scheme}" / "tests" / s!"lean_{scheme}" / "ethlib" / kind
      unless ← kindDir.isDir do continue
      let cases := ((← kindDir.readDir).map (·.path)).qsort (·.toString < ·.toString)
      for case in cases do
        let file := case / "data.yaml"
        unless ← file.pathExists do continue
        let lines := (← IO.FS.readFile file).splitOn "\n"
        let got := runCase scheme kind lines
        let ok := got == expected lines
        IO.println s!"{scheme} {kind} {case.fileName.getD ""}: {if ok then "ok" else "MISMATCH"}"
        unless ok do
          mismatches := mismatches + 1
          IO.println s!"  expected {expected lines}\n  got      {got}"
        (← IO.getStdout).flush
  if let some (hex : String) := args[1]? then
    unless ← knownAnswer (System.FilePath.mk hex) do mismatches := mismatches + 1
  IO.println s!"{mismatches} mismatches"
  return mismatches
