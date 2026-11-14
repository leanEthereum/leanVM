module

public import FORS.Scheme

@[expose] public section

/-!
# The crate's key generation and signer, in FORS's primitives

`key_gen` and `sign` of `crates/lean_sphincs/src/scheme.rs` (leanVM
`40f877dc`), function for function as `Statement/LeanSphincs.lean` transcribes them
(`KeyGenerationAndSigning`), written with FORS's hash inputs, addresses and types: the key
expansion (`LeanSphincsSecretKey::from_bytes`, `SK.prf` then `PK.seed`), the trees built level by level
(`merkle_levels`), the top tree built at key generation and again at each signature (`keygen`),
the randomizer, the digest, each FORS tree built once (`fors_open`), and the layers from the bottom
up, each a WOTS+C signature followed by its tree's levels (the top layer reusing key generation's).

FORS's own key generation and signer (`Seeded.keygen`, `Seeded.sign`, upstream's) compute the same
public key and the same signatures on every answer function, with at most the crate's hash calls
(`CrateStatic.lean`).
-/

namespace FORS.Crate

variable [Params]

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-! ### The key -/

/-- What `slh_keygen_internal` takes (`LeanSphincsSecretKey`'s fields): `SK.seed`, `SK.prf` and
`PK.seed`. -/
structure ExpandedKey where
  secretSeed : MasterSeed
  secretPrfKey : HashOutput
  publicSeed : PublicParameter

/-- `LeanSphincsSecretKey::from_bytes`: `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)`, then
`PK.seed = Trunc_16(H(leanSPHINCS ‖ SK.seed ‖ 0))`, in the order of the crate's struct literal. -/
def expandKey (seed : MasterSeed) : m ExpandedKey := do
  let secretPrfKey ← oracleHash (keySeedInput seed 1)
  let publicSeedOutput ← oracleHash (keySeedInput seed 0)
  return ⟨seed, secretPrfKey, truncateHash publicSeedOutput⟩

/-- `PRF(PK.seed, SK.seed, ADRS)` at a secret's address. -/
def prf (key : ExpandedKey) (domain : KeygenDomain) : m Digest :=
  deriveKey key.publicSeed domain key.secretSeed

/-- `PRF_msg(SK.prf, PK.seed, M')`: the randomizer. -/
def prfMessage (secretPrfKey : HashOutput) (publicSeed : PublicParameter) (message : Message) :
    m Randomness := do
  return truncateHash (← oracleHash (randomizerHashInput secretPrfKey publicSeed message))

/-! ### Trees, level by level -/

/-- Node `index` of a level, `0` past its end. -/
def levelNode (levels : List (List Digest)) (level index : Nat) : Digest :=
  (levels.getD level []).getD index 0

/-- The levels from `below`, at height `height`, up `remaining` levels: `below` first, then node
`j` of the level above hashing nodes `2j` and `2j + 1` (`node (height + 1) j children`). -/
def merkleLevelsFrom (node : Nat → Nat → HashInput → m Digest) (height : Nat)
    (below : List Digest) : Nat → m (List (List Digest))
  | 0 => pure [below]
  | remaining + 1 => do
      let above ← (List.range (below.length / 2)).mapM fun j =>
        node (height + 1) j (nodePayload (below.getD (2 * j) 0) (below.getD (2 * j + 1) 0))
      return below :: (← merkleLevelsFrom node (height + 1) above remaining)

/-- `merkle_levels`: the levels of a tree `height` levels over `leaves`, the leaves first, each
level hashed left to right before the next. -/
def merkleLevels (node : Nat → Nat → HashInput → m Digest) (leaves : List Digest)
    (height : Nat) : m (List (List Digest)) :=
  merkleLevelsFrom node 0 leaves height

/-! ### One-time keys and the hypertree -/

/-- `wots_public_leaf`: the leaf of a one-time key, its chains walked to their ends and hashed. -/
def otsPublicLeaf (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    m Digest := do
  let endpoints ← Seeded.oneTimePublicKey key.publicSeed lay tree leaf key.secretSeed
  leafHash key.publicSeed lay tree leaf endpoints

/-- `wots_sign`: the least admissible counter, then the opened chain values, signing the 16 bytes
of `message`. -/
def otsSign (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : m (Option (Counter × (ChainIndex → Digest))) :=
  Seeded.otsSign key.publicSeed lay tree leaf key.secretSeed (rootPayload message)

/-- `tree_levels`: the levels of tree `tree` of layer `lay`, its leaves first (each a one-time
key's leaf, in leaf order) and its root last. -/
def treeLevels (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) : m (List (List Digest)) := do
  let leaves ← (List.range (2 ^ layerHeight lay)).mapM fun leaf =>
    otsPublicLeaf key lay tree (leafOfNat leaf)
  merkleLevels (fun height nodeIdx payload => tweakableHash key.publicSeed
    (.node lay tree height nodeIdx) payload) leaves (layerHeight lay)

/-! ### FORS -/

/-- A natural read as a FORS leaf. -/
def forsLeafOfNat (value : Nat) : FLeaf :=
  ⟨value % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Node `node` at height `height`, `1 .. a`, of FORS tree `κ` from its children's bytes. -/
def forsNodeHash (publicSeed : PublicParameter) (index : Index) (κ : FTree) (height node : Nat)
    (payload : HashInput) : m Digest :=
  if hheight : height - 1 < forsHeight then
    tweakableHash publicSeed (.forsNode index κ ⟨height - 1, hheight⟩ (forsLeafOfNat node)) payload
  else pure 0

/-- FORS tree `κ` of instance `index`, built once (the closure of `fors_open`): its secrets, its
leaves, its levels; its root, and its opening at `leaf`. -/
def forsTreeOpen (key : ExpandedKey) (index : Index) (κ : FTree) (leaf : FLeaf) :
    m (Digest × TreeOpening) := do
  let secrets ← (List.range (2 ^ forsHeight)).mapM fun s =>
    prf key (.fors index κ (forsLeafOfNat s))
  let leafHashes ← (List.range (2 ^ forsHeight)).mapM fun s =>
    forsLeafHash key.publicSeed index κ (forsLeafOfNat s) (secrets.getD s 0)
  let levels ← merkleLevels (forsNodeHash key.publicSeed index κ) leafHashes forsHeight
  return (levelNode levels forsHeight 0,
    ⟨secrets.getD leaf.val 0, fun z => levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩)

/-- `fors_open`: every tree of instance `index` built once, in tree order, then `T_k` of their
roots; the FORS public key and the opening at the digest's leaves. -/
def forsOpen (key : ExpandedKey) (index : Index) (leaves : FTree → FLeaf) :
    m (Digest × (FTree → TreeOpening)) := do
  let trees ← sequenceFin fun κ => forsTreeOpen key index κ (leaves κ)
  let forsKey ← forsPublicKey key.publicSeed index fun κ => (trees κ).1
  return (forsKey, fun κ => (trees κ).2)

/-! ### Key generation and signing -/

/-- `slh_keygen_internal` (`keygen`): the public key, with the top tree's levels, which signing
reuses. -/
def keygenInternal (key : ExpandedKey) : m (PublicKey × List (List Digest)) := do
  let top ← treeLevels key topLayer rootTree
  return (⟨levelNode top (layerHeight topLayer) 0, key.publicSeed⟩, top)

/-- `key_gen`: the secret key is `SK.seed`, the public key that of its expansion. -/
def keygen (seed : MasterSeed) : m (PublicKey × MasterSeed) := do
  let key ← expandKey seed
  let (publicKey, _) ← keygenInternal key
  return (publicKey, seed)

/-- Layer `lay`'s one-time signature of `message` with its key on the path of `index`, then the
key's tree's levels, built here below the top layer and `top` (key generation's) at it: the layer's
signature with the key's path, and the tree's root, which the layer above signs. -/
def signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index) (lay : Layer)
    (message : Digest) : m (Option (LayerSignature lay × Digest)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let some (counter, values) ← otsSign key lay tree leaf message | return none
  let levels ← if lay = topLayer then pure top else treeLevels key lay tree
  return some (⟨counter, values, fun z => levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩,
    levelNode levels (layerHeight lay) 0)

/-- The crate's `sign`: key generation's top tree and public key, the randomizer, the digest's index and
leaves, the FORS instance built once (its key and its opening), then the layers from the bottom up
(`sequenceThread` runs the last layer, the bottom one, first), each signing what the layer below
gives: the FORS public key at the bottom, the root of the tree below above it. -/
def signWithExpandedKey (key : ExpandedKey) (message : Message) : m (Option Signature) := do
  let (publicKey, top) ← keygenInternal key
  let randomizer ← prfMessage key.secretPrfKey key.publicSeed message
  let digest ← messageDigest publicKey.parameter publicKey.root message randomizer
  let index := digestIndex digest
  let (forsKey, opening) ← forsOpen key index (digestLeaves digest)
  let some layers ← sequenceThread (fun lay below => signLayer key top index lay below) forsKey
    | return none
  return some ⟨randomizer, opening, layers⟩

/-- The key's expansion (`LeanSphincsSecretKey::from_bytes`), then the crate's `sign`. -/
def sign (seed : MasterSeed) (message : Message) : m (Option Signature) := do
  let key ← expandKey seed
  signWithExpandedKey key message

end FORS.Crate
