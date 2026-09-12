import SphincsSecurity.Statement

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-- The key of the specification: the public parameter, the layer-`0` root that every digest binds, and every sampled secret. `Gen` samples them independently and uniformly, at every position of the index types, so positions a layer does not have hold secrets nothing reads; the seed derivation of the specification is an implementation of this key, not this key. -/
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest

namespace Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable opaque otsSecretsSampleableType :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType

noncomputable opaque ftsSecretsSampleableType :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)

noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  ftsSecretsSampleableType

/-- `pk_i = Chain(P, 0, 2^w - 1, sk_i)` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)

/-- `OtsSign`: the least admissible counter, and the chain values it dictates. The search starts at `0` and stops after `encodingAttemptLimit` counters. -/
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)

def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0

/-- `X^{lay,tau}_{level,nodeIdx}`, the Merkle tree over the layer's one-time leaves. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- `TreeRoot(P, lay, tau) = X^{lay,tau}_{h_lay, 0}`. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0

/-- `TreePath`: `A_level = X^{lay,tau}_{level, floor(e / 2^level) xor 1}` for the layer's own `h_lay` levels, and nothing above them. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0

/-- `Y^{idx,kappa}_{level,nodeIdx}`, one tree of the forest. -/
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

/-- `FtsKey(P, idx)`, the hash of the forest's `k - 1` roots. -/
def ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest := do
  let roots ← sequenceFin fun tree =>
    ftsNode parameter index tree (secret tree) ftsTreeHeight 0
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-- `FtsOpen`: the opened secrets and, per tree, the `a` siblings of the opened leaf. -/
def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      ftsNode parameter index tree (secret tree) level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

noncomputable def sampleParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)

/-- `Gen`: sample the parameter and every secret, and build layer `0`'s tree for the root. The trees below it are built when a signature needs them, so nothing else is computed here. -/
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let root ← liftM
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) :
      OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret⟩)

/-- One digest attempt: one hash, keeping the index and the leaf indices if the digest is admissible. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- The digest loop: at most `digestAttemptLimit` attempts, each sampling a fresh randomizer, stopping at the first admissible digest. It takes `2^a` attempts on average. -/
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message

/-- The message layer `lay` signs: the root of the tree below it, or the few-time public key at the bottom. Every layer's message is fixed by the index alone, which is what makes the layers independent. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)

/-- One layer's contribution: its counter, its chain values, and its authentication path. -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)

/-- `Sig(sk, m)`: the digest loop, the few-time opening, one one-time signature per layer, and the assembled signature, or nothing as soon as one layer fails. -/
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) => do
      let ftsPath ← liftM
        (ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index) :
          OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      let layers ← liftM
        (sequenceLayers (fun lay => signLayer secretKey index lay) :
          OracleComp HashSpec
            (Option (Layer → Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
      match layers with
      | none => return none
      | some parts => do
          let _ ← liftM
            (treeRoot secretKey.parameter topLayer rootTree (secretKey.otsSecret topLayer rootTree) :
              OracleComp HashSpec Digest)
          return some
            { randomness := randomness
              ftsSecret := fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
              ftsPath := ftsPath
              counter := fun lay => (parts lay).1
              chainValue := fun lay => (parts lay).2.1
              authPath := flattenPaths fun lay => (parts lay).2.2 }

attribute [irreducible] treeNode ftsNode sampleParameter sampleOtsSecrets sampleFtsSecrets keygen sign

end Concrete

/-- The concrete SPHINCS scheme: key generation, the stateless randomized signer, and the verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model, at `2^24` signing requests per key pair. -/
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end SphincsSecurity
