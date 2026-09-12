import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# SPHINCS with a 256-bit master seed

This module contains the complete seeded scheme: parameters, types, serialized hash inputs, key generation, signing, verification, the consistent random-oracle experiment, and the target `SphincsSecurityStatement`. Key generation samples one 32-byte secret seed and derives the public parameter and every signing secret through the same random oracle. Derivation and verification use disjoint domains.

The theorem `sphincs_has_127_bits_of_classical_security` proves the `127`-bit bound, counting every hash call in the experiment.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 191
def numLayers : Nat := 3
def totalHeight : Nat := 26
/-- The tallest layer, `h_0`, which bounds every layer's leaf index. -/
def maxLayerHeight : Nat := 12
def ftsTreeHeight : Nat := 10
/-- The `k` index groups a digest carries. The forest holds `k - 1` trees, the last group being pinned to zero. -/
def ftsTrees : Nat := 15
/-- Signatures allowed per key pair, `q_s`. -/
def signatureLimit : Nat := 2 ^ 24
/-- Digest attempts per signature, `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per layer, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
/-- `idx`, which few-time key signs. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, a tree of any layer. Layer `lay` only uses the values below `2^(sum_{j < lay} h_j)`. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- `e`, a leaf of any layer. Layer `lay` only uses the values below `2^h_lay`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
/-- A tree of the few-time forest, `kappa < k - 1`. -/
abbrev FtsTree := Fin (ftsTrees - 1)
/-- An index group of the message digest, `kappa < k`. The first `k - 1` select a tree's leaf; the last is pinned to zero. -/
abbrev IndexGroup := Fin ftsTrees
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
/-- A position in the signature's authentication path, the `h` nodes of the `d` layers concatenated top layer first. -/
abbrev PathIndex := Fin totalHeight
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- The `d` Merkle heights, `(h_0, h_1, h_2) = (12, 7, 7)`. Layer `0` carries the public key. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else 7

def topLayer : Layer := ⟨0, by decide⟩
def middleLayer : Layer := ⟨1, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The message digest is `h + k * a = 176` bits, an index and `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + ftsTrees * ftsTreeHeight

abbrev MessageDigest := BitVec messageDigestBits

/-- Keep the first `h + k * a` output bits. -/
def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- A signature, with every component the verifier reads and no other: the randomizer, one few-time secret and its `a` path nodes per held tree, and per layer a counter, `v` chain values, and its share of the `h` path nodes. That is `16 + 14 * 16 + 140 * 16 + 3 * 4 + 126 * 16 + 26 * 16 = 4924` bytes. -/
structure Signature where
  randomness : Randomness
  ftsSecret : FtsTree → Digest
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  counter : Layer → Counter
  chainValue : Layer → ChainIndex → Digest
  authPath : PathIndex → Digest
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The five fields of the specification's `enc(t, lay, tau, p, j)`. -/
structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 32
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 1

/-- The specification's 16 tweak bytes `protocol_domain_sep || tag || layer || 0 || position || tree || index`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++ [0] ++
    bytesLE 4 fields.position ++ bytesLE 4 fields.tree ++ bytesLE 4 fields.index

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Nat) (nodeIdx : Nat)
  | ftsRoots (index : Index)
  | message
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. Inside the hypertree the layer field is the layer and the tree field the tree; inside a few-time key they are the tree of the forest and the index that selects the instance. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step =>
      ⟨1#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val,
        BitVec.ofNat 32 (chainLength * chainIdx.val + step.val), BitVec.ofNat 32 leaf.val⟩
  | .leaf lay tree leaf =>
      ⟨2#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .node lay tree level nodeIdx =>
      ⟨3#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val,
        BitVec.ofNat 32 level, BitVec.ofNat 32 nodeIdx⟩
  | .encoding lay tree leaf =>
      ⟨4#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .ftsLeaf index tree leaf =>
      ⟨6#8, BitVec.ofNat 8 tree.val, BitVec.ofNat 32 index.val, 0#32, BitVec.ofNat 32 leaf.val⟩
  | .ftsNode index tree level nodeIdx =>
      ⟨7#8, BitVec.ofNat 8 tree.val, BitVec.ofNat 32 index.val,
        BitVec.ofNat 32 level, BitVec.ofNat 32 nodeIdx⟩
  | .ftsRoots index => ⟨8#8, 0#8, BitVec.ofNat 32 index.val, 0#32, 0#32⟩
  | .message => ⟨9#8, 0#8, 0#32, 0#32, 0#32⟩

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call and by the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | fts (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => ⟨10#8, 0#8, 0#32, 0#32, 0#32⟩
  | .ots lay tree leaf chain =>
      ⟨0#8, BitVec.ofNat 8 lay.val, BitVec.ofNat 32 tree.val,
        BitVec.ofNat 32 chain.val, BitVec.ofNat 32 leaf.val⟩
  | .fts index tree leaf =>
      ⟨5#8, BitVec.ofNat 8 tree.val, BitVec.ofNat 32 index.val, 0#32, BitVec.ofNat 32 leaf.val⟩

/-- `tweak || P || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 191`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz checksum and forces the counter. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- `v / 2 = 21` digits in each half of the digest. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

/-- `x_i`, the three bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment adds uniform sampling through `OracleWorld` and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- `unifSpec` for uniform sampling, `HashSpec` for the random oracle. A query is `.inl` to sample or `.inr` to hash, so `HasHashQueryBound` counts only the hash side. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

def digestBytes (value : Digest) : HashInput := bytesLE 16 value

def messageBytes (message : Message) : HashInput := bytesLE 32 message

def randomnessBytes (randomness : Randomness) : HashInput := bytesLE 16 randomness

def counterBytes (counter : Counter) : HashInput := bytesLE 4 counter

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau_lay = floor(idx / 2^(sum_{j >= lay} h_j))`. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `e_lay = floor(idx / 2^(sum_{j > lay} h_j)) mod 2^h_lay`. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by
      unfold layerHeight maxLayerHeight; split <;> omega))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `Chain_{lay,tau,e,i}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (digestBytes previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap digestBytes

/-- `X^{lay,tau}_{0,e}`, the one-time leaf: the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `Enc(P, lay, tau, e, M, c)`: hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (digestBytes message ++ counterBytes counter)
  return TargetSum.decodeDigest digest

/-- `OtsLeaf`: the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  match ← encode parameter lay tree leaf message counter with
  | none => pure none
  | some encoding => do
      let endpoints ← sequenceFin fun chainIdx =>
        recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
      let value ← leafHash parameter lay tree leaf endpoints
      return some value

/-! ### A layer -/

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  digestBytes left ++ digestBytes right

/-- `TreeFold`: fold a leaf and a path into the layer's root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### The few-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The index group of the digest that selects this tree's leaf. -/
def ftsIndexOf (tree : FtsTree) : IndexGroup :=
  tree.castLE (Nat.sub_le ftsTrees 1)

/-- The last index group, the one the digest is resampled to zero and the verifier checks. Its tree is the dropped one. -/
def lastIndexGroup : IndexGroup := ⟨ftsTrees - 1, by decide⟩

/-- `Y^{idx,kappa}_{0,j}`, the hash of one few-time secret. -/
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (digestBytes secret)

/-- The `k - 1` roots of the forest. -/
def ftsRootsPayload (roots : FtsTree → Digest) : HashInput :=
  (List.ofFn roots).flatMap digestBytes

/-- The verifier's half of one few-time tree. -/
def ftsFold (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← ftsFold parameter index tree leaf path levels value
      let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload sibling current)
      else
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload current sibling)

/-- `FtsRec`: recover the few-time public key from the opened secrets and paths. -/
def ftsRecover (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : m Digest := do
  let roots ← sequenceFin fun tree => do
    let leaf := leaves (ftsIndexOf tree)
    let value ← ftsLeafHash parameter index tree leaf (secrets tree)
    ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-! ### The message digest -/

/-- `rho || root || m`, what the message digest hashes after the tweak and the parameter. -/
def messageDigestPayload (root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  randomnessBytes randomness ++ digestBytes root ++ messageBytes message

/-- `Digest(P, root, m, rho)`, truncated to `h + k * a` bits. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- `u_kappa = floor(N / 2^(h + kappa * a)) mod 2^a`. -/
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun tree => (digest.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toFin

/-- A digest is admissible exactly when its last index group is zero. -/
def Admissible (digest : MessageDigest) : Prop := digestLeaves digest lastIndexGroup = 0

instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (digestLeaves digest lastIndexGroup = 0))

/-! ### Verification -/

/-- Layer `lay`'s share of the signature's authentication path, its `h_lay` nodes starting at offset `sum_{j < lay} h_j`. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : heightAbove lay + level < totalHeight then
    signature.authPath ⟨heightAbove lay + level, hlevel⟩
  else
    0

/-- The hypertree walk, from the bottom layer up: `remaining + 1` enters at layer `remaining`, and layer `0`'s fold returns the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        match ← otsLeaf parameter lay tree leaf message (signature.counter lay)
          (signature.chainValue lay) with
        | none => pure none
        | some value => do
            let root ← treeFold parameter lay tree leaf (signaturePath signature lay)
              (layerHeight lay) value
            verifyLayers parameter index signature remaining root
      else
        pure none

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the few-time key, walk the layers and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬ Admissible digest then
    return false
  else
    let index := digestIndex digest
    let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath
    match ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey with
    | none => return false
    | some root => return decide (root = publicKey.root)

/-! ### Signing randomness and path assembly -/

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness

/-- Layer `0` holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-! ### Signing -/

/-- Run layers from bottom to top, stopping on failure and indexing the results in serialization order. -/
def sequenceLayers {α : Type} (computation : Layer → m (Option α)) : m (Option (Layer → α)) := do
  match ← computation bottomLayer with
  | none => return none
  | some bottom =>
      match ← computation middleLayer with
      | none => return none
      | some middle =>
          match ← computation topLayer with
          | none => return none
          | some top => return some ![top, middle, bottom]

/-- Which layer's path an entry of the `h` belongs to. -/
def layerOfPath (position : Nat) : Layer :=
  if position < heightAbove middleLayer then topLayer
  else if position < heightAbove bottomLayer then middleLayer
  else bottomLayer

/-- Lay the `d` layers' paths end to end, top layer first, so that every one of the `h` entries is read by verification. -/
def flattenPaths (paths : Layer → Fin maxLayerHeight → Digest) : PathIndex → Digest :=
  fun position =>
    let lay := layerOfPath position.val
    let level := position.val - heightAbove lay
    if hlevel : level < maxLayerHeight then paths lay ⟨level, hlevel⟩ else 0

attribute [irreducible] verify sampleRandomness

end Concrete

def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx => do
    let secret ← deriveKey parameter (.ots lay tree leaf chainIdx) seed
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) secret

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx => do
            let secret ← deriveKey parameter (.ots lay tree leaf chainIdx) seed
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val secret
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf seed message encodingAttemptLimit 0

def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf seed
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree seed level (2 * nodeIdx)
      let right ← treeNode parameter lay tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  treeNode parameter lay tree seed (layerHeight lay) 0

def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0

def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      let secret ← deriveKey parameter (.fts index tree leaf) seed
      ftsLeafHash parameter index tree leaf secret
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree seed level (2 * nodeIdx)
      let right ← ftsNode parameter index tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx) (nodePayload left right)

def ftsKey (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) : m Digest := do
  let roots ← sequenceFin fun tree =>
    ftsNode parameter index tree seed ftsTreeHeight 0
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (seed : MasterSeed) : m (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      ftsNode parameter index tree seed level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

/-- Sample the master seed, derive the public parameter, and build the top tree. -/
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let seed ← liftM sampleMasterSeed
  let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
  let root ← liftM (treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

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

def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      secretKey.seed
  else
    ftsKey secretKey.parameter index secretKey.seed

def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf secretKey.seed message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
      return some (counter, values, path)

noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) => do
      let secrets ← liftM
        (sequenceFin fun tree =>
          deriveKey secretKey.parameter (.fts index tree (leaves (ftsIndexOf tree))) secretKey.seed :
            OracleComp HashSpec (FtsTree → Digest))
      let ftsPath ← liftM
        (ftsOpen secretKey.parameter index leaves secretKey.seed :
          OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
      let layers ← liftM
        (sequenceLayers (fun lay => signLayer secretKey index lay) :
          OracleComp HashSpec
            (Option (Layer → Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))))
      match layers with
      | none => return none
      | some parts => do
          let _ ← liftM
            (treeRoot secretKey.parameter topLayer rootTree secretKey.seed :
              OracleComp HashSpec Digest)
          return some
            { randomness := randomness
              ftsSecret := secrets
              ftsPath := ftsPath
              counter := fun lay => (parts lay).1
              chainValue := fun lay => (parts lay).2.1
              authPath := flattenPaths fun lay => (parts lay).2.2 }

end Seeded

/-! ## The security experiment -/

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- The interface of a stateless signature scheme in the random-oracle experiment. Signing is randomized and may fail, so it returns an option. -/
structure Scheme (Key : Type := Seeded.SecretKey) where
  keygen : OracleComp OracleWorld (PublicKey × Key)
  sign : Key → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Message → Signature → OracleComp OracleWorld Bool

/-- A signing request is a message alone, the scheme being stateless, and the answer is a signature or `none` if the signer fails. -/
abbrev SigningSpec := Message →ₒ Option Signature

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

/-- A signing transcript is valid exactly when the key signed at most `q_s` messages. Nothing forbids repeating a message: the signer is stateless, and a fresh randomizer makes the second signature a different one. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when the transcript contains the same message answered by the same signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle {Key : Type} (scheme : Scheme Key) (sk : Key) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the transcript holds at most `q_s` signatures, the claimed forgery is not one the signer returned for that message, and the signature verifies. -/
noncomputable def gameCore {Key : Type} (scheme : Scheme Key) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle, which starts from the empty cache. The final cache is discarded. -/
noncomputable def forgeAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- Count one per hash call, including cache hits, and zero per uniform sample. -/
noncomputable def countedRomImpl :=
  romImpl.withAddCost (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Every execution of the consistent random oracle uses at most `q` hash calls, including key generation, adversarial hashing, signing, and final verification. -/
def HasHashQueryBound {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅),
    result.2 ≤ q

/-- Having `bits` bits of classical security means that every classical adaptive adversary whose complete experiment stays within a nonzero hash-query budget `q` forges with probability at most `q / 2^bits`. The bound is a slope, so it bounds what a query buys and not what the first one does; a budget below what the honest experiment alone spends admits no adversary and the bound is vacuous there. -/
def HasClassicalSecurityBits {Key : Type} (scheme : Scheme Key) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

noncomputable def Seeded.scheme : Scheme Seeded.SecretKey where
  keygen := Seeded.keygen
  sign := Seeded.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

/-- The security claim for the scheme with a 256-bit master seed. -/
abbrev SphincsSecurityStatement : Prop :=
  HasClassicalSecurityBits Seeded.scheme 127

end SphincsSecurity
