module

public import Quantum.Qrom.Regroup
public import Quantum.Qrom.Sphincs.Slots
public import Quantum.Qrom.Xmss.HonestTable
public import Quantum.Sphincs.HonestTable.Disclosure

@[expose] public section

/-!
# leanSPHINCS's honest table in the random-oracle model

Every hash call of leanSPHINCS's key generation, and every hash call of the signer except the
encoding trials and call 1 of `H_msg`, has an input fixed by the secret key `SK.seed` and the
outputs of earlier calls. These calls are the positions `Pos` of a lazy table
(`Quantum.Qrom.LazyTable`) of the random function `F : HashDomain → Y × Y` that answers the
scheme's hash `H = regroup hmsgRoute F` (`Quantum.Qrom.Regroup`): the two calls of `H_msg` on a
message are one cell, its value the pair of their outputs.

* `RawPos`, `Pos`: the key expansion's two calls, the WOTS+C chain starts, chain steps and leaves
  and the hypertree nodes of the trees in use, the FORS secrets, leaves, nodes and roots
  compressions, and for every message `M` its randomizer `R(M)` (`prfMsg M`) and its digest cell
  (`hmsg M`, call 0 of `H_msg` at `R(M)`). `QTable = Pos → Y × Y`.
* The honest values read from a table: `QTable.publicKey`, `chainValue`, `treeValue`,
  `forsValue`, `randomizer`, `digestOutput` (call 0 the first component, call 1 the second),
  `messageDigest`; with the hash `H` read at the encoding trials, `select`, `signature`.
* `posSlot`, `posPayload`, `cellOf S0 p v`: the slot, payload and cell of a position, a function
  of the values at positions of lower rank; `table S0`: the `LazyTable Pos HashDomain (Y × Y)`
  (`inj` from `cell_injective`). `Consistent S0 v F`: `F` holds `v` at its cells, exactly when `v`
  is the table of `F` (`consistent_iff`); then the regrouped `H` agrees with `v` (`Agrees`,
  `agrees_regroup`).
* `qromEvalDistMap_eq_tableAvg_regroup`: a program against uniform `H`, observed through a
  function of the regrouped table, has the law of the average over uniform `v` of the regrouped
  program against runtime 1 with the cells of `v` hardwired.
* The honest computations as cell reads: in any lawful monad, a hash answering the positions'
  inputs, the digest's call 1 and the encoding trials purely returns the table's keys and
  signature (`keygenFromSeed_eq_pure`, `sign_eq_pure`). So any implementation answering `H` purely
  on those cells makes `sphincsRom` return them (`simulateQ_generateKeys_eq`,
  `simulateQ_sign_eq`); with `honestEval H x` (`Quantum.Qrom.Xmss.honestEval`, the result and the
  hashed cells), `eval_generateKeys`, `eval_sign`, `cellReads_generateKeys`, `signReads_sign`.
* `QTable.valuePos`, `disclosedBy`, `disclosures`: the values at the symbolic positions
  (`Quantum.Sphincs.ValPos`) and the positions a signature discloses, for the symbolic `Known` and
  `Public`; `signature_eq_some`: a signature's values are the values at the disclosed positions.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig hiding PublicKey
open HashSig.OverPermutation (nodePayload sequenceFin walkChain)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput levelNode merkleLevels
  merkleLevelsFrom layerSignatures)
open Quantum.Sphincs (Slot ValPos cpos tpos fpos rootPos treeBits forsDisclosed layerDisclosed
  Key keyOf indexBelow msgPos treeOfIndex_zero leafOfIndex_zero layerHeight_le leafOfIndex_lt
  treeOfIndex_topLayer forsLeafOfNat_val shiftRight_xor_lt getD_map_range lt_two_pow_of_lt
  two_pow_layerHeight_le levelNode_cons_zero levelNode_cons_succ messageDigestInput
  prfMessageInput)
open Quantum.SufCma (QueriesSatisfy queries trace trace_query_bind queriesSatisfy_pure)
open Quantum.Sponge (spongeHardwiredReadRuntime)
open Quantum.Qrom.Xmss (romAnswers honestEval)

namespace Quantum.Qrom.Sphincs

/-! ## Positions -/

set_option synthInstance.maxSize 1024 in
/-- **A hash call of the honest table**, its indices unrestricted (`Pos` keeps those in use). -/
inductive RawPos where
  /-- `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)`. -/
  | prfKey
  /-- `PK.seed`, from `H(leanSPHINCS ‖ SK.seed ‖ 0)`. -/
  | publicSeed
  /-- The start of chain `i` of the one-time key `(l, τ, e)`, a `PRF` call. -/
  | chainStart (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex)
  /-- The step leaving position `step` of chain `i` of the one-time key `(l, τ, e)`. -/
  | chain (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (step : ChainStep)
  /-- The leaf of the one-time key `(l, τ, e)`. -/
  | leaf (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
  /-- Node `index` at height `level + 1` of tree `τ` of layer `l`. -/
  | node (l : Layer) (τ : TreeIndex) (level : Fin (layerHeight topLayer)) (index : TreeLeafIndex)
  /-- The secret of leaf `s` of FORS tree `κ` of instance `idx`, a `PRF` call. -/
  | forsSecret (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex)
  /-- The FORS leaf `s` of tree `κ` of instance `idx`. -/
  | forsLeaf (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex)
  /-- Node `node` at height `level + 1` of FORS tree `κ` of instance `idx`. -/
  | forsNode (idx : Index) (κ : ForsTreeIndex) (level : Fin forsTreeHeight) (node : ForsLeafIndex)
  /-- The FORS public key of instance `idx`. -/
  | forsRoots (idx : Index)
  /-- The randomizer `R(M)`, `PRF_msg`. -/
  | prfMsg (message : Message)
  /-- The digest cell of `M`: call 0 of `H_msg` at `R(M)`, holding both calls' outputs. -/
  | hmsg (message : Message)
  deriving DecidableEq, Fintype

/-- **The positions in use**: the keys and nodes of the trees of the hypertree (tree `τ` of layer
`l` below `2^(treeBits l)`, leaves below `2^(h_l)`, nodes at heights `1` to `h_l`), the FORS nodes
at heights `1` to `a`. -/
def RawPos.InRange : RawPos → Prop
  | .chainStart l τ e _ => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .chain l τ e _ _ => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .leaf l τ e => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .node l τ level index =>
      τ.val < 2 ^ treeBits l ∧ level.val < layerHeight l ∧
        index.val < 2 ^ (layerHeight l - (level.val + 1))
  | .forsNode _ _ level j => j.val < 2 ^ (forsTreeHeight - (level.val + 1))
  | _ => True

instance instDecidablePredRawPosInRange : DecidablePred RawPos.InRange := fun p ↦ by
  cases p <;> unfold RawPos.InRange <;> infer_instance

/-- **A position of the honest table.** -/
abbrev Pos : Type :=
  {p : RawPos // p.InRange}

instance instFintypePos : Fintype Pos :=
  Subtype.fintype _

/-- The randomizer position of `M`. -/
def rndPos (message : Message) : Pos :=
  ⟨.prfMsg message, trivial⟩

/-- The digest cell's position of `M`. -/
def digPos (message : Message) : Pos :=
  ⟨.hmsg message, trivial⟩

/-- The order of the honest computation: a position's input reads values of lower rank only. -/
def RawPos.rank : RawPos → ℕ
  | .prfKey | .publicSeed => 0
  | .chainStart .. | .forsSecret .. | .prfMsg _ => 1
  | .chain _ _ _ _ step => 2 + step.val
  | .leaf .. => 1 + chainLength
  | .node _ _ level _ => 2 + chainLength + level.val
  | .forsLeaf .. => 2
  | .forsNode _ _ level _ => 3 + level.val
  | .forsRoots _ => 3 + forsTreeHeight
  | .hmsg _ => 2 + chainLength + layerHeight topLayer

theorem treeOfIndex_lt (l : Layer) (idx : Index) : (treeOfIndex l idx).val < 2 ^ treeBits l := by
  have hi : idx.val < 2 ^ 26 := idx.isLt
  fin_cases l <;>
    simp only [treeOfIndex, treeBits, indexBits, bitsBelowLayer, layerHeight] <;> norm_num <;> omega

theorem layerHeight_topLayer : layerHeight topLayer = 10 :=
  rfl

theorem two_le_chainLength : 2 ≤ chainLength := by
  decide

/-! ## The honest values of a table -/

/-- **The honest table's values**: one pair of hash outputs per position (a digest cell holds the
outputs of both `H_msg` calls, every other position its output first). -/
abbrev QTable : Type :=
  Pos → HashOutput × HashOutput

namespace QTable

variable (v : QTable)

/-- The output of a position (`0` outside the positions in use). -/
def out (p : RawPos) : HashOutput :=
  if h : p.InRange then (v ⟨p, h⟩).1 else 0

/-- `Trunc_16` of a position's output. -/
def dig (p : RawPos) : Digest :=
  truncateHash (v.out p)

theorem out_of_inRange {p : RawPos} (hp : p.InRange) : v.out p = (v ⟨p, hp⟩).1 :=
  dite_eq_left hp

/-- `SK.prf`. -/
def prfKey : HashOutput :=
  v.out .prfKey

/-- `PK.seed`. -/
def publicSeed : PublicParameter :=
  v.dig .publicSeed

/-- The expanded key of `SK.seed = S0`. -/
def expandedKey (S0 : MasterSeed) : ExpandedKey :=
  ⟨S0, v.prfKey, v.publicSeed⟩

@[simp]
theorem expandedKey_secretSeed (S0 : MasterSeed) : (v.expandedKey S0).secretSeed = S0 :=
  rfl

@[simp]
theorem expandedKey_secretPrfKey (S0 : MasterSeed) : (v.expandedKey S0).secretPrfKey = v.prfKey :=
  rfl

@[simp]
theorem expandedKey_publicSeed (S0 : MasterSeed) : (v.expandedKey S0).publicSeed = v.publicSeed :=
  rfl

/-- Position `j` of chain `i` of the one-time key `(l, τ, e)` (`0` past the end, as `walkChain`):
the start at `0`. -/
def chainValue (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : ℕ → Digest
  | 0 => v.dig (.chainStart l τ e i)
  | j + 1 => if h : j < chainLength - 1 then v.dig (.chain l τ e i ⟨j, h⟩) else 0

/-- The chain ends of a one-time key. -/
def endpoints (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : Digest :=
  v.chainValue l τ e i (chainLength - 1)

/-- The value of tree `τ` of layer `l` at `level`, index `index`: the one-time leaf of key
`leafOfNat index` at level `0`, else the node. -/
def treeValue (l : Layer) (τ : TreeIndex) : ℕ → ℕ → Digest
  | 0, index => v.dig (.leaf l τ (leafOfNat index))
  | level + 1, index =>
      if h : level < layerHeight topLayer ∧ index < 2 ^ layerHeight topLayer then
        v.dig (.node l τ ⟨level, h.1⟩ ⟨index, h.2⟩)
      else 0

/-- The root of tree `τ` of layer `l`. -/
def treeRoot (l : Layer) (τ : TreeIndex) : Digest :=
  v.treeValue l τ (layerHeight l) 0

/-- `PK.root`, the root of the top tree. -/
def root : Digest :=
  v.treeRoot topLayer 0

/-- The public key. -/
def publicKey : PublicKey :=
  ⟨v.publicSeed, v.root⟩

@[simp]
theorem publicKey_publicSeed : v.publicKey.publicSeed = v.publicSeed :=
  rfl

@[simp]
theorem publicKey_root : v.publicKey.root = v.root :=
  rfl

/-- The secret of leaf `s` of FORS tree `κ` of instance `idx`. -/
def forsSecret (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) : Digest :=
  v.dig (.forsSecret idx κ s)

/-- The value of FORS tree `κ` of instance `idx` at `height`, node `j`: the FORS leaf of leaf
`forsLeafOfNat j` at height `0`, else the node. -/
def forsValue (idx : Index) (κ : ForsTreeIndex) : ℕ → ℕ → Digest
  | 0, j => v.dig (.forsLeaf idx κ (forsLeafOfNat j))
  | h + 1, j =>
      if hh : h < forsTreeHeight ∧ j < 2 ^ forsTreeHeight then
        v.dig (.forsNode idx κ ⟨h, hh.1⟩ ⟨j, hh.2⟩)
      else 0

/-- The root of FORS tree `κ` of instance `idx`. -/
def forsRoot (idx : Index) (κ : ForsTreeIndex) : Digest :=
  v.forsValue idx κ forsTreeHeight 0

/-- The FORS public key of instance `idx`. -/
def forsKey (idx : Index) : Digest :=
  v.dig (.forsRoots idx)

/-- The randomizer `R(M)`. -/
def randomizer (message : Message) : Randomizer :=
  v.dig (.prfMsg message)

/-- Call `call` of `H_msg(R(M), PK.seed, PK.root, M)`: the digest cell's first component for call
`0`, its second for call `1`. -/
def digestOutput (message : Message) (call : DigestCall) : HashOutput :=
  if call = 0 then (v (digPos message)).1 else (v (digPos message)).2

theorem digestOutput_zero (message : Message) : v.digestOutput message 0 = (v (digPos message)).1 :=
  ite_eq_left rfl

theorem digestOutput_one (message : Message) : v.digestOutput message 1 = (v (digPos message)).2 :=
  ite_eq_right (by decide)

/-- The message digest of `M`. -/
def messageDigest (message : Message) : MessageDigest :=
  truncateMessageDigest (v.digestOutput message)

/-- The index of `M`'s signature. -/
def index (message : Message) : Index :=
  digestIndex (v.messageDigest message)

/-- The FORS leaves of `M`'s signature. -/
def leaves (message : Message) : ForsTreeIndex → ForsLeafIndex :=
  digestForsLeaves (v.messageDigest message)

/-- The FORS opening of instance `idx` at the leaves `lv`. -/
def forsOpening (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    ForsTreeIndex → ForsTreeOpening :=
  fun κ ↦ ⟨v.forsSecret idx κ (lv κ),
    fun z ↦ v.forsValue idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)⟩

/-- The authentication path of key `e` in tree `τ` of layer `l`. -/
def authPath (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (z : Fin (layerHeight l)) : Digest :=
  v.treeValue l τ z.val ((e.val >>> z.val) ^^^ 1)

/-- **What `K_l(idx)` signs** in every signature of index `idx`: the FORS key of `idx` at the
bottom, the root of the tree below above it. -/
def layerMessage (idx : Index) (l : Layer) : Digest :=
  if h : l.val = 0 then v.forsKey idx
  else v.treeRoot ⟨l.val - 1, by omega⟩ (treeOfIndex ⟨l.val - 1, by omega⟩ idx)

theorem layerMessage_zero (idx : Index) : v.layerMessage idx 0 = v.forsKey idx :=
  rfl

theorem layerMessage_one (idx : Index) :
    v.layerMessage idx 1 = v.treeRoot 0 (treeOfIndex 0 idx) :=
  rfl

theorem layerMessage_two (idx : Index) :
    v.layerMessage idx 2 = v.treeRoot 1 (treeOfIndex 1 idx) :=
  rfl

end QTable

/-! ## The cells read beside the table -/

/-- The cell of an encoding trial of the one-time key `(l, τ, e)` under `PK.seed = seed`. -/
def encCell (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (message : Digest) (counter : EncodingCounter) : Qrom.HashDomain :=
  cell ⟨0, 0, seed⟩ 0 (.enc l τ e) (message, counter)

/-- The cell of call `call` of `H_msg` at the randomizer `R`, under `PK.seed = seed` and
`PK.root = root`. -/
def digestCell (seed : PublicParameter) (root : Digest) (randomizer : Randomizer)
    (message : Message) (call : DigestCall) : Qrom.HashDomain :=
  cell ⟨0, 0, seed⟩ root (.hmsg randomizer message call) ()

theorem encodeInput_encCell (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    encodeInput (addressedHashInput seed (hashDomainFields (.encoding l τ e))
      (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)) =
      some (encCell seed l τ e message counter) :=
  encodeInput_slotInput ⟨0, 0, seed⟩ 0 (.enc l τ e) (message, counter)

theorem encodeInput_digestCell (seed : PublicParameter) (root : Digest) (randomizer : Randomizer)
    (message : Message) (call : DigestCall) :
    encodeInput (messageDigestInput randomizer seed root message call) =
      some (digestCell seed root randomizer message call) :=
  encodeInput_slotInput ⟨0, 0, seed⟩ root (.hmsg randomizer message call) ()

namespace QTable

variable (v : QTable) (H : Qrom.HashDomain → HashOutput)

/-- The encoding digest of the one-time key `(l, τ, e)` on `message` at `counter`, read from
`H`. -/
def encDigest (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest)
    (counter : EncodingCounter) : Digest :=
  truncateHash (H (encCell v.publicSeed l τ e message counter))

/-- The counter search from `counter`, `attempts` counters: the first codeword's counter and
word. -/
def selectFrom (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    ℕ → ℕ → Option (EncodingCounter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
    match TargetSum.decodeDigest (v.encDigest H l τ e message (BitVec.ofNat counterBits counter))
    with
    | some x => some (BitVec.ofNat counterBits counter, x)
    | none => selectFrom l τ e message attempts (counter + 1)

/-- **The selection** of the one-time key `(l, τ, e)` on `message`: the least counter below
`2^32` whose encoding is a codeword, with the codeword. -/
def select (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    Option (EncodingCounter × Encoding) :=
  v.selectFrom H l τ e message encodingAttemptLimit 0

/-- The one-time signature of `message` by `(l, τ, e)`, with the key's path. -/
def layerSignature (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (message : Digest) :
    Option (LayerSignature l) :=
  (v.select H l τ e message).map fun sel ↦
    ⟨sel.1, fun i ↦ v.chainValue l τ e i (sel.2 i).val, v.authPath l τ e⟩

/-- The signature of layer `l` in a signature of index `idx`. -/
def layerSig (idx : Index) (l : Layer) : Option (LayerSignature l) :=
  v.layerSignature H l (treeOfIndex l idx) (leafOfIndex l idx) (v.layerMessage idx l)

/-- **The honest signature** of a message. -/
def signature (message : Message) : Option Signature :=
  match v.layerSig H (v.index message) 0, v.layerSig H (v.index message) 1,
    v.layerSig H (v.index message) 2 with
  | some bottom, some middle, some top =>
      some ⟨v.randomizer message, v.forsOpening (v.index message) (v.leaves message),
        layerSignatures bottom middle top⟩
  | _, _, _ => none

end QTable

/-! ## The cells and the lazy table -/

/-- The slot of a position's hash call (a digest cell's randomizer read from the table). -/
def posSlot (v : QTable) : RawPos → Slot
  | .prfKey => .expand 1
  | .publicSeed => .expand 0
  | .chainStart l τ e i => .prf (.oneTimeChain l τ e i)
  | .chain l τ e i step => .chain l τ e i step
  | .leaf l τ e => .leaf l τ e
  | .node l τ level index => .node l τ (level.val + 1) index.val
  | .forsSecret idx κ s => .prf (.forsSecret idx κ s)
  | .forsLeaf idx κ s => .forsLeaf idx κ s
  | .forsNode idx κ level node => .forsNode idx κ (level.val + 1) node.val
  | .forsRoots idx => .forsRoots idx
  | .prfMsg message => .prfMsg message
  | .hmsg message => .hmsg (v.randomizer message) message 0

/-- The payload of a position's hash call, from the values. -/
def posPayload (v : QTable) : (p : RawPos) → SlotPayload (posSlot v p)
  | .prfKey => ()
  | .publicSeed => ()
  | .chainStart .. => ()
  | .chain l τ e i step => v.chainValue l τ e i step.val
  | .leaf l τ e => v.endpoints l τ e
  | .node l τ level index =>
      (v.treeValue l τ level.val (2 * index.val), v.treeValue l τ level.val (2 * index.val + 1))
  | .forsSecret .. => ()
  | .forsLeaf idx κ s => v.forsSecret idx κ s
  | .forsNode idx κ level node =>
      (v.forsValue idx κ level.val (2 * node.val), v.forsValue idx κ level.val (2 * node.val + 1))
  | .forsRoots idx => v.forsRoot idx
  | .prfMsg _ => ()
  | .hmsg _ => ()

/-- **The honest input of a position**, given `SK.seed = S0` and the values. -/
def posInput (S0 : MasterSeed) (v : QTable) (p : RawPos) : HashInput :=
  slotInput (v.expandedKey S0) v.root (posSlot v p) (posPayload v p)

/-- **The cell of a position**: the code of its honest input. -/
def cellOf (S0 : MasterSeed) (p : Pos) (v : QTable) : Qrom.HashDomain :=
  cell (v.expandedKey S0) v.root (posSlot v p.1) (posPayload v p.1)

theorem encodeInput_posInput (S0 : MasterSeed) (v : QTable) (p : Pos) :
    encodeInput (posInput S0 v p.1) = some (cellOf S0 p v) :=
  encodeInput_slotInput _ _ _ _

theorem slotInRange_posSlot (v : QTable) (p : Pos) : SlotInRange (posSlot v p.1) := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | node l τ level index =>
    have h1 : level.val < 10 := level.isLt
    have h2 : index.val < 1024 := index.isLt
    exact ⟨by omega, by omega⟩
  | forsNode idx κ level node =>
    have := level.isLt
    exact ⟨by omega, by omega, (hp : node.val < 2 ^ (forsTreeHeight - (level.val + 1)))⟩
  | _ => trivial

theorem posSlot_injective (v : QTable) : Function.Injective (posSlot v) := by
  intro p q h
  cases p <;> cases q <;>
    simp only [posSlot, reduceCtorEq, Slot.prf.injEq, KeygenDomain.oneTimeChain.injEq,
      KeygenDomain.forsSecret.injEq, Slot.chain.injEq, Slot.leaf.injEq, Slot.node.injEq,
      Slot.forsLeaf.injEq, Slot.forsNode.injEq, Slot.forsRoots.injEq, Slot.prfMsg.injEq,
      Slot.hmsg.injEq, Slot.expand.injEq, Nat.add_right_cancel_iff] at h <;>
    first
      | rfl
      | exact absurd h (by decide)
      | simp only [RawPos.chainStart.injEq, RawPos.chain.injEq, RawPos.leaf.injEq,
          RawPos.node.injEq, RawPos.forsSecret.injEq, RawPos.forsLeaf.injEq,
          RawPos.forsNode.injEq, RawPos.forsRoots.injEq, RawPos.prfMsg.injEq,
          RawPos.hmsg.injEq, Fin.ext_iff]
        omega
      | simp only [RawPos.chainStart.injEq, RawPos.chain.injEq, RawPos.leaf.injEq,
          RawPos.node.injEq, RawPos.forsSecret.injEq, RawPos.forsLeaf.injEq,
          RawPos.forsNode.injEq, RawPos.forsRoots.injEq,
          RawPos.hmsg.injEq, Fin.ext_iff]
        tauto

namespace QTable

variable {v v' : QTable}

theorem dig_congr {p : RawPos} (h : ∀ hp : p.InRange, v ⟨p, hp⟩ = v' ⟨p, hp⟩) :
    v.dig p = v'.dig p := by
  unfold dig out
  split_ifs with hp
  · rw [h hp]
  · rfl

theorem out_congr {p : RawPos} (h : ∀ hp : p.InRange, v ⟨p, hp⟩ = v' ⟨p, hp⟩) :
    v.out p = v'.out p := by
  unfold out
  split_ifs with hp
  · rw [h hp]
  · rfl

theorem chainValue_congr {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {i : ChainIndex} {j : ℕ}
    (h : ∀ q : Pos, q.1.rank < 2 + j → v q = v' q) :
    v.chainValue l τ e i j = v'.chainValue l τ e i j := by
  cases j with
  | zero => exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
  | succ j =>
    simp only [chainValue]
    split_ifs with hj
    · exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
    · rfl

theorem treeValue_congr {l : Layer} {τ : TreeIndex} {level index : ℕ}
    (h : ∀ q : Pos, q.1.rank < 2 + chainLength + level → v q = v' q) :
    v.treeValue l τ level index = v'.treeValue l τ level index := by
  cases level with
  | zero => exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
  | succ level =>
    simp only [treeValue]
    split_ifs with hl
    · exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
    · rfl

theorem forsValue_congr {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (h : ∀ q : Pos, q.1.rank < 3 + height → v q = v' q) :
    v.forsValue idx κ height node = v'.forsValue idx κ height node := by
  cases height with
  | zero => exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
  | succ height =>
    simp only [forsValue]
    split_ifs with hh
    · exact dig_congr fun hp ↦ h ⟨_, hp⟩ (by simp [RawPos.rank])
    · rfl

end QTable

theorem cell_congr {key key' : ExpandedKey} {root root' : Digest} {s : Slot} {p : SlotPayload s}
    (h : slotInput key root s p = slotInput key' root' s p) :
    cell key root s p = cell key' root' s p :=
  codeOf_congr h _ _

/-- **A cell reads only the values of lower rank.** -/
theorem cellOf_congr (S0 : MasterSeed) {p : Pos} {v v' : QTable}
    (h : ∀ q : Pos, q.1.rank < p.1.rank → v q = v' q) : cellOf S0 p v = cellOf S0 p v' := by
  have hK : 0 < p.1.rank → v.expandedKey S0 = v'.expandedKey S0 := fun hp ↦ by
    have h1 : v.prfKey = v'.prfKey := QTable.out_congr fun hq ↦ h ⟨_, hq⟩ hp
    have h0 : v.publicSeed = v'.publicSeed := QTable.dig_congr fun hq ↦ h ⟨_, hq⟩ hp
    unfold QTable.expandedKey
    rw [h1, h0]
  have hc := two_le_chainLength
  obtain ⟨p, hp⟩ := p
  cases p with
  | prfKey => exact cell_congr rfl
  | publicSeed => exact cell_congr rfl
  | chainStart l τ e i =>
    change cell _ _ (.prf _) () = cell _ _ (.prf _) ()
    rw [hK (by show 0 < 1; omega)]
    exact cell_congr rfl
  | chain l τ e i step =>
    change cell _ _ (.chain l τ e i step) (v.chainValue l τ e i step.val) =
      cell _ _ (.chain l τ e i step) (v'.chainValue l τ e i step.val)
    rw [hK (by show 0 < 2 + step.val; omega), QTable.chainValue_congr (fun q hq ↦ h q hq)]
    exact cell_congr rfl
  | leaf l τ e =>
    change cell _ _ (.leaf l τ e) (v.endpoints l τ e) = cell _ _ (.leaf l τ e) (v'.endpoints l τ e)
    have he : v.endpoints l τ e = v'.endpoints l τ e := funext fun _ ↦
      QTable.chainValue_congr fun q hq ↦
        h q (lt_of_lt_of_le hq (by show 2 + (chainLength - 1) ≤ 1 + chainLength; omega))
    rw [hK (by show 0 < 1 + chainLength; omega), he]
    exact cell_congr rfl
  | node l τ level index =>
    change cell _ _ (.node l τ (level.val + 1) index.val)
        (v.treeValue l τ level.val _, v.treeValue l τ level.val _) =
      cell _ _ (.node l τ (level.val + 1) index.val)
        (v'.treeValue l τ level.val _, v'.treeValue l τ level.val _)
    rw [hK (by show 0 < 2 + chainLength + level.val; omega), QTable.treeValue_congr h,
      QTable.treeValue_congr h]
    exact cell_congr rfl
  | forsSecret idx κ s =>
    change cell _ _ (.prf _) () = cell _ _ (.prf _) ()
    rw [hK (by show 0 < 1; omega)]
    exact cell_congr rfl
  | forsLeaf idx κ s =>
    change cell _ _ (.forsLeaf idx κ s) (v.forsSecret idx κ s) =
      cell _ _ (.forsLeaf idx κ s) (v'.forsSecret idx κ s)
    rw [hK (by show 0 < 2; omega),
      show v.forsSecret idx κ s = v'.forsSecret idx κ s from
        QTable.dig_congr fun hp ↦ h ⟨_, hp⟩ (by show 1 < 2; omega)]
    exact cell_congr rfl
  | forsNode idx κ level node =>
    change cell _ _ (.forsNode idx κ (level.val + 1) node.val)
        (v.forsValue idx κ level.val _, v.forsValue idx κ level.val _) =
      cell _ _ (.forsNode idx κ (level.val + 1) node.val)
        (v'.forsValue idx κ level.val _, v'.forsValue idx κ level.val _)
    rw [hK (by show 0 < 3 + level.val; omega), QTable.forsValue_congr h,
      QTable.forsValue_congr h]
    exact cell_congr rfl
  | forsRoots idx =>
    change cell _ _ (.forsRoots idx) (v.forsRoot idx) = cell _ _ (.forsRoots idx) (v'.forsRoot idx)
    have hr : v.forsRoot idx = v'.forsRoot idx := funext fun _ ↦ QTable.forsValue_congr h
    rw [hK (by show 0 < 3 + forsTreeHeight; omega), hr]
    exact cell_congr rfl
  | prfMsg message =>
    change cell _ _ (.prfMsg message) () = cell _ _ (.prfMsg message) ()
    rw [hK (by show 0 < 1; omega)]
    exact cell_congr rfl
  | hmsg message =>
    change cell (v.expandedKey S0) v.root (.hmsg (v.randomizer message) message 0) () =
      cell (v'.expandedKey S0) v'.root (.hmsg (v'.randomizer message) message 0) ()
    have hR : v.randomizer message = v'.randomizer message :=
      QTable.dig_congr fun hp ↦
        h ⟨_, hp⟩ (by show 1 < 2 + chainLength + layerHeight topLayer; omega)
    have hroot : v.treeValue topLayer 0 (layerHeight topLayer) 0 =
        v'.treeValue topLayer 0 (layerHeight topLayer) 0 :=
      QTable.treeValue_congr fun q hq ↦ h q hq
    change cell (v.expandedKey S0) (v.treeValue topLayer 0 (layerHeight topLayer) 0)
        (.hmsg (v.randomizer message) message 0) () =
      cell (v'.expandedKey S0) (v'.treeValue topLayer 0 (layerHeight topLayer) 0)
        (.hmsg (v'.randomizer message) message 0) ()
    rw [hK (by show 0 < 2 + chainLength + layerHeight topLayer; omega), hR, hroot]

/-- **The honest table of leanSPHINCS at `SK.seed = S0`**: positions `Pos`, cells `cellOf S0`,
ordered by rank; distinct positions hash distinct inputs by `cell_injective`. -/
def table (S0 : MasterSeed) : LazyTable Pos Qrom.HashDomain (HashOutput × HashOutput) where
  cell := cellOf S0
  pre p q := p.1.rank < q.1.rank
  wf := (measure fun p : Pos ↦ p.1.rank).wf
  dep _ _ _ h := cellOf_congr S0 h
  inj v p q h := Subtype.ext (posSlot_injective v
    (slot_eq_of_cell_eq _ _ (slotInRange_posSlot v p) (slotInRange_posSlot v q) h))

/-- **`F` holds the table's values at their cells.** -/
def Consistent (S0 : MasterSeed) (v : QTable) (F : Qrom.HashDomain → HashOutput × HashOutput) :
    Prop :=
  ∀ p, F (cellOf S0 p v) = v p

theorem consistent_iff {S0 : MasterSeed} {v : QTable}
    {F : Qrom.HashDomain → HashOutput × HashOutput} :
    Consistent S0 v F ↔ (table S0).tab F = v :=
  (table S0).tab_eq_iff.symm

/-- Every function is consistent with its table. -/
theorem consistent_tab (S0 : MasterSeed) (F : Qrom.HashDomain → HashOutput × HashOutput) :
    Consistent S0 ((table S0).tab F) F :=
  consistent_iff.2 rfl

/-- A function overwritten at the cells of `v` by `v` is consistent with `v`. -/
theorem consistent_fill (S0 : MasterSeed) (v : QTable)
    (F : Qrom.HashDomain → HashOutput × HashOutput) : Consistent S0 v ((table S0).fill v v F) :=
  (table S0).fill_cell v v F

/-- **The regrouped law of the honest table.** A program against a uniform random oracle `H`,
observed through a function `f` of `H` that is, at `H = regroup hmsgRoute F`, a function `g` of the
table of `F`, has the law of the average over uniform values `v` of the regrouped program against
runtime 1 with the cells of `v` hardwired to `v`. -/
theorem qromEvalDistMap_eq_tableAvg_regroup (S0 : MasterSeed) {M : Type} [Fintype M]
    [DecidableEq M] (m₀ : M) {β : Type*} [MeasurableSpace β] {W : QReg → Type*} {A : QReg}
    (x : QuantumComp LocalSig.instruments (qromSpec Qrom.HashDomain HashOutput) W A)
    (ρ : SubState A) (f : (Qrom.HashDomain → HashOutput) → (Σ u, W u) → β)
    (g : QTable → (Σ u, W u) → β) (hfg : ∀ F, f (regroup hmsgRoute F) = g ((table S0).tab F)) :
    qromEvalDistMap .instruments x ρ f =
      ∑ v : QTable, (Fintype.card QTable : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime (HashOutput × HashOutput) Qrom.HashDomain ((table S0).hwOf v)
          m₀).evalDistMap .instruments (liftH (regroupCalls hmsgRoute x)).liftOrdinary ρ (g v) := by
  rw [← qromEvalDistMap_regroup hmsgRoute x ρ f,
    show (fun F ↦ f (regroup hmsgRoute F)) = fun F ↦ g ((table S0).tab F) from funext hfg]
  exact qromEvalDistMap_eq_tableAvg (table S0) m₀ .instruments _ ρ g

/-! ## The regrouped hash agrees with the table -/

/-- An input with a call of `H_msg` is an `H_msg` slot's. -/
theorem exists_hmsg_of_hmsgCall {key : ExpandedKey} {root : Digest} {s : Slot}
    (hs : SlotInRange s) {p : SlotPayload s} {call : DigestCall}
    (h : hmsgCall (cell key root s p) = some call) : ∃ R M c, s = .hmsg R M c := by
  rw [hmsgCall_of_encodeInput_eq_some (encodeInput_slotInput key root s p)] at h
  have hl := (hmsgCallOf_eq_some_iff.mp h).1
  have e := slotOf_cell key root hs p
  rw [slotOf_of_encodeInput_eq_some _ (encodeInput_slotInput key root s p), slotOfInput,
    ite_eq_left hl, hmsgSlotOf] at e
  split_ifs at e
  obtain ⟨c, -, hc⟩ := Option.map_eq_some_iff.mp e
  exact ⟨_, _, _, hc.symm⟩

/-- No position's cell is a call 1 of `H_msg`. -/
theorem hmsgCall_cellOf_ne (S0 : MasterSeed) (v : QTable) (p : Pos) :
    hmsgCall (cellOf S0 p v) ≠ some 1 := by
  intro h
  obtain ⟨p, hp⟩ := p
  cases p with
  | hmsg message =>
    change hmsgCall (digestCell v.publicSeed v.root (v.randomizer message) message 0) = some 1 at h
    rw [hmsgCall_of_encodeInput_eq_some (encodeInput_digestCell _ _ _ _ _),
      hmsgCallOf_messageDigestInput] at h
    exact absurd h (by decide)
  | _ =>
    obtain ⟨R, M, c, hs⟩ := exists_hmsg_of_hmsgCall (slotInRange_posSlot v ⟨_, hp⟩) h
    cases hs

/-- **The hash agrees with the table**: every position's input is answered by the first component
of its value, call 1 of a digest by the second component of the digest cell. -/
def Agrees (S0 : MasterSeed) (v : QTable) (H : Qrom.HashDomain → HashOutput) : Prop :=
  (∀ p, H (cellOf S0 p v) = (v p).1) ∧
    ∀ message, H (digestCell v.publicSeed v.root (v.randomizer message) message 1) =
      (v (digPos message)).2

/-- **The regrouped function agrees with its table.** -/
theorem agrees_regroup {S0 : MasterSeed} {v : QTable}
    {F : Qrom.HashDomain → HashOutput × HashOutput} (hF : Consistent S0 v F) :
    Agrees S0 v (regroup hmsgRoute F) := by
  refine ⟨fun p ↦ ?_, fun message ↦ ?_⟩
  · rw [regroup_apply_of_fixed (hmsgRoute_of_ne (hmsgCall_cellOf_ne S0 v p)), hF p]
  · have h₀ := encodeInput_digestCell v.publicSeed v.root (v.randomizer message) message 0
    have h₁ := encodeInput_digestCell v.publicSeed v.root (v.randomizer message) message 1
    rw [regroup_apply_of_second (hmsgRoute_messageDigestInput _ _ _ _ h₀ h₁)]
    exact congrArg Prod.snd (hF (digPos message))

/-! ## The honest computations in any monad -/

section Monadic

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem sequenceFin_pure {β : Type} : ∀ {k : ℕ} (c : Fin k → β),
    sequenceFin (m := m) (fun i ↦ pure (c i)) = pure c
  | 0, c => by
    change (pure Fin.elim0 : m _) = pure c
    exact congrArg pure (funext fun i ↦ i.elim0)
  | k + 1, c => by
    simp only [sequenceFin, pure_bind, sequenceFin_pure]
    exact congrArg pure (funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i)

theorem mapM_eq_pure {α β : Type} {f : α → m β} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = pure (g a)) → l.mapM f = pure (l.map g)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons, h a List.mem_cons_self, pure_bind,
      mapM_eq_pure fun b hb ↦ h b (List.mem_cons_of_mem a hb), pure_bind, List.map_cons]

/-- **Levels built from nodes answering purely**: node `j` of level `z` of the levels over the
nodes at height `height` is the value `T (height + z) j`. -/
theorem merkleLevelsFrom_eq_pure (node : ℕ → ℕ → HashInput → m Digest) (T : ℕ → ℕ → Digest)
    (top : ℕ) (hnode : ∀ h j, h < top → j < 2 ^ (top - (h + 1)) →
      node (h + 1) j (nodePayload (T h (2 * j)) (T h (2 * j + 1))) = pure (T (h + 1) j)) :
    ∀ (remaining height : ℕ) (below : List Digest), height + remaining = top →
      below.length = 2 ^ remaining → (∀ i < below.length, below.getD i 0 = T height i) →
      ∃ levels, merkleLevelsFrom node height below remaining = pure levels ∧
        ∀ z ≤ remaining, ∀ j < 2 ^ (remaining - z), levelNode levels z j = T (height + z) j := by
  intro remaining
  induction remaining with
  | zero =>
    intro height below _ hlen hbelow
    refine ⟨[below], rfl, fun z hz j hj ↦ ?_⟩
    obtain rfl : z = 0 := by omega
    rw [levelNode_cons_zero, Nat.add_zero]
    exact hbelow j (by rw [hlen]; simpa using hj)
  | succ remaining ih =>
    intro height below hH hlen hbelow
    have hhalf : below.length / 2 = 2 ^ remaining := by rw [hlen, pow_succ]; omega
    have hmap : (List.range (below.length / 2)).mapM (fun j ↦ node (height + 1) j
        (nodePayload (below.getD (2 * j) 0) (below.getD (2 * j + 1) 0))) =
        pure ((List.range (below.length / 2)).map (T (height + 1))) := by
      refine mapM_eq_pure fun j hj ↦ ?_
      rw [List.mem_range] at hj
      rw [hbelow _ (by omega), hbelow _ (by omega)]
      exact hnode height j (by omega) (by rw [show top - (height + 1) = remaining by omega]; omega)
    obtain ⟨levels, hl, hz⟩ := ih (height + 1)
      ((List.range (below.length / 2)).map (T (height + 1))) (by omega) (by simp [hhalf])
      (fun i hi ↦ by
      simp only [List.length_map, List.length_range] at hi
      exact getD_map_range _ _ _ _ hi)
    refine ⟨below :: levels, ?_, fun z hz' j hj ↦ ?_⟩
    · rw [merkleLevelsFrom, hmap, pure_bind, hl, pure_bind]
    · cases z with
      | zero =>
        rw [levelNode_cons_zero, Nat.add_zero]
        exact hbelow j (by rw [hlen]; simpa using hj)
      | succ z =>
        rw [levelNode_cons_succ, show height + (z + 1) = height + 1 + z by omega]
        exact hz z (by omega) j (by simpa [Nat.add_sub_add_right] using hj)

/-- **The hash answers the table's positions by their values.** -/
def AnswersTable (S0 : MasterSeed) (v : QTable) (hash : HashInput → m HashOutput) : Prop :=
  ∀ (p : RawPos) (hp : p.InRange), hash (posInput S0 v p) = pure (v ⟨p, hp⟩).1

/-- **The hash answers call 1 of each digest** by the digest cell's second component. -/
def AnswersDigest (v : QTable) (hash : HashInput → m HashOutput) : Prop :=
  ∀ message, hash (messageDigestInput (v.randomizer message) v.publicSeed v.root message 1) =
    pure (v (digPos message)).2

/-- **The hash answers the encoding trials** by `H` at their cells. -/
def AnswersEnc (v : QTable) (H : Qrom.HashDomain → HashOutput)
    (hash : HashInput → m HashOutput) : Prop :=
  ∀ l τ e (message : Digest) (counter : EncodingCounter),
    hash (addressedHashInput v.publicSeed (hashDomainFields (.encoding l τ e))
      (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)) =
      pure (H (encCell v.publicSeed l τ e message counter))

variable {S0 : MasterSeed} {v : QTable} {H : Qrom.HashDomain → HashOutput}
  {hash : HashInput → m HashOutput}

omit [LawfulMonad m] in
theorem hash_posInput (hT : AnswersTable S0 v hash) (p : RawPos) (hp : p.InRange) :
    hash (posInput S0 v p) = pure (v.out p) := by
  rw [v.out_of_inRange hp]
  exact hT p hp

theorem addressedHash_eq_dig (hT : AnswersTable S0 v hash) (p : RawPos) (hp : p.InRange)
    {seed : PublicParameter} {address : Address} {payload : HashInput}
    (h : addressedHashInput seed address payload = posInput S0 v p) :
    LeanSphincsOver.addressedHash hash seed address payload = pure (v.dig p) := by
  rw [LeanSphincsOver.addressedHash, h, hash_posInput hT p hp, pure_bind]
  rfl

theorem expandKey_eq_pure (hT : AnswersTable S0 v hash) :
    LeanSphincsOver.expandKey hash S0 = pure (v.expandedKey S0) := by
  have h1 : hash (keyDerivationInput S0 1) = pure v.prfKey := hash_posInput hT .prfKey trivial
  have h0 : hash (keyDerivationInput S0 0) = pure (v.out .publicSeed) :=
    hash_posInput hT .publicSeed trivial
  rw [LeanSphincsOver.expandKey, h1, pure_bind, h0, pure_bind]
  rfl

theorem otsSecrets_eq_pure (hT : AnswersTable S0 v hash) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) :
    LeanSphincsOver.otsSecrets hash (v.expandedKey S0) l τ e =
      pure fun i ↦ v.chainValue l τ e i 0 := by
  have h : ∀ i, LeanSphincsOver.prf hash (v.expandedKey S0) (.oneTimeChain l τ e i) =
      pure (v.chainValue l τ e i 0) := fun i ↦
    addressedHash_eq_dig hT (.chainStart l τ e i) ⟨hτ, he⟩ rfl
  rw [LeanSphincsOver.otsSecrets]
  simp only [h, sequenceFin_pure]

theorem chainWalk_eq_pure (hT : AnswersTable S0 v hash) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l)
    (i : ChainIndex) : ∀ j, LeanSphincsOver.chainWalk hash (v.expandedKey S0).publicSeed l τ e i 0 j
      (v.chainValue l τ e i 0) = pure (v.chainValue l τ e i j)
  | 0 => rfl
  | j + 1 => by
    have ih := chainWalk_eq_pure hT hτ he i j
    rw [LeanSphincsOver.chainWalk] at ih ⊢
    rw [walkChain, ih, pure_bind]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (show 0 + j < chainLength - 1 by omega),
        show v.chainValue l τ e i (j + 1) = v.dig (.chain l τ e i ⟨j, h⟩) from dite_eq_left h]
      simp only [Nat.zero_add]
      exact addressedHash_eq_dig hT (.chain l τ e i ⟨j, h⟩) ⟨hτ, he⟩ rfl
    · rw [dite_eq_right (show ¬(0 + j < chainLength - 1) by omega),
        show v.chainValue l τ e i (j + 1) = 0 from dite_eq_right h]

theorem otsPublicLeaf_eq_pure (hT : AnswersTable S0 v hash) {l : Layer} {τ : TreeIndex}
    {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l) (he : e.val < 2 ^ layerHeight l) :
    LeanSphincsOver.otsPublicLeaf hash (v.expandedKey S0) l τ e = pure (v.dig (.leaf l τ e)) := by
  rw [LeanSphincsOver.otsPublicLeaf, otsSecrets_eq_pure hT hτ he, pure_bind]
  simp only [chainWalk_eq_pure hT hτ he, sequenceFin_pure, pure_bind]
  exact addressedHash_eq_dig hT (.leaf l τ e) ⟨hτ, he⟩ rfl

/-- The levels of tree `τ` of layer `l` hold the table's tree values. -/
def LevelsOf (v : QTable) (l : Layer) (τ : TreeIndex) (levels : List (List Digest)) : Prop :=
  ∀ z ≤ layerHeight l, ∀ j < 2 ^ (layerHeight l - z), levelNode levels z j = v.treeValue l τ z j

omit [LawfulMonad m] in
theorem levelsOf_fields {l : Layer} {τ : TreeIndex} {levels : List (List Digest)}
    (h : LevelsOf v l τ levels) (e : TreeLeafIndex) (he : e.val < 2 ^ layerHeight l) :
    (fun z : Fin (layerHeight l) ↦ levelNode levels z.val ((e.val >>> z.val) ^^^ 1)) =
      v.authPath l τ e ∧ levelNode levels (layerHeight l) 0 = v.treeRoot l τ :=
  ⟨funext fun z ↦ h z.val z.isLt.le _ (shiftRight_xor_lt he z.isLt), h _ le_rfl 0 (by simp)⟩

theorem treeLevels_eq_pure (hT : AnswersTable S0 v hash) {l : Layer} {τ : TreeIndex}
    (hτ : τ.val < 2 ^ treeBits l) :
    ∃ levels, LeanSphincsOver.treeLevels hash (v.expandedKey S0) l τ = pure levels ∧
      LevelsOf v l τ levels := by
  have hl10 := layerHeight_le l
  have hleaves : (List.range (2 ^ layerHeight l)).mapM (fun leaf ↦
      LeanSphincsOver.otsPublicLeaf hash (v.expandedKey S0) l τ (leafOfNat leaf)) =
      pure ((List.range (2 ^ layerHeight l)).map (v.treeValue l τ 0)) := by
    refine mapM_eq_pure fun j hj ↦ ?_
    rw [List.mem_range] at hj
    have hj' : (leafOfNat j).val < 2 ^ layerHeight l := by
      change j % 2 ^ layerHeight topLayer < _
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hj (two_pow_layerHeight_le l))]
      exact hj
    exact otsPublicLeaf_eq_pure hT hτ hj'
  have hnode : ∀ h j, h < layerHeight l → j < 2 ^ (layerHeight l - (h + 1)) →
      LeanSphincsOver.tweakableHash hash (v.expandedKey S0).publicSeed (.node l τ (h + 1) j)
        (nodePayload (v.treeValue l τ h (2 * j)) (v.treeValue l τ h (2 * j + 1))) =
        pure (v.treeValue l τ (h + 1) j) := by
    intro h j hh hj
    have hh' : h < layerHeight topLayer := by rw [layerHeight_topLayer]; omega
    have hj' : j < 2 ^ layerHeight topLayer :=
      lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by rw [layerHeight_topLayer]; omega))
    rw [show v.treeValue l τ (h + 1) j = v.dig (.node l τ ⟨h, hh'⟩ ⟨j, hj'⟩) from
      dite_eq_left ⟨hh', hj'⟩]
    exact addressedHash_eq_dig hT (.node l τ ⟨h, hh'⟩ ⟨j, hj'⟩) ⟨hτ, hh, hj⟩ rfl
  obtain ⟨levels, hl, hz⟩ := merkleLevelsFrom_eq_pure
    (fun height nodeIndex ↦
      LeanSphincsOver.tweakableHash hash (v.expandedKey S0).publicSeed (.node l τ height nodeIndex))
    (v.treeValue l τ) (layerHeight l) hnode (layerHeight l) 0
    ((List.range (2 ^ layerHeight l)).map (v.treeValue l τ 0)) (by omega) (by simp)
    (fun i hi ↦ by
      simp only [List.length_map, List.length_range] at hi
      exact getD_map_range _ _ _ _ hi)
  refine ⟨levels, ?_, fun z hz' j hj ↦ by simpa using hz z hz' j hj⟩
  rw [LeanSphincsOver.treeLevels, hleaves, pure_bind, merkleLevels]
  exact hl

theorem forsTreeOpen_eq_pure (hT : AnswersTable S0 v hash) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) :
    LeanSphincsOver.forsTreeOpen hash (v.expandedKey S0) idx κ leaf =
      pure (v.forsRoot idx κ, ⟨v.forsSecret idx κ leaf,
        fun z ↦ v.forsValue idx κ z.val ((leaf.val >>> z.val) ^^^ 1)⟩) := by
  have hsec : (List.range (2 ^ forsTreeHeight)).mapM (fun s ↦
      LeanSphincsOver.forsSecret hash (v.expandedKey S0) idx κ (forsLeafOfNat s)) =
      pure ((List.range (2 ^ forsTreeHeight)).map fun s ↦ v.forsSecret idx κ (forsLeafOfNat s)) :=
    mapM_eq_pure fun s _ ↦ addressedHash_eq_dig hT (.forsSecret idx κ (forsLeafOfNat s)) trivial rfl
  have hleaf : (List.range (2 ^ forsTreeHeight)).mapM (fun s ↦
      LeanSphincsOver.forsLeafHash hash (v.expandedKey S0).publicSeed idx κ (forsLeafOfNat s)
        (((List.range (2 ^ forsTreeHeight)).map fun s ↦
          v.forsSecret idx κ (forsLeafOfNat s)).getD s 0)) =
      pure ((List.range (2 ^ forsTreeHeight)).map (v.forsValue idx κ 0)) := by
    refine mapM_eq_pure fun s hs ↦ ?_
    rw [List.mem_range] at hs
    rw [getD_map_range _ _ _ _ hs]
    exact addressedHash_eq_dig hT (.forsLeaf idx κ (forsLeafOfNat s)) trivial rfl
  have hnode : ∀ h j, h < forsTreeHeight → j < 2 ^ (forsTreeHeight - (h + 1)) →
      LeanSphincsOver.tweakableHash hash (v.expandedKey S0).publicSeed
        (.forsNode idx κ (h + 1) j)
        (nodePayload (v.forsValue idx κ h (2 * j)) (v.forsValue idx κ h (2 * j + 1))) =
        pure (v.forsValue idx κ (h + 1) j) := by
    intro h j hh hj
    have hj' : j < 2 ^ forsTreeHeight :=
      lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show v.forsValue idx κ (h + 1) j = v.dig (.forsNode idx κ ⟨h, hh⟩ ⟨j, hj'⟩) from
      dite_eq_left ⟨hh, hj'⟩]
    exact addressedHash_eq_dig hT (.forsNode idx κ ⟨h, hh⟩ ⟨j, hj'⟩) hj rfl
  obtain ⟨levels, hl, hz⟩ := merkleLevelsFrom_eq_pure
    (fun height node ↦ LeanSphincsOver.tweakableHash hash (v.expandedKey S0).publicSeed
      (.forsNode idx κ height node))
    (v.forsValue idx κ) forsTreeHeight hnode forsTreeHeight 0
    ((List.range (2 ^ forsTreeHeight)).map (v.forsValue idx κ 0)) (by omega) (by simp)
    (fun i hi ↦ by
      simp only [List.length_map, List.length_range] at hi
      exact getD_map_range _ _ _ _ hi)
  rw [LeanSphincsOver.forsTreeOpen, hsec, pure_bind, hleaf, pure_bind, merkleLevels, hl, pure_bind,
    getD_map_range _ _ _ _ leaf.isLt, forsLeafOfNat_val]
  have hr := hz forsTreeHeight le_rfl 0 (by simp)
  rw [Nat.zero_add] at hr
  rw [hr]
  refine congrArg (fun f ↦ (pure (v.forsRoot idx κ,
    (⟨v.forsSecret idx κ leaf, f⟩ : ForsTreeOpening)) : m _)) (funext fun z ↦ ?_)
  have h := hz z.val z.isLt.le _ (shiftRight_xor_lt leaf.isLt z.isLt)
  rwa [Nat.zero_add] at h

theorem forsOpen_eq_pure (hT : AnswersTable S0 v hash) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    LeanSphincsOver.forsOpen hash (v.expandedKey S0) idx lv =
      pure (v.forsKey idx, v.forsOpening idx lv) := by
  have hk : LeanSphincsOver.forsPublicKey hash (v.expandedKey S0).publicSeed idx
      (fun κ ↦ v.forsRoot idx κ) = pure (v.forsKey idx) :=
    addressedHash_eq_dig hT (.forsRoots idx) trivial rfl
  simp only [LeanSphincsOver.forsOpen, forsTreeOpen_eq_pure hT, sequenceFin_pure, pure_bind, hk]
  rfl

theorem encode_eq_pure (hE : AnswersEnc v H hash) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    LeanSphincsOver.encode hash (v.expandedKey S0).publicSeed l τ e message counter =
      pure (TargetSum.decodeDigest (v.encDigest H l τ e message counter)) := by
  simp only [LeanSphincsOver.encode, LeanSphincsOver.tweakableHash, LeanSphincsOver.addressedHash,
    QTable.expandedKey_publicSeed, hE l τ e message counter, pure_bind]
  rfl

theorem otsSignFrom_eq_pure (hT : AnswersTable S0 v hash) (hE : AnswersEnc v H hash)
    {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} (hτ : τ.val < 2 ^ treeBits l)
    (he : e.val < 2 ^ layerHeight l) (message : Digest) : ∀ attempts counter,
      LeanSphincsOver.otsSignFrom hash (v.expandedKey S0) l τ e message attempts counter =
        pure ((v.selectFrom H l τ e message attempts counter).map fun sel ↦
          (sel.1, fun i ↦ v.chainValue l τ e i (sel.2 i).val))
  | 0, _ => rfl
  | attempts + 1, counter => by
    rw [LeanSphincsOver.otsSignFrom, encode_eq_pure hE, pure_bind, QTable.selectFrom]
    cases TargetSum.decodeDigest (v.encDigest H l τ e message (BitVec.ofNat counterBits counter))
      with
    | none => exact otsSignFrom_eq_pure hT hE hτ he message attempts (counter + 1)
    | some x =>
      simp only [otsSecrets_eq_pure hT hτ he, pure_bind, chainWalk_eq_pure hT hτ he,
        sequenceFin_pure, Option.map_some]

theorem signLayer_eq_pure (hT : AnswersTable S0 v hash) (hE : AnswersEnc v H hash)
    {top : List (List Digest)} (htop : LevelsOf v topLayer 0 top) (idx : Index) (layer : Layer)
    (message : Digest) :
    LeanSphincsOver.signLayer hash (v.expandedKey S0) top idx layer message =
      pure ((v.layerSignature H layer (treeOfIndex layer idx) (leafOfIndex layer idx)
        message).map fun sig ↦ (sig, v.treeRoot layer (treeOfIndex layer idx))) := by
  have hτ := treeOfIndex_lt layer idx
  have he := leafOfIndex_lt layer idx
  rw [LeanSphincsOver.signLayer, LeanSphincsOver.otsSign, otsSignFrom_eq_pure hT hE hτ he,
    pure_bind, QTable.layerSignature, QTable.select]
  cases v.selectFrom H layer (treeOfIndex layer idx) (leafOfIndex layer idx) message
      encodingAttemptLimit 0 with
  | none => rfl
  | some sel =>
    simp only [Option.map_some]
    by_cases h : layer = topLayer
    · subst h
      obtain ⟨hpath, hroot⟩ := levelsOf_fields htop (leafOfIndex topLayer idx) he
      rw [ite_eq_left rfl, pure_bind, treeOfIndex_topLayer, hpath, hroot]
    · obtain ⟨levels, hl, hlev⟩ := treeLevels_eq_pure (S0 := S0) (hash := hash) hT hτ
      obtain ⟨hpath, hroot⟩ := levelsOf_fields hlev (leafOfIndex layer idx) he
      rw [ite_eq_right h, hl, pure_bind, hpath, hroot]

theorem keygenInternal_eq_pure (hT : AnswersTable S0 v hash) :
    ∃ top, LeanSphincsOver.keygenInternal hash (v.expandedKey S0) = pure (v.publicKey, top) ∧
      LevelsOf v topLayer 0 top := by
  obtain ⟨top, hl, hlev⟩ := treeLevels_eq_pure hT (l := topLayer) (τ := 0) (by simp)
  refine ⟨top, ?_, hlev⟩
  rw [LeanSphincsOver.keygenInternal, hl, pure_bind,
    (levelsOf_fields hlev 0 (Nat.two_pow_pos _)).2]
  rfl

/-- **Key generation returns the table's keys.** -/
theorem keygenFromSeed_eq_pure (hT : AnswersTable S0 v hash) :
    LeanSphincsOver.keygenFromSeed hash S0 = pure (v.publicKey, S0) := by
  obtain ⟨top, htop, -⟩ := keygenInternal_eq_pure hT
  rw [LeanSphincsOver.keygenFromSeed, expandKey_eq_pure hT, pure_bind, htop, pure_bind]

theorem prfMessage_eq_randomizer (hT : AnswersTable S0 v hash) (message : Message) :
    LeanSphincsOver.prfMessage hash (v.expandedKey S0).secretPrfKey
      (v.expandedKey S0).publicSeed message = pure (v.randomizer message) := by
  have h : hash (prfMessageInput (v.expandedKey S0).secretPrfKey (v.expandedKey S0).publicSeed
      message) = pure (v.out (.prfMsg message)) := hash_posInput hT (.prfMsg message) trivial
  refine (prfMessage_eq hash _ _ message).trans ?_
  rw [h, pure_bind]
  rfl

theorem messageDigest_eq_pure (hT : AnswersTable S0 v hash) (hD : AnswersDigest v hash)
    (message : Message) :
    LeanSphincsOver.messageDigest hash v.publicKey (v.randomizer message) message =
      pure (v.messageDigest message) := by
  have hcall : ∀ c : DigestCall, c = 0 ∨ c = 1 := by decide
  have hc : ∀ c, LeanSphincsOver.messageDigestCall hash (v.randomizer message)
      v.publicKey.publicSeed v.publicKey.root message c = pure (v.digestOutput message c) := by
    intro c
    rw [messageDigestCall_eq]
    rcases hcall c with rfl | rfl
    · rw [QTable.digestOutput_zero]
      exact hT (.hmsg message) trivial
    · rw [QTable.digestOutput_one]
      exact hD message
  rw [LeanSphincsOver.messageDigest]
  simp only [hc, sequenceFin_pure, pure_bind]
  rfl

/-- **Signing returns the table's signature.** -/
theorem sign_eq_pure (hT : AnswersTable S0 v hash) (hD : AnswersDigest v hash)
    (hE : AnswersEnc v H hash) (message : Message) :
    LeanSphincsOver.sign hash S0 message = pure (v.signature H message) := by
  obtain ⟨top, htop, hlev⟩ := keygenInternal_eq_pure hT
  have hI : digestIndex (v.messageDigest message) = v.index message := rfl
  have hV : digestForsLeaves (v.messageDigest message) = v.leaves message := rfl
  rw [LeanSphincsOver.sign, expandKey_eq_pure hT, pure_bind, LeanSphincsOver.signWithExpandedKey,
    htop, pure_bind]
  simp only [prfMessage_eq_randomizer hT, messageDigest_eq_pure hT hD, pure_bind, hI, hV,
    forsOpen_eq_pure hT, signLayer_eq_pure hT hE hlev]
  simp only [QTable.signature, QTable.layerSig, QTable.layerMessage_zero,
    QTable.layerMessage_one, QTable.layerMessage_two]
  cases v.layerSignature H 0 (treeOfIndex 0 (v.index message)) (leafOfIndex 0 (v.index message))
      (v.forsKey (v.index message)) with
  | none => rfl
  | some bottom =>
    simp only [Option.map_some]
    cases v.layerSignature H 1 (treeOfIndex 1 (v.index message))
        (leafOfIndex 1 (v.index message)) (v.treeRoot 0 (treeOfIndex 0 (v.index message))) with
    | none => rfl
    | some middle =>
      simp only [Option.map_some]
      cases v.layerSignature H 2 (treeOfIndex 2 (v.index message))
          (leafOfIndex 2 (v.index message)) (v.treeRoot 1 (treeOfIndex 1 (v.index message))) with
      | none => rfl
      | some top => rfl

end Monadic

/-! ## The honest computations as cell reads -/

/-- The cells of the table. -/
def TableCell (S0 : MasterSeed) (v : QTable) (x : Qrom.HashDomain) : Prop :=
  ∃ p, cellOf S0 p v = x

/-- **The cells the signer reads**: the table's, call 1 of each digest, the encoding trials. -/
def SignCell (S0 : MasterSeed) (v : QTable) (x : Qrom.HashDomain) : Prop :=
  TableCell S0 v x ∨
    (∃ message, digestCell v.publicSeed v.root (v.randomizer message) message 1 = x) ∨
    ∃ l τ e message counter, encCell v.publicSeed l τ e message counter = x

/-- The hash through an implementation of the model's oracles. -/
def hashBy {n : Type → Type} [Monad n] (impl : QueryImpl RomOracles n) (input : HashInput) :
    n HashOutput :=
  simulateQ impl (hashQ input)

section Impl

variable {n : Type → Type} [Monad n] [LawfulMonad n] (impl : QueryImpl RomOracles n)

theorem simulateQ_addressedHash (seed : PublicParameter) (address : Address)
    (payload : HashInput) :
    simulateQ impl (LeanSphincsOver.addressedHash hashQ seed address payload) =
      LeanSphincsOver.addressedHash (hashBy impl) seed address payload := by
  simp only [LeanSphincsOver.addressedHash, simulateQ_bind, simulateQ_pure]
  rfl

theorem simulateQ_chainWalk (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) (start steps : ℕ) (value : Digest) :
    simulateQ impl (LeanSphincsOver.chainWalk hashQ seed l τ e i start steps value) =
      LeanSphincsOver.chainWalk (hashBy impl) seed l τ e i start steps value := by
  simp only [LeanSphincsOver.chainWalk, Quantum.Sphincs.WithHash.simulateQ_walkChain,
    simulateQ_addressedHash]

theorem simulateQ_encode (seed : PublicParameter) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    simulateQ impl (LeanSphincsOver.encode hashQ seed l τ e message counter) =
      LeanSphincsOver.encode (hashBy impl) seed l τ e message counter := by
  simp only [LeanSphincsOver.encode, simulateQ_bind, simulateQ_pure, simulateQ_addressedHash]

theorem simulateQ_prf (key : ExpandedKey) (domain : KeygenDomain) :
    simulateQ impl (LeanSphincsOver.prf hashQ key domain) =
      LeanSphincsOver.prf (hashBy impl) key domain :=
  simulateQ_addressedHash impl _ _ _

theorem simulateQ_otsSecrets (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) :
    simulateQ impl (LeanSphincsOver.otsSecrets hashQ key l τ e) =
      LeanSphincsOver.otsSecrets (hashBy impl) key l τ e := by
  simp only [LeanSphincsOver.otsSecrets, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
    simulateQ_prf]

theorem simulateQ_otsPublicLeaf (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) :
    simulateQ impl (LeanSphincsOver.otsPublicLeaf hashQ key l τ e) =
      LeanSphincsOver.otsPublicLeaf (hashBy impl) key l τ e := by
  simp only [LeanSphincsOver.otsPublicLeaf, simulateQ_bind, simulateQ_otsSecrets,
    Quantum.Sphincs.WithHash.simulateQ_sequenceFin, simulateQ_chainWalk,
    LeanSphincsOver.leafHash, simulateQ_addressedHash]

theorem simulateQ_otsSignFrom (key : ExpandedKey) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (message : Digest) : ∀ attempts counter : ℕ,
      simulateQ impl (LeanSphincsOver.otsSignFrom hashQ key l τ e message attempts counter) =
        LeanSphincsOver.otsSignFrom (hashBy impl) key l τ e message attempts counter
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
    simulateQ impl (LeanSphincsOver.treeLevels hashQ key l τ) =
      LeanSphincsOver.treeLevels (hashBy impl) key l τ := by
  simp only [LeanSphincsOver.treeLevels, merkleLevels, simulateQ_bind,
    Quantum.Sphincs.WithHash.simulateQ_mapM, simulateQ_otsPublicLeaf,
    Quantum.Sphincs.WithHash.simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_forsOpen (key : ExpandedKey) (idx : Index)
    (lv : ForsTreeIndex → ForsLeafIndex) :
    simulateQ impl (LeanSphincsOver.forsOpen hashQ key idx lv) =
      LeanSphincsOver.forsOpen (hashBy impl) key idx lv := by
  simp only [LeanSphincsOver.forsOpen, LeanSphincsOver.forsTreeOpen, LeanSphincsOver.forsSecret,
    LeanSphincsOver.forsLeafHash, LeanSphincsOver.forsPublicKey, merkleLevels, simulateQ_bind,
    simulateQ_pure, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
    Quantum.Sphincs.WithHash.simulateQ_mapM, simulateQ_prf,
    Quantum.Sphincs.WithHash.simulateQ_merkleLevelsFrom, simulateQ_addressedHash]

theorem simulateQ_expandKey (secretSeed : SecretKey) :
    simulateQ impl (LeanSphincsOver.expandKey hashQ secretSeed) =
      LeanSphincsOver.expandKey (hashBy impl) secretSeed := by
  simp only [LeanSphincsOver.expandKey, simulateQ_bind, simulateQ_pure]
  rfl

theorem simulateQ_keygenInternal (key : ExpandedKey) :
    simulateQ impl (LeanSphincsOver.keygenInternal hashQ key) =
      LeanSphincsOver.keygenInternal (hashBy impl) key := by
  simp only [LeanSphincsOver.keygenInternal, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

theorem simulateQ_keygenFromSeed (secretSeed : SecretKey) :
    simulateQ impl (LeanSphincsOver.keygenFromSeed hashQ secretSeed) =
      LeanSphincsOver.keygenFromSeed (hashBy impl) secretSeed := by
  simp only [LeanSphincsOver.keygenFromSeed, simulateQ_bind, simulateQ_expandKey,
    simulateQ_keygenInternal]
  refine bind_congr fun key ↦ bind_congr fun x ↦ ?_
  rfl

theorem simulateQ_signLayer (key : ExpandedKey) (top : List (List Digest)) (idx : Index)
    (layer : Layer) (message : Digest) :
    simulateQ impl (LeanSphincsOver.signLayer hashQ key top idx layer message) =
      LeanSphincsOver.signLayer (hashBy impl) key top idx layer message := by
  simp only [LeanSphincsOver.signLayer, LeanSphincsOver.otsSign, simulateQ_bind,
    simulateQ_otsSignFrom]
  refine bind_congr fun x ↦ ?_
  rcases x with _ | ⟨counter, values⟩
  · rfl
  · by_cases h : layer = topLayer
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure]
    · simp only [h, ↓reduceIte, simulateQ_bind, simulateQ_pure, simulateQ_treeLevels]

theorem simulateQ_sign (secretKey : SecretKey) (message : Message) :
    simulateQ impl (LeanSphincsOver.sign hashQ secretKey message) =
      LeanSphincsOver.sign (hashBy impl) secretKey message := by
  simp only [LeanSphincsOver.sign, LeanSphincsOver.signWithExpandedKey,
    LeanSphincsOver.prfMessage, LeanSphincsOver.messageDigest,
    LeanSphincsOver.messageDigestCall, simulateQ_bind, simulateQ_pure, simulateQ_expandKey,
    simulateQ_keygenInternal, Quantum.Sphincs.WithHash.simulateQ_sequenceFin,
    simulateQ_forsOpen, simulateQ_signLayer]
  refine bind_congr fun key ↦ bind_congr fun x ↦ ?_
  rcases x with ⟨publicKey, top⟩
  refine bind_congr fun y ↦ bind_congr fun outputs ↦ bind_congr fun f ↦ ?_
  rcases f with ⟨forsKey, forsOpening⟩
  refine bind_congr fun b ↦ ?_
  rcases b with _ | ⟨bottom, bottomRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun c ↦ ?_
  rcases c with _ | ⟨middle, middleRoot⟩
  · rfl
  simp only [simulateQ_bind, simulateQ_signLayer]
  refine bind_congr fun d ↦ ?_
  rcases d with _ | ⟨topSignature, _⟩ <;> rfl

variable {S0 : MasterSeed} {v : QTable} {H : Qrom.HashDomain → HashOutput}

theorem hashBy_of_encodeInput_eq_some {input : HashInput} {x : Qrom.HashDomain}
    (h : encodeInput input = some x) : hashBy impl input = impl (.inr x) := by
  rw [hashBy, hashQ_of_encodeInput_eq_some h, simulateQ_spec_query]

theorem answersTable_hashBy (hv : Agrees S0 v H)
    (himpl : ∀ x, TableCell S0 v x → impl (.inr x) = pure (H x)) :
    AnswersTable S0 v (hashBy impl) := fun p hp ↦ by
  rw [hashBy_of_encodeInput_eq_some impl (encodeInput_posInput S0 v ⟨p, hp⟩),
    himpl _ ⟨_, rfl⟩, hv.1]

theorem answersDigest_hashBy (hv : Agrees S0 v H)
    (himpl : ∀ x, SignCell S0 v x → impl (.inr x) = pure (H x)) :
    AnswersDigest v (hashBy impl) := fun message ↦ by
  rw [hashBy_of_encodeInput_eq_some impl (encodeInput_digestCell _ _ _ _ _),
    himpl _ (Or.inr (Or.inl ⟨_, rfl⟩)), hv.2]

theorem answersEnc_hashBy (himpl : ∀ x, SignCell S0 v x → impl (.inr x) = pure (H x)) :
    AnswersEnc v H (hashBy impl) := fun l τ e message counter ↦ by
  rw [hashBy_of_encodeInput_eq_some impl (encodeInput_encCell _ _ _ _ _ _),
    himpl _ (Or.inr (Or.inr ⟨_, _, _, _, _, rfl⟩))]

/-- **Key generation in the random-oracle model returns the table's keys**, under any
implementation answering `H` purely at the table's cells. -/
theorem simulateQ_generateKeys_eq (hv : Agrees S0 v H)
    (himpl : ∀ x, TableCell S0 v x → impl (.inr x) = pure (H x)) :
    simulateQ impl (sphincsRom.generateKeys S0) = pure (v.publicKey, S0) := by
  change simulateQ impl (LeanSphincsOver.keygenFromSeed hashQ S0) = _
  rw [simulateQ_keygenFromSeed]
  exact keygenFromSeed_eq_pure (answersTable_hashBy impl hv himpl)

/-- **Signing in the random-oracle model returns the table's signature**, under any
implementation answering `H` purely at the cells the signer reads. -/
theorem simulateQ_sign_eq (hv : Agrees S0 v H)
    (himpl : ∀ x, SignCell S0 v x → impl (.inr x) = pure (H x)) (message : Message) :
    simulateQ impl (sphincsRom.sign S0 message) = pure (v.signature H message) := by
  change simulateQ impl (LeanSphincsOver.sign hashQ S0 message) = _
  rw [simulateQ_sign]
  exact sign_eq_pure (answersTable_hashBy impl hv fun x hx ↦ himpl x (Or.inl hx))
    (answersDigest_hashBy impl hv himpl) (answersEnc_hashBy impl himpl) message

end Impl

/-- A query of the model hashes a point satisfying `P`. -/
def RomRead (P : Qrom.HashDomain → Prop) : RomOracles.Domain → Prop
  | .inl _ => False
  | .inr x => P x

theorem not_romRead_inl (P : Qrom.HashDomain → Prop) (n : ℕ) : ¬RomRead P (.inl n) :=
  id

/-- The model's oracles answered by `H` at the points satisfying `P`, failing elsewhere. -/
noncomputable def guardAnswers (H : Qrom.HashDomain → HashOutput) (P : Qrom.HashDomain → Prop) :
    QueryImpl RomOracles Option
  | .inl _ => none
  | .inr x => @ite _ (P x) (Classical.propDecidable _) (some (H x)) none

/-- **A computation that never fails under the guarded answers** returns its evaluation with `H`
and queries only points satisfying `P`. -/
theorem eval_queriesSatisfy_of_guard {H : Qrom.HashDomain → HashOutput}
    {P : Qrom.HashDomain → Prop} {α : Type} {x : OracleComp RomOracles α} {a : α}
    (h : simulateQ (guardAnswers H P) x = some a) :
    evalWithAnswerFn (romAnswers H) x = a ∧ QueriesSatisfy (romAnswers H) (RomRead P) x := by
  induction x using OracleComp.inductionOn with
  | pure b =>
    rw [simulateQ_pure] at h
    exact ⟨Option.some.inj h, queriesSatisfy_pure _⟩
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    cases hg : guardAnswers H P t with
    | none =>
      rw [hg] at h
      exact absurd h (by simp)
    | some u =>
      rw [hg] at h
      have hk : simulateQ (guardAnswers H P) (k u) = some a := h
      have ht : RomRead P t ∧ u = romAnswers H t := by
        rcases t with n | y
        · simp [guardAnswers] at hg
        · simp only [guardAnswers] at hg
          split_ifs at hg with hy
          cases hg
          exact ⟨hy, rfl⟩
      obtain ⟨he, hq⟩ := ih u hk
      rw [ht.2] at he hq
      refine ⟨by rw [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query]; exact he, ?_⟩
      intro q hq'
      rw [queries, trace_query_bind, List.mem_append, List.mem_singleton] at hq'
      rcases hq' with rfl | hq'
      · exact ht.1
      · exact hq q hq'

theorem simulateQ_guardAnswers_eq {H : Qrom.HashDomain → HashOutput} {P : Qrom.HashDomain → Prop}
    {x : Qrom.HashDomain} (hx : P x) : guardAnswers H P (.inr x) = pure (H x) := by
  simp only [guardAnswers]
  exact ite_eq_left hx

variable {S0 : MasterSeed} {v : QTable} {H : Qrom.HashDomain → HashOutput}

/-- **Key generation returns the table's keys.** -/
theorem eval_generateKeys (hv : Agrees S0 v H) :
    evalWithAnswerFn (romAnswers H) (sphincsRom.generateKeys S0) = (v.publicKey, S0) := by
  have h := simulateQ_generateKeys_eq (romAnswers H) hv fun _ _ ↦ rfl
  unfold evalWithAnswerFn
  exact h

/-- **Signing returns the table's signature.** -/
theorem eval_sign (hv : Agrees S0 v H) (message : Message) :
    evalWithAnswerFn (romAnswers H) (sphincsRom.sign S0 message) = v.signature H message := by
  have h := simulateQ_sign_eq (romAnswers H) hv (fun _ _ ↦ rfl) message
  unfold evalWithAnswerFn
  exact h

/-- **Key generation hashes cells of the table only.** -/
theorem cellReads_generateKeys (hv : Agrees S0 v H) :
    QueriesSatisfy (romAnswers H) (RomRead (TableCell S0 v)) (sphincsRom.generateKeys S0) :=
  (eval_queriesSatisfy_of_guard (simulateQ_generateKeys_eq (guardAnswers H (TableCell S0 v)) hv
    fun _ hx ↦ simulateQ_guardAnswers_eq hx)).2

/-- **The signer hashes the table's cells, call 1 of the digests and encoding trials only.** -/
theorem signReads_sign (hv : Agrees S0 v H) (message : Message) :
    QueriesSatisfy (romAnswers H) (RomRead (SignCell S0 v)) (sphincsRom.sign S0 message) :=
  (eval_queriesSatisfy_of_guard (simulateQ_sign_eq (guardAnswers H (SignCell S0 v)) hv
    (fun _ hx ↦ simulateQ_guardAnswers_eq hx) message)).2

theorem fst_honestEval {α : Type} (x : OracleComp RomOracles α) :
    (honestEval H x).1 = evalWithAnswerFn (romAnswers H) x :=
  rfl

theorem fst_honestEval_generateKeys (hv : Agrees S0 v H) :
    (honestEval H (sphincsRom.generateKeys S0)).1 = (v.publicKey, S0) := by
  rw [fst_honestEval]
  exact eval_generateKeys hv

theorem fst_honestEval_sign (hv : Agrees S0 v H) (message : Message) :
    (honestEval H (sphincsRom.sign S0 message)).1 = v.signature H message := by
  rw [fst_honestEval]
  exact eval_sign hv message

/-! ## Values at the symbolic positions and disclosures -/

namespace QTable

variable (v : QTable) (H : Qrom.HashDomain → HashOutput)

/-- **The honest value at a symbolic position** (`Quantum.Sphincs.ValPos`). -/
def valuePos : ValPos → Digest
  | .chain l τ e i j => v.chainValue l τ e i j.val
  | .tree l τ level index => v.treeValue l τ level.val index.val
  | .forsSecret idx κ s => v.forsSecret idx κ s
  | .forsTree idx κ height node => v.forsValue idx κ height.val node.val
  | .forsKey idx => v.forsKey idx

theorem valuePos_cpos (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) {j : ℕ}
    (hj : j < chainLength) : v.valuePos (cpos l τ e i j) = v.chainValue l τ e i j := by
  change v.chainValue l τ e i (j % chainLength) = _
  rw [Nat.mod_eq_of_lt hj]

theorem valuePos_tpos (l : Layer) (τ : TreeIndex) {level index : ℕ}
    (hl : level ≤ layerHeight topLayer) (hi : index < 2 ^ layerHeight topLayer) :
    v.valuePos (tpos l τ level index) = v.treeValue l τ level index := by
  change v.treeValue l τ (level % (layerHeight topLayer + 1)) (index % 2 ^ layerHeight topLayer) =
    _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hl), Nat.mod_eq_of_lt hi]

theorem valuePos_fpos (idx : Index) (κ : ForsTreeIndex) {height node : ℕ}
    (hh : height ≤ forsTreeHeight) (hn : node < 2 ^ forsTreeHeight) :
    v.valuePos (fpos idx κ height node) = v.forsValue idx κ height node := by
  change v.forsValue idx κ (height % (forsTreeHeight + 1)) (node % 2 ^ forsTreeHeight) = _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hh), Nat.mod_eq_of_lt hn]

theorem valuePos_rootPos : v.valuePos rootPos = v.root :=
  v.valuePos_tpos topLayer 0 (level := layerHeight topLayer) (index := 0) le_rfl
    (Nat.two_pow_pos _)

/-- **Each key signs one fixed value**: in every signature of index `idx`, the key `K_l(idx)`
signs the value at `msgPos (keyOf l idx)`, whatever the message. -/
theorem msgPos_eq (l : Layer) (idx : Index) :
    v.valuePos (msgPos (keyOf l idx)) = v.layerMessage idx l := by
  have hi : idx.val < 67108864 := idx.isLt
  fin_cases l
  · change v.forsKey (indexBelow 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx)) = v.forsKey idx
    refine congrArg v.forsKey (Fin.ext ?_)
    change ((treeOfIndex 0 idx).val * 2 ^ 8 + (leafOfIndex 0 idx).val) % 2 ^ 26 = idx.val
    rw [treeOfIndex_zero, leafOfIndex_zero]
    change (idx.val / 256 * 256 + idx.val % 256) % 67108864 = idx.val
    omega
  · change v.valuePos (tpos 0 (indexBelow 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx)) 8 0) =
      v.treeValue 0 (treeOfIndex 0 idx) 8 0
    rw [v.valuePos_tpos 0 _ (level := 8) (index := 0) (by decide) (Nat.two_pow_pos _)]
    refine congrArg (fun τ ↦ v.treeValue 0 τ 8 0) (Fin.ext ?_)
    change (idx.val / 65536 * 256 + idx.val / 256 % 256) % 67108864 = idx.val / 256
    omega
  · change v.valuePos (tpos 1 (indexBelow 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx)) 8 0) =
      v.treeValue 1 (treeOfIndex 1 idx) 8 0
    rw [v.valuePos_tpos 1 _ (level := 8) (index := 0) (by decide) (Nat.two_pow_pos _)]
    refine congrArg (fun τ ↦ v.treeValue 1 τ 8 0) (Fin.ext ?_)
    change (idx.val / 67108864 * 1024 + idx.val / 65536 % 1024) % 67108864 = idx.val / 65536
    omega

/-- **The counter search of `K_l(idx)` runs on the value at `msgPos`**, in every signature of
index `idx`. -/
theorem layerSig_eq (idx : Index) (l : Layer) :
    v.layerSig H idx l = v.layerSignature H l (treeOfIndex l idx) (leafOfIndex l idx)
      (v.valuePos (msgPos (keyOf l idx))) := by
  rw [msgPos_eq]
  rfl

/-- The selection of `K_l(idx)` on the value it signs. -/
def layerSelect (idx : Index) (l : Layer) : Option (EncodingCounter × Encoding) :=
  v.select H l (treeOfIndex l idx) (leafOfIndex l idx) (v.layerMessage idx l)

/-- **The positions the signature of `M` discloses**: the FORS secrets at the digest's leaves and
their paths, and each layer's opened chain positions and path, when the signer returns a
signature; none otherwise. -/
def disclosedBy (message : Message) : Set ValPos :=
  match v.layerSelect H (v.index message) 0, v.layerSelect H (v.index message) 1,
    v.layerSelect H (v.index message) 2 with
  | some s0, some s1, some s2 =>
      forsDisclosed (v.index message) (v.leaves message) ∪
        layerDisclosed 0 (treeOfIndex 0 (v.index message)) (leafOfIndex 0 (v.index message)) s0.2 ∪
        layerDisclosed 1 (treeOfIndex 1 (v.index message)) (leafOfIndex 1 (v.index message)) s1.2 ∪
        layerDisclosed 2 (treeOfIndex 2 (v.index message)) (leafOfIndex 2 (v.index message)) s2.2
  | _, _, _ => ∅

/-- The positions disclosed after the messages `msgs`: the public key's root and each message's
signature. -/
def disclosures (msgs : List Message) : Set ValPos :=
  {rootPos} ∪ ⋃ message ∈ msgs, v.disclosedBy H message

theorem disclosures_mono {msgs msgs' : List Message} (h : msgs ⊆ msgs') :
    v.disclosures H msgs ⊆ v.disclosures H msgs' :=
  Set.union_subset_union_right _ (Set.biUnion_subset_biUnion_left fun _ hr ↦ h hr)

theorem layerSelect_eq (idx : Index) (l : Layer) :
    v.layerSelect H idx l = v.select H l (treeOfIndex l idx) (leafOfIndex l idx)
      (v.valuePos (msgPos (keyOf l idx))) := by
  rw [msgPos_eq]
  rfl

/-- A signature is returned exactly when the message discloses positions. -/
theorem signature_isSome_iff (message : Message) :
    (v.signature H message).isSome ↔ v.disclosedBy H message ≠ ∅ := by
  simp only [signature, disclosedBy, layerSig, layerSelect, layerSignature]
  cases v.select H 0 (treeOfIndex 0 (v.index message)) (leafOfIndex 0 (v.index message))
      (v.layerMessage (v.index message) 0) with
  | none => simp
  | some s0 =>
    cases v.select H 1 (treeOfIndex 1 (v.index message)) (leafOfIndex 1 (v.index message))
        (v.layerMessage (v.index message) 1) with
    | none => simp
    | some s1 =>
      cases v.select H 2 (treeOfIndex 2 (v.index message)) (leafOfIndex 2 (v.index message))
          (v.layerMessage (v.index message) 2) with
      | none => simp
      | some s2 =>
        simp only [Option.map_some, Option.isSome_some, ne_eq, true_iff]
        exact Set.Nonempty.ne_empty ⟨_, Or.inl (Or.inl (Or.inl ⟨⟨0, by decide⟩, Or.inl rfl⟩))⟩

/-- A layer signature's values are the values at the positions it discloses. -/
theorem layerSig_eq_some {idx : Index} {l : Layer} {sigL : LayerSignature l}
    (h : v.layerSig H idx l = some sigL) :
    ∃ sel, v.layerSelect H idx l = some sel ∧ sigL.counter = sel.1 ∧
      (∀ i, sigL.chainValues i =
        v.valuePos (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val)) ∧
      ∀ z : Fin (layerHeight l), sigL.authenticationPath z =
        v.valuePos (tpos l (treeOfIndex l idx) z.val
          (((leafOfIndex l idx).val >>> z.val) ^^^ 1)) := by
  rw [layerSig, layerSignature, Option.map_eq_some_iff] at h
  obtain ⟨sel, hsel, rfl⟩ := h
  refine ⟨sel, hsel, rfl, fun i ↦ (v.valuePos_cpos _ _ _ i (sel.2 i).isLt).symm, fun z ↦ ?_⟩
  have hl := layerHeight_le l
  have ht : layerHeight topLayer = 10 := rfl
  have hz := z.isLt
  have hb := shiftRight_xor_lt (leafOfIndex_lt l idx) z.isLt
  rw [v.valuePos_tpos _ _ (level := z.val) (by omega)
    (lt_of_lt_of_le (lt_two_pow_of_lt hb) (two_pow_layerHeight_le l))]
  rfl

/-- **A signature's values are the values at the disclosed positions**: the FORS secrets and
paths, and each layer's opened chain values and path. -/
theorem signature_eq_some {message : Message} {sig : Signature}
    (h : v.signature H message = some sig) :
    sig.randomizer = v.randomizer message ∧
    (∀ κ, (sig.forsOpening κ).secret =
        v.valuePos (.forsSecret (v.index message) κ (v.leaves message κ)) ∧
      ∀ z : Fin forsTreeHeight, (sig.forsOpening κ).path z = v.valuePos
        (fpos (v.index message) κ z.val (((v.leaves message κ).val >>> z.val) ^^^ 1))) ∧
    ∀ l, ∃ sel, v.layerSelect H (v.index message) l = some sel ∧
      (sig.layers l).counter = sel.1 ∧
      (∀ i, (sig.layers l).chainValues i =
        v.valuePos (cpos l (treeOfIndex l (v.index message)) (leafOfIndex l (v.index message)) i
          (sel.2 i).val)) ∧
      ∀ z : Fin (layerHeight l), (sig.layers l).authenticationPath z =
        v.valuePos (tpos l (treeOfIndex l (v.index message)) z.val
          (((leafOfIndex l (v.index message)).val >>> z.val) ^^^ 1)) := by
  unfold signature at h
  cases h0 : v.layerSig H (v.index message) 0 with
  | none => rw [h0] at h; simp at h
  | some bottom =>
    cases h1 : v.layerSig H (v.index message) 1 with
    | none => rw [h0, h1] at h; simp at h
    | some middle =>
      cases h2 : v.layerSig H (v.index message) 2 with
      | none => rw [h0, h1, h2] at h; simp at h
      | some top =>
        rw [h0, h1, h2] at h
        obtain rfl := Option.some.inj h
        refine ⟨rfl, fun κ ↦ ⟨rfl, fun z ↦ ?_⟩, fun l ↦ ?_⟩
        · have hb := shiftRight_xor_lt (v.leaves message κ).isLt z.isLt
          rw [v.valuePos_fpos _ κ z.isLt.le (lt_two_pow_of_lt hb)]
          rfl
        · fin_cases l
          · exact v.layerSig_eq_some H h0
          · exact v.layerSig_eq_some H h1
          · exact v.layerSig_eq_some H h2

end QTable

end Quantum.Qrom.Sphincs

end
