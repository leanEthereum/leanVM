module

public import Quantum.Qrom.Sphincs.HonestTable

@[expose] public section

/-!
# leanSPHINCS at a fixed hash: the honest structure and the property events

At a fixed table every hash is a function `h : HashInput → HashOutput`. The honest structure of a
leanSPHINCS key is a table `v : QTable` (`Quantum.Qrom.Sphincs.QTable`): its secret positions (the
key expansion, the WOTS chain starts, the FORS secrets, the randomizers) hold arbitrary values, and
every other position holds the hash of its honest input (`Honest h v`). The honest signature of `M`
is `v.signature (cellHash h) M`, the public key `v.publicKey`.

The events of the reduction (design, Theorem 2), each a property win against the honest structure:

* `EvItsr`: the forgery's pair `(R*, M*)` is no signed pair, and the cells its digest selects are
  covered by the cells of the signed messages' digests (ITSR).
* `EvEnc`: a key in use signs its message at its selected counter, and another pair of message and
  counter has the same encoding digest (EncTCR+C).
* `EvTcr`: a target position (a WOTS leaf `T_v`, a hypertree or FORS node `H`, a FORS key `T_k`)
  has a different payload at its slot with the honest digest (SM-TCR).
* `EvCpre`: a WOTS chain walks a value from a position below its end to the honest end, the value
  differing from the honest one there or the position below the key's selected digit, or a FORS
  secret maps to the honest FORS leaf, differing from the honest secret or never disclosed by a
  returned signature (CPRE).
-/

open HashSig hiding PublicKey
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey)
open Quantum.Sphincs (Key msgPos treeBits)
open Quantum.Qrom.Sphincs (QTable RawPos Pos posInput posPayload posSlot slotInput digPos)

namespace Quantum.StdModel.Sphincs

/-! ## The honest structure -/

/-- The hash as a function of the random-oracle model's cells. -/
def cellHash (h : HashInput → HashOutput) : Qrom.HashDomain → HashOutput :=
  fun x ↦ h (Qrom.decodeInput x)

/-- The secret positions: the key expansion, the chain starts, the FORS secrets, the
randomizers. -/
def IsSecret : RawPos → Prop
  | .prfKey | .publicSeed | .chainStart .. | .forsSecret .. | .prfMsg _ => True
  | _ => False

/-- **The honest structure of `h`**: every position other than a secret holds the hash of its
honest input, and the digest cell's second component is call 1 of `H_msg`. -/
structure Honest (h : HashInput → HashOutput) (v : QTable) : Prop where
  out : ∀ p : Pos, ¬IsSecret p.1 → (v p).1 = h (posInput 0 v p.1)
  call1 : ∀ message, (v (digPos message)).2 =
    h (Quantum.Sphincs.messageDigestInput (v.randomizer message) v.publicSeed v.root message 1)

/-- The expanded key with the public seed `P` and no secret. -/
def pubKey (P : PublicParameter) : ExpandedKey :=
  ⟨0, 0, P⟩

/-- `Th` at a slot: the first 16 bytes of the hash of the slot's input. -/
def thSlot (h : HashInput → HashOutput) (P : PublicParameter) (s : Quantum.Sphincs.Slot)
    (p : Quantum.Qrom.Sphincs.SlotPayload s) : Digest :=
  truncateHash (h (slotInput (pubKey P) 0 s p))

/-- A key in use: its tree and leaf in range. -/
def KeyIn (K : Key) : Prop :=
  K.2.1.val < 2 ^ treeBits K.1 ∧ K.2.2.val < 2 ^ layerHeight K.1

/-- The message the key `K` signs in every signature. -/
def keyMessage (v : QTable) (K : Key) : Digest :=
  v.valuePos (msgPos K)

/-- The selection of the key `K` on its message. -/
def keySelect (h : HashInput → HashOutput) (v : QTable) (K : Key) :
    Option (EncodingCounter × Encoding) :=
  v.select (cellHash h) K.1 K.2.1 K.2.2 (keyMessage v K)

/-- The chain walk of chain `i` of the key `K` under `h`, from position `μ`, `n` steps. -/
def walkH (h : HashInput → HashOutput) (P : PublicParameter) (K : Key) (i : ChainIndex) (μ n : ℕ)
    (z : Digest) : Digest :=
  Quantum.Qrom.Sphincs.LeanSphincsOver.chainWalk (m := Id) (fun l ↦ h l) P K.1 K.2.1 K.2.2 i μ n z

/-- The cells a digest selects: the FORS instance with one leaf per tree. -/
def digestCells (d : MessageDigest) : Finset (Index × ForsTreeIndex × ForsLeafIndex) :=
  Finset.univ.image fun κ ↦ (digestIndex d, κ, digestForsLeaves d κ)

/-- The digest of `(R, M)` under the public key `pk`. -/
def digestOf (h : HashInput → HashOutput) (pk : PublicKey) (R : Randomizer) (M : Message) :
    MessageDigest :=
  truncateMessageDigest fun c ↦
    h (Quantum.Sphincs.messageDigestInput R pk.publicSeed pk.root M c)

/-! ## The events -/

variable (h : HashInput → HashOutput) (v : QTable)

/-- **ITSR**: the forgery's pair is no signed pair, and its cells are covered by the signed
messages' cells. -/
def EvItsr (log : List Message) (R : Randomizer) (M : Message) : Prop :=
  (R, M) ∉ log.map (fun M' ↦ (v.randomizer M', M')) ∧
    digestCells (digestOf h v.publicKey R M) ⊆
      (log.map fun M' ↦ digestCells (digestOf h v.publicKey (v.randomizer M') M')).foldr
        (· ∪ ·) ∅

/-- **EncTCR+C**: a key in use, selected at counter `c` on its message `m`, and a pair
`(m', c') ≠ (m, c)` with the same encoding digest. -/
def EvEnc : Prop :=
  ∃ K, KeyIn K ∧ ∃ sel, keySelect h v K = some sel ∧ ∃ (m' : Digest) (c' : EncodingCounter),
    (m', c') ≠ (keyMessage v K, sel.1) ∧
      thSlot h v.publicSeed (.enc K.1 K.2.1 K.2.2) (m', c') =
        thSlot h v.publicSeed (.enc K.1 K.2.1 K.2.2) (keyMessage v K, sel.1)

/-- The target positions of SM-TCR: WOTS leaves, hypertree and FORS nodes, FORS keys. -/
def IsTarget : RawPos → Prop
  | .leaf .. | .node .. | .forsNode .. | .forsRoots _ => True
  | _ => False

/-- **SM-TCR**: a target position and a different payload at its slot with the honest digest. -/
def EvTcr : Prop :=
  ∃ p : Pos, IsTarget p.1 ∧ ∃ d : Quantum.Qrom.Sphincs.SlotPayload (posSlot v p.1),
    d ≠ posPayload v p.1 ∧ thSlot h v.publicSeed (posSlot v p.1) d = v.dig p.1

/-- The FORS leaf `(idx, κ, s)` is disclosed by a returned signature of a signed message. -/
def ForsOpened (log : List Message) (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
    Prop :=
  ∃ M ∈ log, (v.signature (cellHash h) M).isSome ∧ v.index M = idx ∧ v.leaves M κ = s

/-- **CPRE**: a WOTS chain of a key in use walks `z` from position `μ` below its end to the
honest end, with `z` not the honest value or `μ` below the key's selected digit (or the key has no
selection); or a FORS secret `z` maps to the honest FORS leaf, `z` not the honest secret or the
leaf never disclosed. -/
def EvCpre (log : List Message) : Prop :=
  (∃ K, KeyIn K ∧ ∃ (i : ChainIndex) (μ : ℕ), μ < chainLength - 1 ∧ ∃ z,
    walkH h v.publicSeed K i μ (chainLength - 1 - μ) z = v.endpoints K.1 K.2.1 K.2.2 i ∧
      (z ≠ v.chainValue K.1 K.2.1 K.2.2 i μ ∨
        ¬∃ sel, keySelect h v K = some sel ∧ (sel.2 i).val ≤ μ)) ∨
  ∃ (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) (z : Digest),
    thSlot h v.publicSeed (.forsLeaf idx κ s) z = v.forsValue idx κ 0 s.val ∧
      (z ≠ v.forsSecret idx κ s ∨ ¬ForsOpened h v log idx κ s)

end Quantum.StdModel.Sphincs

end
