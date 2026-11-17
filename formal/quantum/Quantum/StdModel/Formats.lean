module

public import Quantum.Qrom.Sphincs.Slots
public import Quantum.Qrom.Xmss.Slots
public import Quantum.StdModel.World

@[expose] public section

/-!
# The Keccak-256 inputs of leanXMSS and leanSPHINCS

Every Keccak-256 call of either scheme hashes the honest input of one slot, a function of the
public parameter (and, for leanSPHINCS, the expanded key and root), the slot (the role and the
tweak) and the payload. The rows of the design's call tables:

* leanXMSS (`Quantum.Xmss.Slot`, input `Qrom.Xmss.slotInput P s d`, `d : Qrom.Xmss.Payload s`):
  X1 `.seed` (`S = H("leanXMSS" ‖ S_0)`), X2 `.param`, X3 `.prf l e j`, X4 `.rnd l e`,
  X5 `.msg l e`, X6 `.chain l e μ i` (the tweak of a chain step is its address and the chain
  index `i` of its payload), X7 `.leaf l e`, X8 `.node l λ j`.
* leanSPHINCS (`Quantum.Sphincs.Slot`, input `Qrom.Sphincs.slotInput key root s p`): S1 and S2
  `.expand d`, S3 `.prf d`, S4 `.prfMsg M`, S5 `.hmsg R M c`, S6 `.enc l t e`, S7 `.chain …`,
  S8 `.forsLeaf …`, S9 `.node …` and `.forsNode …`, S10 `.leaf …`, S11 `.forsRoots i`.

## Main statements

* `xmss_slotInput_inj`, `sphincs_slotInput_inj` (**DIST**): two honest inputs are equal only for
  the same slot and payload; so distinct slots (distinct roles, or distinct tweaks of one role)
  never share an input, whatever their payloads (`xmss_slotInput_ne`, `sphincs_slotInput_ne`).
* Call sites: each hash call of the schemes (over any hash, in any monad) hashes its slot's
  input (`xmss_chainStep_eq`, …, `sphincs_chainStep_eq`, …).
* `thAt W tab input`: the tweakable hash `Th` at a fixed table of a world; at `keccakWorld` it is
  the first 16 bytes of the statement's Keccak-256 (`thAt_keccakWorld`), and classically it is
  what the schemes' `Th` returns (`simulateQ_th`).
-/

open OracleComp OracleSpec

namespace Quantum.StdModel

/-! ## The tweakable hash at a fixed table -/

/-- **`Th` at the table `tab`**: the first 16 bytes of Keccak-256 at `tab`. -/
def thAt (W : OracleWorld) (tab : W.Tab) (input : HashSig.HashInput) : HashSig.Digest :=
  HashSig.truncateHash (W.hashOf tab input)

/-- The schemes' `Th` on an input, answered by a fixed table, is `thAt`. -/
theorem simulateQ_th (W : OracleWorld) (tab : W.Tab) (input : HashSig.HashInput) :
    simulateQ (W.eager tab) (do return HashSig.truncateHash (← W.hash input)) =
      pure (thAt W tab input) := by
  rw [simulateQ_bind, W.simulateQ_hash, pure_bind, simulateQ_pure]
  rfl

/-- **The standard-model `Th`** is the first 16 bytes of Keccak-256 over Keccak-f[1600]. -/
theorem thAt_keccakWorld (input : HashSig.HashInput) :
    thAt keccakWorld () input = HashSig.truncateHash (Id.run (HashSig.OverPermutation.keccakHash
      (fun s ↦ (pure (LeanVM.Semantics.keccakF1600 s) : Id LeanVM.Semantics.KeccakState))
      input)) :=
  rfl

/-! ## leanXMSS -/

section Xmss

open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Qrom.Xmss (Payload slotInput Addressable MsgBytes cell cell_injective)

/-- **DIST for leanXMSS**: under one public parameter, two honest inputs of addressable slots
are equal only for the same slot and payload. -/
theorem xmss_slotInput_inj (P : PublicParameter) {s s' : Slot} (hs : Addressable s)
    (hs' : Addressable s') {d : Payload s} {d' : Payload s'}
    (h : slotInput P s d = slotInput P s' d') : (⟨s, d⟩ : Σ s, Payload s) = ⟨s', d'⟩ :=
  cell_injective P hs hs' (congrArg (fun l ↦ (Qrom.encodeInput l).getD 0) h)

/-- Distinct addressable slots never share an input. -/
theorem xmss_slotInput_ne (P : PublicParameter) {s s' : Slot} (hs : Addressable s)
    (hs' : Addressable s') (hne : s ≠ s') (d : Payload s) (d' : Payload s') :
    slotInput P s d ≠ slotInput P s' d' :=
  fun h ↦ hne (congrArg Sigma.fst (xmss_slotInput_inj P hs hs' h))

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (P : PublicParameter)

omit [Monad m] in
/-- X1: the scheme seed hashes the input of `.seed`. -/
theorem xmss_schemeSeed_eq (masterSeed : MasterSeed) :
    Qrom.Xmss.Over.schemeSeedOf hash masterSeed = hash (slotInput P .seed masterSeed) :=
  rfl

/-- X2: the public parameter hashes the input of `.param`. -/
theorem xmss_publicParameter_eq (seed : MasterSeed) :
    Qrom.Xmss.Over.publicParameterOf hash seed =
      (do return truncateHash (← hash (slotInput P .param seed))) :=
  rfl

omit [Monad m] in
/-- X3: the starts of chains `2j`, `2j + 1` hash the input of `.prf l e j`. -/
theorem xmss_chainStarts_eq (layer : Layer) (key : KeyIndex) (pair : ChainPairIndex)
    (seed : MasterSeed) :
    Qrom.Xmss.Over.thPair hash P (keygenDomainFields (.oneTimeChainPair layer key pair))
        (littleEndianBytes 32 seed) = hash (slotInput P (.prf layer key pair) seed) :=
  rfl

/-- X4: the randomizer base hashes the input of `.rnd l e`. -/
theorem xmss_randomizerBase_eq (layer : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : MsgBytes) :
    Qrom.Xmss.Over.th hash P (tweakFields 7 0 (layerHi layer 0) key)
        (littleEndianBytes 32 seed ++ message.1) =
      (do return truncateHash (← hash (slotInput P (.rnd layer key) (seed, message)))) :=
  rfl

/-- X5: the message digest hashes the input of `.msg l e`. -/
theorem xmss_messageDigest_eq (layer : Layer) (key : KeyIndex) (message : MsgBytes)
    (randomizer : Randomizer) :
    Qrom.Xmss.Over.messageDigest hash P layer key message.1 randomizer =
      (do return truncateHash (← hash (slotInput P (.msg layer key) (message, randomizer)))) :=
  rfl

/-- X6: step `μ` of chain `i` hashes the input of `.chain l e μ i`. -/
theorem xmss_chainStep_eq (layer : Layer) (key : KeyIndex) (step : ChainStep)
    (chain : ChainIndex) (value : Digest) :
    Qrom.Xmss.Over.tweakableHash hash P (.chain layer key step)
        (Verification.chainPayload chain value) =
      (do return truncateHash (← hash (slotInput P (.chain layer key step chain) value))) :=
  rfl

/-- X7: the leaf hashes the input of `.leaf l e`. -/
theorem xmss_leaf_eq (layer : Layer) (key : KeyIndex) (endpoints : ChainIndex → Digest) :
    Qrom.Xmss.Over.leafHash hash P layer key endpoints =
      (do return truncateHash (← hash (slotInput P (.leaf layer key) endpoints))) :=
  rfl

/-- X8: a tree node hashes the input of `.node l λ j`. -/
theorem xmss_node_eq (layer : Layer) (level nodeIndex : ℕ) (left right : Digest) :
    Qrom.Xmss.Over.tweakableHash hash P (.node layer level nodeIndex) (nodePayload left right) =
      hash (slotInput P (.node layer level nodeIndex) (left, right)) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

end Xmss

/-! ## leanSPHINCS -/

section Sphincs

open HashSig hiding PublicKey
open HashSig.OverPermutation (nodePayload)
open _root_.Sphincs hiding HashDomain
open _root_.Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput)
open Quantum.Sphincs (Slot)
open Quantum.Qrom.Sphincs (SlotPayload slotInput SlotInRange codeOf_congr cell cell_injective)

/-- **DIST for leanSPHINCS**: under one expanded key and root, two honest inputs of in-range
slots are equal only for the same slot and payload. -/
theorem sphincs_slotInput_inj (key : ExpandedKey) (root : Digest) {s s' : Slot}
    (hs : SlotInRange s) (hs' : SlotInRange s') {p : SlotPayload s} {p' : SlotPayload s'}
    (h : slotInput key root s p = slotInput key root s' p') :
    (⟨s, p⟩ : Σ s, SlotPayload s) = ⟨s', p'⟩ :=
  cell_injective key root hs hs' (codeOf_congr h _ _)

/-- Distinct in-range slots never share an input. -/
theorem sphincs_slotInput_ne (key : ExpandedKey) (root : Digest) {s s' : Slot}
    (hs : SlotInRange s) (hs' : SlotInRange s') (hne : s ≠ s') (p : SlotPayload s)
    (p' : SlotPayload s') : slotInput key root s p ≠ slotInput key root s' p' :=
  fun h ↦ hne (congrArg Sigma.fst (sphincs_slotInput_inj key root hs hs' h))

variable {m : Type → Type} [Monad m] (hash : HashInput → m HashOutput) (key : ExpandedKey)
  (root : Digest)

omit [Monad m] in
/-- S1, S2: the key expansion hashes the inputs of `.expand 0` and `.expand 1`. -/
theorem sphincs_expand_eq (domain : UInt8) :
    hash (keyDerivationInput key.secretSeed domain) =
      hash (slotInput key root (.expand domain) ()) :=
  rfl

/-- S3: a WOTS chain start or FORS secret hashes the input of `.prf d`. -/
theorem sphincs_prf_eq (domain : KeygenDomain) :
    Qrom.Sphincs.LeanSphincsOver.prf hash key domain =
      (do return truncateHash (← hash (slotInput key root (.prf domain) ()))) :=
  rfl

/-- S4: `PRF_msg` (with the public seed as its optional randomness) hashes the input of
`.prfMsg M`. -/
theorem sphincs_prfMessage_eq (message : Message) :
    Qrom.Sphincs.LeanSphincsOver.prfMessage hash key.secretPrfKey key.publicSeed message =
      (do return truncateHash (← hash (slotInput key root (.prfMsg message) ()))) :=
  rfl

omit [Monad m] in
/-- S5: call `c` of `H_msg` hashes the input of `.hmsg R M c`. -/
theorem sphincs_messageDigestCall_eq (randomizer : Randomizer) (message : Message)
    (call : DigestCall) :
    Qrom.Sphincs.LeanSphincsOver.messageDigestCall hash randomizer key.publicSeed root message
        call = hash (slotInput key root (.hmsg randomizer message call) ()) :=
  rfl

/-- S6: an encoding trial hashes the input of `.enc l t e`. -/
theorem sphincs_encoding_eq (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) (counter : EncodingCounter) :
    Qrom.Sphincs.LeanSphincsOver.tweakableHash hash key.publicSeed (.encoding layer tree leaf)
        (littleEndianBytes 16 message ++ bigEndianBytes 4 counter) =
      hash (slotInput key root (.enc layer tree leaf) (message, counter)) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S7: a chain step hashes the input of `.chain l t e i μ`. -/
theorem sphincs_chainStep_eq (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (chainIndex : ChainIndex) (step : ChainStep) (value : Digest) :
    Qrom.Sphincs.LeanSphincsOver.tweakableHash hash key.publicSeed
        (.chain layer tree leaf chainIndex step)
        (littleEndianBytes 16 value) =
      hash (slotInput key root (.chain layer tree leaf chainIndex step) value) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S8: a FORS leaf hashes the input of `.forsLeaf i κ s`. -/
theorem sphincs_forsLeaf_eq (index : Index) (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex)
    (secret : Digest) :
    Qrom.Sphincs.LeanSphincsOver.forsLeafHash hash key.publicSeed index forsTree forsLeaf secret =
      hash (slotInput key root (.forsLeaf index forsTree forsLeaf) secret) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S9: a hypertree node hashes the input of `.node l t h j`. -/
theorem sphincs_node_eq (layer : Layer) (tree : TreeIndex) (height nodeIndex : ℕ)
    (left right : Digest) :
    Qrom.Sphincs.LeanSphincsOver.tweakableHash hash key.publicSeed
        (.node layer tree height nodeIndex)
        (nodePayload left right) =
      hash (slotInput key root (.node layer tree height nodeIndex) (left, right)) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S9: a FORS node hashes the input of `.forsNode i κ h j`. -/
theorem sphincs_forsNode_eq (index : Index) (forsTree : ForsTreeIndex) (height node : ℕ)
    (left right : Digest) :
    Qrom.Sphincs.LeanSphincsOver.tweakableHash hash key.publicSeed
        (.forsNode index forsTree height node)
        (nodePayload left right) =
      hash (slotInput key root (.forsNode index forsTree height node) (left, right)) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S10: a WOTS leaf hashes the input of `.leaf l t e`. -/
theorem sphincs_leaf_eq (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (endpoints : ChainIndex → Digest) :
    Qrom.Sphincs.LeanSphincsOver.leafHash hash key.publicSeed layer tree leaf endpoints =
      hash (slotInput key root (.leaf layer tree leaf) endpoints) >>=
        fun output ↦ pure (truncateHash output) :=
  rfl

/-- S11: a FORS public key hashes the input of `.forsRoots i`. -/
theorem sphincs_forsRoots_eq (index : Index) (roots : ForsTreeIndex → Digest) :
    Qrom.Sphincs.LeanSphincsOver.forsPublicKey hash key.publicSeed index roots =
      (do return truncateHash (← hash (slotInput key root (.forsRoots index) roots))) :=
  rfl

end Sphincs

end Quantum.StdModel

end
