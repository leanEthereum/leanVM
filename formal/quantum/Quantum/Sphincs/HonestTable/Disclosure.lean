module

public import Quantum.Sphincs.HonestTable.Values

@[expose] public section

/-!
# leanSPHINCS's value positions, slots and disclosures

* `ValPos`, `valuePos L`: the positions of the honest 128-bit values and their values (contract
  C1, `Quantum.Sphincs.HonestTable`); `cpos`, `tpos`, `fpos` the positions at natural indices
  (reduced into range), `rootPos` the position of `PK.root`.
* `InTable`: the structural slots of the honest table (chain steps, one-time leaves and tree nodes
  of the hypertree, FORS leaves, nodes and roots compressions). `slotOutPos s`, `slotNeed s`: the
  position a slot outputs and the positions its honest path depends on; `slotInput seed s f` the
  input of a structural or `H_msg` slot from the values `f`; `honestInput_eq_slotInput`,
  `honestInput_hmsg_eq_slotInput`: at `valuePos L`, the honest input. `target_eq_some`: the digest
  of a structural slot's honest input is the value at its output.
* `honestInput`, `honestTail`, `target` for every slot kind with one honest input (structural,
  `H_msg` at the honest randomizer, `PRF`, `PRF_msg`, the key expansion); `slotOf_honestTail`: the
  honest tail lies in its slot.
* `msgPos K`, `msgPos_eq`: the one value each WOTS+C key signs; `layerSig_eq`, `layerSelect_eq`:
  the counter search of `K_l(idx)` runs on `valuePos L (msgPos (keyOf l idx))`.
* `Known D`, `Public D`: the positions computable from the disclosed positions `D` and the
  structural slots whose payload is computable; `disclosedBy L M`: the positions the signature of
  `M` discloses (the FORS secrets at the digest's leaves and their paths, each layer's opened chain
  positions and path); `disclosures L msgs`; `signature_eq_some`: a returned signature's values are
  the values at those positions.
-/

open Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed ChainStep
  chainLength littleEndianBytes truncateHash digestsPayload)
open HashSig.OverPermutation (nodePayload)
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Xmss (X Z blocks trunc128)

namespace Quantum.Sphincs

/-! ## Value positions (contract C1) -/

/-- **A position of an honest 128-bit value.** -/
inductive ValPos where
  /-- Position `j` of chain `i` of the one-time key `(l, τ, e)`; `j = 0` is the chain start. -/
  | chain (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (j : Fin chainLength)
  /-- The value of tree `τ` of layer `l` at `level`, index `index`: the one-time leaf of key `index`
  at level `0`, a node above. -/
  | tree (l : Layer) (τ : TreeIndex) (level : Fin (layerHeight topLayer + 1))
      (index : TreeLeafIndex)
  /-- The secret of leaf `s` of FORS tree `κ` of instance `idx`. -/
  | forsSecret (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex)
  /-- The value of FORS tree `κ` of instance `idx` at `height`, node `node`: the FORS leaf at height
  `0`, a node above, the root at height `a`. -/
  | forsTree (idx : Index) (κ : ForsTreeIndex) (height : Fin (forsTreeHeight + 1))
      (node : ForsLeafIndex)
  /-- The FORS public key of instance `idx`. -/
  | forsKey (idx : Index)
  deriving DecidableEq, Fintype

/-- Position `j` of a chain (reduced into range). -/
def cpos (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (j : ℕ) : ValPos :=
  .chain l τ e i ⟨j % chainLength, Nat.mod_lt _ (by decide)⟩

/-- The value of a tree at `level`, index `index` (reduced into range). -/
def tpos (l : Layer) (τ : TreeIndex) (level index : ℕ) : ValPos :=
  .tree l τ ⟨level % (layerHeight topLayer + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨index % 2 ^ layerHeight topLayer, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The value of a FORS tree at `height`, node `node` (reduced into range). -/
def fpos (idx : Index) (κ : ForsTreeIndex) (height node : ℕ) : ValPos :=
  .forsTree idx κ ⟨height % (forsTreeHeight + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨node % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The position of `PK.root`: the top tree's root. -/
def rootPos : ValPos :=
  tpos topLayer 0 (layerHeight topLayer) 0

/-- **The honest value at a position.** -/
def valuePos (L : HonestTable) : ValPos → Digest
  | .chain l τ e i j => L.chainValue l τ e i j.val
  | .tree l τ level index => L.treeValue l τ level.val index.val
  | .forsSecret idx κ s => L.forsSecret idx κ s
  | .forsTree idx κ height node => L.forsValue idx κ height.val node.val
  | .forsKey idx => L.forsKey idx

section Values

variable (L : HonestTable)

theorem valuePos_cpos (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) {j : ℕ}
    (hj : j < chainLength) : valuePos L (cpos l τ e i j) = L.chainValue l τ e i j := by
  change L.chainValue l τ e i (j % chainLength) = _
  rw [Nat.mod_eq_of_lt hj]

theorem valuePos_tpos (l : Layer) (τ : TreeIndex) {level index : ℕ}
    (hl : level ≤ layerHeight topLayer) (hi : index < 2 ^ layerHeight topLayer) :
    valuePos L (tpos l τ level index) = L.treeValue l τ level index := by
  change L.treeValue l τ (level % (layerHeight topLayer + 1)) (index % 2 ^ layerHeight topLayer) = _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hl), Nat.mod_eq_of_lt hi]

theorem valuePos_fpos (idx : Index) (κ : ForsTreeIndex) {height node : ℕ}
    (hh : height ≤ forsTreeHeight) (hn : node < 2 ^ forsTreeHeight) :
    valuePos L (fpos idx κ height node) = L.forsValue idx κ height node := by
  change L.forsValue idx κ (height % (forsTreeHeight + 1)) (node % 2 ^ forsTreeHeight) = _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hh), Nat.mod_eq_of_lt hn]

theorem valuePos_rootPos : valuePos L rootPos = L.root :=
  valuePos_tpos L topLayer 0 (level := layerHeight topLayer) (index := 0) le_rfl
    (Nat.two_pow_pos _)

end Values

/-- `2 j + 1 < 2^a` for a node `j < 2^(a - h)` at height `h ≥ 1`: its children are in range. -/
theorem two_mul_add_one_lt {j a h : ℕ} (hj : j < 2 ^ (a - h)) (h1 : 1 ≤ h) (ha : h ≤ a) :
    2 * j + 1 < 2 ^ a := by
  have hp : 2 ^ (a - h) * 2 ≤ 2 ^ a := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem lt_two_pow_of_lt {j a h : ℕ} (hj : j < 2 ^ (a - h)) : j < 2 ^ a :=
  lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le a h))

theorem two_pow_layerHeight_le (l : Layer) : 2 ^ layerHeight l ≤ 2 ^ layerHeight topLayer :=
  Nat.pow_le_pow_right (by norm_num) (layerHeight_le l)

/-! ## Structural slots -/

/-- The bits of a tree index of layer `l`: `18`, `10`, `0` from the bottom. -/
def treeBits (l : Layer) : ℕ :=
  indexBits - bitsBelowLayer l - layerHeight l

/-- **The structural slots of the honest table**: the chain steps and leaves of the keys and the
nodes at heights `1` to `h_l` of the trees of the hypertree, and every FORS leaf, node (heights `1`
to `a`) and roots compression. -/
def InTable : Slot → Prop
  | .chain l τ e _ _ => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .leaf l τ e => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .node l τ height index =>
      τ.val < 2 ^ treeBits l ∧ 1 ≤ height ∧ height ≤ layerHeight l ∧
        index < 2 ^ (layerHeight l - height)
  | .forsLeaf .. => True
  | .forsNode _ _ height node =>
      1 ≤ height ∧ height ≤ forsTreeHeight ∧ node < 2 ^ (forsTreeHeight - height)
  | .forsRoots _ => True
  | _ => False

instance instDecidablePredInTable : DecidablePred InTable := fun s ↦ by
  cases s <;> unfold InTable <;> infer_instance

/-- The hash domain of a slot's call (the FORS roots of instance `0` for a slot of none). -/
def slotDomain : Slot → HashDomain
  | .chain l τ e i step => .chain l τ e i step
  | .leaf l τ e => .leaf l τ e
  | .node l τ height index => .node l τ height index
  | .enc l τ e => .encoding l τ e
  | .forsLeaf idx κ s => .forsLeaf idx κ s
  | .forsNode idx κ height node => .forsNode idx κ height node
  | .forsRoots idx => .forsRoots idx
  | _ => .forsRoots 0

/-- **The position a slot outputs**: a structural slot's value, a secret's (a chain start or a FORS
secret); `rootPos` for the other slots. -/
def slotOutPos : Slot → ValPos
  | .chain l τ e i step => cpos l τ e i (step.val + 1)
  | .leaf l τ e => tpos l τ 0 e.val
  | .node l τ height index => tpos l τ height index
  | .forsLeaf idx κ s => fpos idx κ 0 s.val
  | .forsNode idx κ height node => fpos idx κ height node
  | .forsRoots idx => .forsKey idx
  | .prf (.oneTimeChain l τ e i) => cpos l τ e i 0
  | .prf (.forsSecret idx κ s) => .forsSecret idx κ s
  | _ => rootPos

/-- **The positions a slot's honest path depends on**: a structural slot's payload positions and
output position, `PK.root` for `H_msg`, the output of a secret. -/
def slotNeed : Slot → Finset ValPos
  | .chain l τ e i step => {cpos l τ e i step.val, cpos l τ e i (step.val + 1)}
  | .leaf l τ e =>
      insert (tpos l τ 0 e.val) (Finset.univ.image fun i ↦ cpos l τ e i (chainLength - 1))
  | .node l τ height index =>
      {tpos l τ (height - 1) (2 * index), tpos l τ (height - 1) (2 * index + 1),
        tpos l τ height index}
  | .forsLeaf idx κ s => {.forsSecret idx κ s, fpos idx κ 0 s.val}
  | .forsNode idx κ height node =>
      {fpos idx κ (height - 1) (2 * node), fpos idx κ (height - 1) (2 * node + 1),
        fpos idx κ height node}
  | .forsRoots idx =>
      insert (.forsKey idx) (Finset.univ.image fun κ ↦ fpos idx κ forsTreeHeight 0)
  | .hmsg .. => {rootPos}
  | .prf (.oneTimeChain l τ e i) => {cpos l τ e i 0}
  | .prf (.forsSecret idx κ s) => {.forsSecret idx κ s}
  | _ => ∅

/-- The payload of a structural slot from the values `f` at the positions. -/
def slotPayload (f : ValPos → Digest) : Slot → HashInput
  | .chain l τ e i step => littleEndianBytes 16 (f (cpos l τ e i step.val))
  | .leaf l τ e => digestsPayload fun i ↦ f (cpos l τ e i (chainLength - 1))
  | .node l τ height index =>
      nodePayload (f (tpos l τ (height - 1) (2 * index)))
        (f (tpos l τ (height - 1) (2 * index + 1)))
  | .forsLeaf idx κ s => littleEndianBytes 16 (f (.forsSecret idx κ s))
  | .forsNode idx κ height node =>
      nodePayload (f (fpos idx κ (height - 1) (2 * node)))
        (f (fpos idx κ (height - 1) (2 * node + 1)))
  | .forsRoots idx => digestsPayload fun κ ↦ f (fpos idx κ forsTreeHeight 0)
  | _ => []

/-- **The input of a slot from the values `f`**: a structural slot's addressed input under
`PK.seed` with its payload, an `H_msg` call's input at the root `f rootPos`. -/
def slotInput (publicSeed : PublicParameter) (s : Slot) (f : ValPos → Digest) : HashInput :=
  match s with
  | .hmsg randomizer message call =>
      messageDigestInput randomizer publicSeed (f rootPos) message call
  | _ => addressedHashInput publicSeed (hashDomainFields (slotDomain s)) (slotPayload f s)

theorem slotOutPos_mem_slotNeed {s : Slot} (hs : InTable s) : slotOutPos s ∈ slotNeed s := by
  cases s with
  | chain => simp [slotNeed, slotOutPos]
  | leaf => simp [slotNeed, slotOutPos]
  | node => simp [slotNeed, slotOutPos]
  | forsLeaf => simp [slotNeed, slotOutPos]
  | forsNode => simp [slotNeed, slotOutPos]
  | forsRoots => simp [slotNeed, slotOutPos]
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

theorem slotOutPos_mem_slotNeed_prf (d : KeygenDomain) :
    slotOutPos (.prf d) ∈ slotNeed (.prf d) := by
  cases d <;> simp [slotNeed, slotOutPos]

/-- **A slot's input depends on the values only at its coordinates.** -/
theorem slotInput_congr (publicSeed : PublicParameter) {s : Slot} {f g : ValPos → Digest}
    (h : ∀ p ∈ slotNeed s, f p = g p) : slotInput publicSeed s f = slotInput publicSeed s g := by
  cases s with
  | chain l τ e i step =>
    change addressedHashInput _ _ (littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (littleEndianBytes 16 (g _))
    rw [h (cpos l τ e i step.val) (by simp [slotNeed])]
  | leaf l τ e =>
    change addressedHashInput _ _ (digestsPayload fun i ↦ f _) =
      addressedHashInput _ _ (digestsPayload fun i ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun i ↦
      h _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))
  | node l τ height index =>
    change addressedHashInput _ _ (nodePayload (f _) (f _)) =
      addressedHashInput _ _ (nodePayload (g _) (g _))
    rw [h (tpos l τ (height - 1) (2 * index)) (by simp [slotNeed]),
      h (tpos l τ (height - 1) (2 * index + 1)) (by simp [slotNeed])]
  | forsLeaf idx κ s =>
    change addressedHashInput _ _ (littleEndianBytes 16 (f _)) =
      addressedHashInput _ _ (littleEndianBytes 16 (g _))
    rw [h (.forsSecret idx κ s) (by simp [slotNeed])]
  | forsNode idx κ height node =>
    change addressedHashInput _ _ (nodePayload (f _) (f _)) =
      addressedHashInput _ _ (nodePayload (g _) (g _))
    rw [h (fpos idx κ (height - 1) (2 * node)) (by simp [slotNeed]),
      h (fpos idx κ (height - 1) (2 * node + 1)) (by simp [slotNeed])]
  | forsRoots idx =>
    change addressedHashInput _ _ (digestsPayload fun κ ↦ f _) =
      addressedHashInput _ _ (digestsPayload fun κ ↦ g _)
    exact congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun κ ↦
      h _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ κ)))))
  | hmsg randomizer message call =>
    change messageDigestInput _ _ (f rootPos) _ _ = messageDigestInput _ _ (g rootPos) _ _
    rw [h rootPos (by simp [slotNeed])]
  | enc => rfl
  | prf => rfl
  | prfMsg => rfl
  | expand => rfl

/-! ## Honest inputs -/

namespace HonestTable

variable (L : HonestTable)

/-- The honest payload of a structural slot. -/
def payload : Slot → HashInput
  | .chain l τ e i step => littleEndianBytes 16 (L.chainValue l τ e i step.val)
  | .leaf l τ e => digestsPayload (L.endpoints l τ e)
  | .node l τ height index => nodePayload (L.treeValue l τ (height - 1) (2 * index))
      (L.treeValue l τ (height - 1) (2 * index + 1))
  | .forsLeaf idx κ s => littleEndianBytes 16 (L.forsSecret idx κ s)
  | .forsNode idx κ height node => nodePayload (L.forsValue idx κ (height - 1) (2 * node))
      (L.forsValue idx κ (height - 1) (2 * node + 1))
  | .forsRoots idx => digestsPayload (L.forsRoot idx)
  | _ => []

/-- The honest input of a structural slot of the table. -/
def structInput (s : Slot) : Option HashInput :=
  if InTable s then
    some (addressedHashInput L.publicSeed (hashDomainFields (slotDomain s)) (L.payload s))
  else none

/-- **The honest input of a slot**: a structural slot's (in the table); an `H_msg` call's at the
honest randomizer `R(M)`; a secret's; `PRF_msg`'s; the key expansion's two calls. An encoding slot
has many honest inputs (the counter trials) and gets none. -/
def honestInput (s : Slot) : Option HashInput :=
  match s with
  | .hmsg randomizer message call =>
      if randomizer = L.randomizer message then
        some (messageDigestInput randomizer L.publicSeed L.root message call)
      else none
  | .prf d => some (addressedHashInput L.publicSeed (keygenDomainFields d)
      (littleEndianBytes 32 L.secretSeed))
  | .prfMsg message => some (prfMessageInput L.prfKey L.publicSeed message)
  | .expand d => if d = 0 ∨ d = 1 then some (keyDerivationInput L.secretSeed d) else none
  | .enc .. => none
  | .chain .. | .leaf .. | .node .. | .forsLeaf .. | .forsNode .. | .forsRoots .. =>
      L.structInput s

/-- The Msponge tail of a slot's honest input. -/
def honestTail (s : Slot) : Option (List X) :=
  (L.honestInput s).map fun input ↦ absorbTail L.view (blocks input)

/-- **The target of a slot**: the digest of its honest input. -/
def target (s : Slot) : Option Digest :=
  (L.honestInput s).map fun input ↦ trunc128 (spongeHash L.view (blocks input))

theorem honestInput_of_inTable {s : Slot} (hs : InTable s) :
    L.honestInput s =
      some (addressedHashInput L.publicSeed (hashDomainFields (slotDomain s)) (L.payload s)) := by
  cases s <;> first
    | exact hs.elim
    | exact ite_eq_left (e := none) hs

/-- **The honest input of a structural slot is the slot's input at the table's values.** -/
theorem honestInput_eq_slotInput {s : Slot} (hs : InTable s) :
    L.honestInput s = some (slotInput L.publicSeed s (valuePos L)) := by
  rw [L.honestInput_of_inTable hs]
  refine congrArg some ?_
  cases s with
  | chain l τ e i step =>
    change _ = addressedHashInput _ _ (littleEndianBytes 16 (valuePos L _))
    rw [valuePos_cpos L l τ e i (j := step.val) (by have := step.isLt; omega)]
    rfl
  | leaf l τ e =>
    change _ = addressedHashInput _ _ (digestsPayload fun i ↦ valuePos L _)
    refine congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun i ↦ ?_))
    rw [valuePos_cpos L l τ e i (j := chainLength - 1) (by decide)]
    rfl
  | node l τ height index =>
    obtain ⟨-, h1, h2, h3⟩ := hs
    have hc := two_mul_add_one_lt h3 h1 h2
    have hl := layerHeight_le l
    have hp := two_pow_layerHeight_le l
    have ht : layerHeight topLayer = 10 := rfl
    change _ = addressedHashInput _ _ (nodePayload (valuePos L _) (valuePos L _))
    rw [valuePos_tpos L l τ (level := height - 1) (index := 2 * index) (by omega) (by omega),
      valuePos_tpos L l τ (level := height - 1) (index := 2 * index + 1) (by omega) (by omega)]
    rfl
  | forsLeaf idx κ s => rfl
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hc := two_mul_add_one_lt h3 h1 h2
    change _ = addressedHashInput _ _ (nodePayload (valuePos L _) (valuePos L _))
    rw [valuePos_fpos L idx κ (height := height - 1) (node := 2 * node) (by omega) (by omega),
      valuePos_fpos L idx κ (height := height - 1) (node := 2 * node + 1) (by omega) (by omega)]
    rfl
  | forsRoots idx =>
    change _ = addressedHashInput _ _ (digestsPayload fun κ ↦ valuePos L _)
    refine congrArg (addressedHashInput _ _) (congrArg digestsPayload (funext fun κ ↦ ?_))
    rw [valuePos_fpos L idx κ (height := forsTreeHeight) (node := 0) le_rfl (Nat.two_pow_pos _)]
    rfl
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **The honest input of an `H_msg` call at the honest randomizer is the slot's input at the
table's values.** -/
theorem honestInput_hmsg_eq_slotInput (message : Message) (call : DigestCall) :
    L.honestInput (.hmsg (L.randomizer message) message call) =
      some (slotInput L.publicSeed (.hmsg (L.randomizer message) message call) (valuePos L)) := by
  change (if L.randomizer message = L.randomizer message then _ else none) = _
  rw [ite_eq_left rfl]
  change _ = some (messageDigestInput _ _ (valuePos L rootPos) _ _)
  rw [valuePos_rootPos]

theorem trunc128_spongeHash (input : HashInput) :
    trunc128 (spongeHash L.view (blocks input)) = L.digest input :=
  rfl

/-- **The target of a structural slot is the value at its output.** -/
theorem target_eq_some {s : Slot} (hs : InTable s) :
    L.target s = some (valuePos L (slotOutPos s)) := by
  rw [target, L.honestInput_of_inTable hs, Option.map_some, trunc128_spongeHash]
  refine congrArg some ?_
  cases s with
  | chain l τ e i step =>
    change _ = valuePos L (cpos l τ e i (step.val + 1))
    rw [valuePos_cpos L l τ e i (j := step.val + 1) (by have := step.isLt; omega), chainValue_succ]
    rfl
  | leaf l τ e =>
    obtain ⟨-, he⟩ := hs
    change _ = valuePos L (tpos l τ 0 e.val)
    rw [valuePos_tpos L l τ (Nat.zero_le _) (lt_of_lt_of_le he (two_pow_layerHeight_le l)),
      treeValue_zero, leafOfNat_val]
    rfl
  | node l τ height index =>
    obtain ⟨-, h1, h2, h3⟩ := hs
    obtain ⟨k, rfl⟩ : ∃ k, height = k + 1 := ⟨height - 1, by omega⟩
    have hl := layerHeight_le l
    have hp := two_pow_layerHeight_le l
    have hi := lt_two_pow_of_lt h3
    have ht : layerHeight topLayer = 10 := rfl
    change _ = valuePos L (tpos l τ (k + 1) index)
    rw [valuePos_tpos L l τ (level := k + 1) (index := index) (by omega) (by omega), treeValue_succ]
    rfl
  | forsLeaf idx κ s =>
    change _ = valuePos L (fpos idx κ 0 s.val)
    rw [valuePos_fpos L idx κ (Nat.zero_le _) s.isLt, forsValue_zero, forsLeafOfNat_val]
    rfl
  | forsNode idx κ height node =>
    obtain ⟨h1, h2, h3⟩ := hs
    obtain ⟨k, rfl⟩ : ∃ k, height = k + 1 := ⟨height - 1, by omega⟩
    change _ = valuePos L (fpos idx κ (k + 1) node)
    rw [valuePos_fpos L idx κ h2 (lt_two_pow_of_lt h3), forsValue_succ]
    rfl
  | forsRoots idx => rfl
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **The target of a secret's slot is the secret**: a chain start or a FORS secret. -/
theorem target_prf (d : KeygenDomain) :
    L.target (.prf d) = some (valuePos L (slotOutPos (.prf d))) := by
  cases d with
  | oneTimeChain l τ e i =>
    change some (L.secret _) = some (valuePos L (cpos l τ e i 0))
    rw [valuePos_cpos L l τ e i (j := 0) (by decide)]
    rfl
  | forsSecret idx κ s => rfl

/-- **The honest tail lies in its slot.** -/
theorem slotOf_honestTail {s : Slot} {tail : List X} (h : L.honestTail s = some tail) :
    slotOf L.publicKey tail = some s := by
  rw [honestTail] at h
  cases s with
  | hmsg randomizer message call =>
    change Option.map _ (if randomizer = L.randomizer message then _ else none) = _ at h
    split_ifs at h with hr
    · obtain rfl := Option.some.inj h
      exact slotOf_messageDigestInput_self L.view L.publicKey randomizer message call
    · exact absurd h (by simp)
  | prf d =>
    obtain rfl := Option.some.inj h
    exact slotOf_prf L.view L.publicKey d L.secretSeed
  | prfMsg message =>
    obtain rfl := Option.some.inj h
    exact slotOf_prfMessageInput L.view L.publicKey L.prfKey L.publicSeed message
  | expand d =>
    change Option.map _ (if d = 0 ∨ d = 1 then _ else none) = _ at h
    split_ifs at h with hd
    · obtain rfl := Option.some.inj h
      exact slotOf_keyDerivationInput L.view L.publicKey L.secretSeed d
    · exact absurd h (by simp)
  | enc => exact absurd h (by simp [honestInput])
  | chain l τ e i step =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      exact slotOf_chain L.view L.publicKey l τ e i step _
    · exact absurd h (by simp)
  | leaf l τ e =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      exact slotOf_leaf L.view L.publicKey l τ e _
    · exact absurd h (by simp)
  | node l τ height index =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      obtain ⟨-, h1, h2, h3⟩ := hs
      have hl := layerHeight_le l
      have hi := lt_two_pow_of_lt h3
      have hp : 2 ^ layerHeight l ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact slotOf_node L.view L.publicKey l τ height index
        (lt_of_le_of_lt (h2.trans hl) (by norm_num)) (lt_of_lt_of_le hi hp) _ _
    · exact absurd h (by simp)
  | forsLeaf idx κ s =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      exact slotOf_forsLeaf L.view L.publicKey idx κ s _
    · exact absurd h (by simp)
  | forsNode idx κ height node =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      obtain ⟨h1, h2, h3⟩ := hs
      exact slotOf_forsNode L.view L.publicKey idx κ height node (by omega) h2 h3 _ _
    · exact absurd h (by simp)
  | forsRoots idx =>
    change Option.map _ (L.structInput _) = _ at h
    rw [structInput] at h
    split_ifs at h with hs
    · obtain rfl := Option.some.inj h
      exact slotOf_forsRoots L.view L.publicKey idx _
    · exact absurd h (by simp)

/-- Distinct slots have distinct honest tails. -/
theorem honestTail_injective {s s' : Slot} {tail : List X} (h : L.honestTail s = some tail)
    (h' : L.honestTail s' = some tail) : s = s' :=
  Option.some.inj ((L.slotOf_honestTail h).symm.trans (L.slotOf_honestTail h'))

end HonestTable

/-! ## The one value each key signs -/

/-- A WOTS+C key `K = (l, τ, e)`: layer, tree, leaf. -/
abbrev Key : Type :=
  Layer × TreeIndex × TreeLeafIndex

/-- The key `K_l(idx)`. -/
def keyOf (l : Layer) (idx : Index) : Key :=
  (l, treeOfIndex l idx, leafOfIndex l idx)

/-- The layer below a layer above the bottom (the bottom itself for the bottom). -/
def layerBelow (l : Layer) : Layer :=
  ⟨l.val - 1, by have := l.isLt; omega⟩

/-- The tree or FORS instance below the key `(l, τ, e)`: `τ 2^(h_l) + e`. -/
def indexBelow (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) : Index :=
  ⟨(τ.val * 2 ^ layerHeight l + e.val) % 2 ^ indexBits, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- **The position of the value a key signs**: the FORS key of instance `τ 2^8 + e` at the bottom,
the root of tree `τ 2^(h_l) + e` of the layer below above it. -/
def msgPos : Key → ValPos
  | (l, τ, e) =>
    if l.val = 0 then .forsKey (indexBelow l τ e)
    else tpos (layerBelow l) (indexBelow l τ e) (layerHeight (layerBelow l)) 0

/-- **Each key signs one fixed value**: in every signature of index `idx`, the key `K_l(idx)` signs
the value at `msgPos (keyOf l idx)`, whatever the message. -/
theorem msgPos_eq (L : HonestTable) (l : Layer) (idx : Index) :
    valuePos L (msgPos (keyOf l idx)) = L.layerMessage idx l := by
  have hi : idx.val < 67108864 := idx.isLt
  fin_cases l
  · change L.forsKey (indexBelow 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx)) = L.forsKey idx
    refine congrArg L.forsKey (Fin.ext ?_)
    change ((treeOfIndex 0 idx).val * 2 ^ 8 + (leafOfIndex 0 idx).val) % 2 ^ 26 = idx.val
    rw [treeOfIndex_zero, leafOfIndex_zero]
    change (idx.val / 256 * 256 + idx.val % 256) % 67108864 = idx.val
    omega
  · change valuePos L (tpos 0 (indexBelow 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx)) 8 0) =
      L.treeValue 0 (treeOfIndex 0 idx) 8 0
    rw [valuePos_tpos L 0 _ (level := 8) (index := 0) (by decide) (Nat.two_pow_pos _)]
    refine congrArg (fun τ ↦ L.treeValue 0 τ 8 0) (Fin.ext ?_)
    change (idx.val / 65536 * 256 + idx.val / 256 % 256) % 67108864 = idx.val / 256
    omega
  · change valuePos L (tpos 1 (indexBelow 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx)) 8 0) =
      L.treeValue 1 (treeOfIndex 1 idx) 8 0
    rw [valuePos_tpos L 1 _ (level := 8) (index := 0) (by decide) (Nat.two_pow_pos _)]
    refine congrArg (fun τ ↦ L.treeValue 1 τ 8 0) (Fin.ext ?_)
    change (idx.val / 67108864 * 1024 + idx.val / 65536 % 1024) % 67108864 = idx.val / 65536
    omega

namespace HonestTable

/-- **The counter search of `K_l(idx)` runs on the value at `msgPos`**, in every signature of index
`idx`. -/
theorem layerSig_eq (L : HonestTable) (idx : Index) (l : Layer) :
    L.layerSig idx l = L.layerSignature l (treeOfIndex l idx) (leafOfIndex l idx)
      (valuePos L (msgPos (keyOf l idx))) := by
  rw [msgPos_eq]
  rfl

end HonestTable

/-! ## Computable positions and disclosures -/

/-- The positions of a structural slot's payload all satisfy `K`. -/
def PayloadIn (K : ValPos → Prop) : Slot → Prop
  | .chain l τ e i step => K (cpos l τ e i step.val)
  | .leaf l τ e => ∀ i, K (cpos l τ e i (chainLength - 1))
  | .node l τ height index =>
      K (tpos l τ (height - 1) (2 * index)) ∧ K (tpos l τ (height - 1) (2 * index + 1))
  | .forsLeaf idx κ s => K (.forsSecret idx κ s)
  | .forsNode idx κ height node =>
      K (fpos idx κ (height - 1) (2 * node)) ∧ K (fpos idx κ (height - 1) (2 * node + 1))
  | .forsRoots idx => ∀ κ, K (fpos idx κ forsTreeHeight 0)
  | _ => False

theorem PayloadIn.mono {K K' : ValPos → Prop} (h : ∀ p, K p → K' p) {s : Slot}
    (hs : PayloadIn K s) : PayloadIn K' s := by
  cases s with
  | chain => exact h _ hs
  | leaf => exact fun i ↦ h _ (hs i)
  | node => exact ⟨h _ hs.1, h _ hs.2⟩
  | forsLeaf => exact h _ hs
  | forsNode => exact ⟨h _ hs.1, h _ hs.2⟩
  | forsRoots => exact fun κ ↦ h _ (hs κ)
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **The positions computable from the disclosed positions `D`**: the least set containing `D`
and the output of every structural slot whose payload it contains (`known_iff`,
`known_subset`). -/
inductive Known (D : Set ValPos) : ValPos → Prop
  /-- A disclosed position. -/
  | disclosed (p : ValPos) : p ∈ D → Known D p
  /-- A chain step's output. -/
  | chain (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) (step : ChainStep) :
      InTable (.chain l τ e i step) → Known D (cpos l τ e i step.val) →
        Known D (cpos l τ e i (step.val + 1))
  /-- A one-time leaf, from the chain ends. -/
  | leaf (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) : InTable (.leaf l τ e) →
      (∀ i, Known D (cpos l τ e i (chainLength - 1))) → Known D (tpos l τ 0 e.val)
  /-- A node, from its children. -/
  | node (l : Layer) (τ : TreeIndex) (height index : ℕ) : InTable (.node l τ height index) →
      Known D (tpos l τ (height - 1) (2 * index)) →
        Known D (tpos l τ (height - 1) (2 * index + 1)) → Known D (tpos l τ height index)
  /-- A FORS leaf, from its secret. -/
  | forsLeaf (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
      Known D (.forsSecret idx κ s) → Known D (fpos idx κ 0 s.val)
  /-- A FORS node, from its children. -/
  | forsNode (idx : Index) (κ : ForsTreeIndex) (height node : ℕ) :
      InTable (.forsNode idx κ height node) → Known D (fpos idx κ (height - 1) (2 * node)) →
        Known D (fpos idx κ (height - 1) (2 * node + 1)) → Known D (fpos idx κ height node)
  /-- A FORS key, from the roots. -/
  | forsRoots (idx : Index) : (∀ κ, Known D (fpos idx κ forsTreeHeight 0)) →
      Known D (.forsKey idx)

/-- **The fixed point**: a position is computable when it is disclosed or the output of a
structural slot whose payload is computable. -/
theorem known_iff {D : Set ValPos} {p : ValPos} :
    Known D p ↔ p ∈ D ∨ ∃ s, InTable s ∧ slotOutPos s = p ∧ PayloadIn (Known D) s := by
  constructor
  · intro h
    cases h with
    | disclosed p hp => exact Or.inl hp
    | chain l τ e i step hs h => exact Or.inr ⟨.chain l τ e i step, hs, rfl, h⟩
    | leaf l τ e hs h => exact Or.inr ⟨.leaf l τ e, hs, rfl, h⟩
    | node l τ height index hs h1 h2 => exact Or.inr ⟨.node l τ height index, hs, rfl, h1, h2⟩
    | forsLeaf idx κ s h => exact Or.inr ⟨.forsLeaf idx κ s, trivial, rfl, h⟩
    | forsNode idx κ height node hs h1 h2 =>
      exact Or.inr ⟨.forsNode idx κ height node, hs, rfl, h1, h2⟩
    | forsRoots idx h => exact Or.inr ⟨.forsRoots idx, trivial, rfl, h⟩
  · rintro (h | ⟨s, hs, rfl, hk⟩)
    · exact .disclosed p h
    · cases s with
      | chain l τ e i step => exact .chain l τ e i step hs hk
      | leaf l τ e => exact .leaf l τ e hs hk
      | node l τ height index => exact .node l τ height index hs hk.1 hk.2
      | forsLeaf idx κ s => exact .forsLeaf idx κ s hk
      | forsNode idx κ height node => exact .forsNode idx κ height node hs hk.1 hk.2
      | forsRoots idx => exact .forsRoots idx hk
      | enc => exact hs.elim
      | prf => exact hs.elim
      | hmsg => exact hs.elim
      | prfMsg => exact hs.elim
      | expand => exact hs.elim

/-- **Least**: every set containing `D` and closed under the outputs of structural slots whose
payload it contains contains the computable positions. -/
theorem known_subset {D K : Set ValPos} (hD : D ⊆ K)
    (hK : ∀ s, InTable s → PayloadIn (· ∈ K) s → slotOutPos s ∈ K) {p : ValPos}
    (h : Known D p) : p ∈ K := by
  induction h with
  | disclosed p hp => exact hD hp
  | chain l τ e i step hs _ ih => exact hK (.chain l τ e i step) hs ih
  | leaf l τ e hs _ ih => exact hK (.leaf l τ e) hs ih
  | node l τ height index hs _ _ ih1 ih2 => exact hK (.node l τ height index) hs ⟨ih1, ih2⟩
  | forsLeaf idx κ s _ ih => exact hK (.forsLeaf idx κ s) trivial ih
  | forsNode idx κ height node hs _ _ ih1 ih2 =>
    exact hK (.forsNode idx κ height node) hs ⟨ih1, ih2⟩
  | forsRoots idx _ ih => exact hK (.forsRoots idx) trivial ih

theorem known_mono {D D' : Set ValPos} (h : D ⊆ D') {p : ValPos} (hp : Known D p) : Known D' p :=
  known_subset (K := {p | Known D' p}) (fun _ hq ↦ .disclosed _ (h hq))
    (fun _ hs hk ↦ known_iff.2 (Or.inr ⟨_, hs, rfl, hk⟩)) hp

/-- **The public slots**: the structural slots of the table whose payload is computable from the
disclosed positions `D`. -/
def Public (D : Set ValPos) : Set Slot :=
  {s | InTable s ∧ PayloadIn (Known D) s}

theorem public_mono {D D' : Set ValPos} (h : D ⊆ D') : Public D ⊆ Public D' :=
  fun _ hs ↦ ⟨hs.1, hs.2.mono fun _ ↦ known_mono h⟩

/-- The positions a FORS opening of instance `idx` at the leaves `lv` discloses: the secrets at the
leaves and their paths. -/
def forsDisclosed (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) : Set ValPos :=
  {p | ∃ κ, p = .forsSecret idx κ (lv κ) ∨
    ∃ z : Fin forsTreeHeight, p = fpos idx κ z.val (((lv κ).val >>> z.val) ^^^ 1)}

/-- The positions the signature of layer `l` by key `(τ, e)` with codeword `x` discloses: the opened
chain positions and the path. -/
def layerDisclosed (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (x : Encoding) : Set ValPos :=
  {p | (∃ i, p = cpos l τ e i (x i).val) ∨
    ∃ z : Fin (layerHeight l), p = tpos l τ z.val ((e.val >>> z.val) ^^^ 1)}

namespace HonestTable

variable (L : HonestTable)

/-- The selection of `K_l(idx)` on the value it signs. -/
def layerSelect (idx : Index) (l : Layer) : Option (EncodingCounter × Encoding) :=
  L.select l (treeOfIndex l idx) (leafOfIndex l idx) (L.layerMessage idx l)

/-- **The positions the signature of `M` discloses**: the FORS secrets at the digest's leaves and
their paths, and each layer's opened chain positions and path, when the signer returns a signature;
none otherwise. -/
def disclosedBy (message : Message) : Set ValPos :=
  match L.layerSelect (L.index message) 0, L.layerSelect (L.index message) 1,
    L.layerSelect (L.index message) 2 with
  | some s0, some s1, some s2 =>
      forsDisclosed (L.index message) (L.leaves message) ∪
        layerDisclosed 0 (treeOfIndex 0 (L.index message)) (leafOfIndex 0 (L.index message)) s0.2 ∪
        layerDisclosed 1 (treeOfIndex 1 (L.index message)) (leafOfIndex 1 (L.index message)) s1.2 ∪
        layerDisclosed 2 (treeOfIndex 2 (L.index message)) (leafOfIndex 2 (L.index message)) s2.2
  | _, _, _ => ∅

/-- The positions disclosed after the messages `msgs`: the public key's root and each message's
signature. -/
def disclosures (msgs : List Message) : Set ValPos :=
  {rootPos} ∪ ⋃ message ∈ msgs, L.disclosedBy message

theorem disclosures_mono {msgs msgs' : List Message} (h : msgs ⊆ msgs') :
    L.disclosures msgs ⊆ L.disclosures msgs' :=
  Set.union_subset_union_right _ (Set.biUnion_subset_biUnion_left fun _ hr ↦ h hr)

theorem layerSelect_eq (idx : Index) (l : Layer) :
    L.layerSelect idx l = L.select l (treeOfIndex l idx) (leafOfIndex l idx)
      (valuePos L (msgPos (keyOf l idx))) := by
  rw [msgPos_eq]
  rfl

/-- A signature is returned exactly when the message discloses positions. -/
theorem signature_isSome_iff (message : Message) :
    (L.signature message).isSome ↔ L.disclosedBy message ≠ ∅ := by
  simp only [signature, disclosedBy, layerSig, layerSelect, layerSignature]
  cases L.select 0 (treeOfIndex 0 (L.index message)) (leafOfIndex 0 (L.index message))
      (L.layerMessage (L.index message) 0) with
  | none => simp
  | some s0 =>
    cases L.select 1 (treeOfIndex 1 (L.index message)) (leafOfIndex 1 (L.index message))
        (L.layerMessage (L.index message) 1) with
    | none => simp
    | some s1 =>
      cases L.select 2 (treeOfIndex 2 (L.index message)) (leafOfIndex 2 (L.index message))
          (L.layerMessage (L.index message) 2) with
      | none => simp
      | some s2 =>
        simp only [Option.map_some, Option.isSome_some, ne_eq, true_iff]
        exact Set.Nonempty.ne_empty ⟨_, Or.inl (Or.inl (Or.inl ⟨⟨0, by decide⟩, Or.inl rfl⟩))⟩

/-- A layer signature's values are the values at the positions it discloses. -/
theorem layerSig_eq_some {idx : Index} {l : Layer} {sigL : LayerSignature l}
    (h : L.layerSig idx l = some sigL) :
    ∃ sel, L.layerSelect idx l = some sel ∧ sigL.counter = sel.1 ∧
      (∀ i, sigL.chainValues i =
        valuePos L (cpos l (treeOfIndex l idx) (leafOfIndex l idx) i (sel.2 i).val)) ∧
      ∀ z : Fin (layerHeight l), sigL.authenticationPath z =
        valuePos L (tpos l (treeOfIndex l idx) z.val
          (((leafOfIndex l idx).val >>> z.val) ^^^ 1)) := by
  rw [layerSig, layerSignature, Option.map_eq_some_iff] at h
  obtain ⟨sel, hsel, rfl⟩ := h
  refine ⟨sel, hsel, rfl, fun i ↦ (valuePos_cpos L _ _ _ i (sel.2 i).isLt).symm, fun z ↦ ?_⟩
  have hl := layerHeight_le l
  have ht : layerHeight topLayer = 10 := rfl
  have hz := z.isLt
  have hb := shiftRight_xor_lt (leafOfIndex_lt l idx) z.isLt
  rw [valuePos_tpos L _ _ (level := z.val) (by omega)
    (lt_of_lt_of_le (lt_two_pow_of_lt hb) (two_pow_layerHeight_le l))]
  rfl

/-- **A signature's values are the values at the disclosed positions**: the FORS secrets and
paths, and each layer's opened chain values and path. -/
theorem signature_eq_some {message : Message} {sig : Signature}
    (h : L.signature message = some sig) :
    sig.randomizer = L.randomizer message ∧
    (∀ κ, (sig.forsOpening κ).secret =
        valuePos L (.forsSecret (L.index message) κ (L.leaves message κ)) ∧
      ∀ z : Fin forsTreeHeight, (sig.forsOpening κ).path z = valuePos L
        (fpos (L.index message) κ z.val (((L.leaves message κ).val >>> z.val) ^^^ 1))) ∧
    ∀ l, ∃ sel, L.layerSelect (L.index message) l = some sel ∧
      (sig.layers l).counter = sel.1 ∧
      (∀ i, (sig.layers l).chainValues i =
        valuePos L (cpos l (treeOfIndex l (L.index message)) (leafOfIndex l (L.index message)) i
          (sel.2 i).val)) ∧
      ∀ z : Fin (layerHeight l), (sig.layers l).authenticationPath z =
        valuePos L (tpos l (treeOfIndex l (L.index message)) z.val
          (((leafOfIndex l (L.index message)).val >>> z.val) ^^^ 1)) := by
  unfold signature at h
  cases h0 : L.layerSig (L.index message) 0 with
  | none => rw [h0] at h; simp at h
  | some bottom =>
    cases h1 : L.layerSig (L.index message) 1 with
    | none => rw [h0, h1] at h; simp at h
    | some middle =>
      cases h2 : L.layerSig (L.index message) 2 with
      | none => rw [h0, h1, h2] at h; simp at h
      | some top =>
        rw [h0, h1, h2] at h
        obtain rfl := Option.some.inj h
        refine ⟨rfl, fun κ ↦ ⟨rfl, fun z ↦ ?_⟩, fun l ↦ ?_⟩
        · have hb := shiftRight_xor_lt (L.leaves message κ).isLt z.isLt
          rw [valuePos_fpos L _ κ z.isLt.le (lt_two_pow_of_lt hb)]
          rfl
        · fin_cases l
          · exact L.layerSig_eq_some h0
          · exact L.layerSig_eq_some h1
          · exact L.layerSig_eq_some h2

end HonestTable

end Quantum.Sphincs

end
