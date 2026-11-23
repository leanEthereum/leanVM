module

public import Quantum.Qrom.TableLaw
public import Quantum.Qrom.Xmss.Slots
public import Quantum.Xmss.HonestTable

@[expose] public section

/-!
# leanXMSS's honest table in the random-oracle model

Every hash call of leanXMSS's key generation, and every hash call of the signer except the
randomizer trials' message digests, has an input fixed by the master seed `S_0` and the outputs of
earlier calls. These calls are the positions `Pos` of a lazy table (`Quantum.Qrom.LazyTable`); the
honest values are a table `v : QTable = Pos → HashOutput`.

* `Pos`: the scheme seed `S`, the public parameter `P`, the chain-start derivations, the chain
  steps, the leaves, the nodes (full trees of `2^32` leaves on both layers) and the randomizer bases
  `R0` of every key and message. `Pos.slot`: the slot (`Quantum.Xmss.Slot`) of its hash call.
* `QTable.seed`, `QTable.param`, `QTable.chainValue`, `QTable.treeValue`, `QTable.publicKey`,
  `QTable.select`, `QTable.signature`: the honest values read from a table (the selection reads
  the message digests from the hash `H`).
* `cellOf S0 p v`: the input hashed at `p` (`cell` of its slot with its payload, a function of the
  values at earlier positions); `table S0`: the `LazyTable Pos HashDomain HashOutput` (`dep` by
  rank, `inj` from `cell_injective`). `Consistent S0 v H`: `H` holds the values at their cells,
  exactly when `v` is the table of `H` (`consistent_iff`).
* `honestEval H x`: a computation answered by `H`, its result and the hashed cells in order.
  `eval_generateKeys`, `eval_sign`: against a consistent `H`, key generation returns
  `(v.publicKey, v.secretKey S0)` and the signer returns `v.signature H req`;
  `cellReads_generateKeys`, `signReads_sign`: key generation hashes cells of the table only, the
  signer cells of the table and message-digest cells; `simulateQ_generateKeys`, `simulateQ_sign`:
  any implementation answering `H` purely returns them. `IsHash`: a query of `H`, not a coin.
* `QTable.honCell S0 v s`: the honest cell and truncated value of a chain step, leaf or node slot
  of the table (`slotOf_honCell`: the cell lies in its slot).
* `Pos.out`, `QTable.value`: the symbolic position (`Quantum.Xmss.Pos`) of a structural position's
  value and the values at symbolic positions; `disclosedBy`, `disclosures`: the symbolic positions a
  signature, and the public key with the signatures, disclose (`Quantum.Xmss.layerDisclosed`), for
  the symbolic `Known` and `Public`.
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot leafKey leafKey_val layerDisclosed evalWithAnswerFn_sequenceFin
  inputBit_littleEndianBytes)
open Quantum.SufCma (QueriesSatisfy queries trace trace_query_bind queriesSatisfy_pure
  queriesSatisfy_bind queriesSatisfy_sequenceFin)

namespace Quantum.Qrom.Xmss

/-! ## Positions -/

/-- **A position of the honest table**: a hash call of key generation or signing whose input is
fixed by `S_0` and the outputs of earlier calls. Every key of both layers has its chain-start
derivations, chain steps and leaf; both layers have full trees over `2^32` leaves (node `index` at
tree level `level + 1`); every key has a randomizer base for each message it may sign (a message
on the bottom layer, a bottom root on the top layer). -/
inductive Pos where
  /-- The scheme seed `S = H("leanXMSS" ‖ S_0)`. -/
  | seed
  /-- The public parameter's derivation. -/
  | param
  /-- The derivation of the starts of chains `2 pair`, `2 pair + 1` of key `key`. -/
  | prf (layer : Layer) (key : KeyIndex) (pair : ChainPairIndex)
  /-- Step `step` of chain `chain` of key `key`. -/
  | chain (layer : Layer) (key : KeyIndex) (chain : ChainIndex) (step : ChainStep)
  /-- The leaf of key `key`. -/
  | leaf (layer : Layer) (key : KeyIndex)
  /-- The node `index` at tree level `level + 1`. -/
  | node (layer : Layer) (level : Fin layerHeight) (index : Fin (2 ^ (31 - level.val)))
  /-- The randomizer base of bottom key `key` for `message`. -/
  | rndBottom (key : KeyIndex) (message : Message)
  /-- The randomizer base of top key `key` for the bottom root `root`. -/
  | rndTop (key : KeyIndex) (root : Digest)
  deriving DecidableEq, Fintype

/-- The slot of a position's hash call. -/
def Pos.slot : Pos → Slot
  | .seed => .seed
  | .param => .param
  | .prf l e t => .prf l e t
  | .chain l e i step => .chain l e step i
  | .leaf l e => .leaf l e
  | .node l k x => .node l (k.val + 1) x.val
  | .rndBottom e _ => .rnd bottomLayer e
  | .rndTop e _ => .rnd topLayer e

/-- The order of the honest computation: a position's input reads values of lower rank only. -/
def Pos.rank : Pos → ℕ
  | .seed => 0
  | .param => 1
  | .prf .. | .rndBottom .. | .rndTop .. => 2
  | .chain _ _ _ step => 3 + step.val
  | .leaf .. => 2 + chainLength
  | .node _ k _ => 3 + chainLength + k.val

theorem addressable_slot : ∀ p : Pos, Addressable p.slot
  | .node _ k x => ⟨by have := k.isLt; simp only [layerHeight] at this; omega,
      lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  | .seed | .param | .prf .. | .chain .. | .leaf .. | .rndBottom .. | .rndTop .. => trivial

/-- A message's bytes, as a digested message. -/
def messageBytes (message : Message) : MsgBytes :=
  ⟨littleEndianBytes 32 message, length_messageBytes_le message⟩

/-- A bottom root's bytes, as a digested message. -/
def rootBytes (root : Digest) : MsgBytes :=
  ⟨littleEndianBytes 16 root, length_digestBytes_le root⟩

/-! ## The honest values of a table -/

/-- **The honest table's values**: one hash output per position. -/
abbrev QTable := Pos → HashOutput

namespace QTable

variable (v : QTable)

/-- The scheme seed `S`. -/
def seed : MasterSeed :=
  v .seed

/-- The public parameter `P`. -/
def param : PublicParameter :=
  truncateHash (v .param)

/-- The start of chain `i` of key `e` of layer `l`: a half of a seed derivation. -/
def chainStart (l : Layer) (e : KeyIndex) (i : ChainIndex) : Digest :=
  hashHalfForChain i.val (v (.prf l e (chainPair i)))

/-- Position `j` of chain `i` of key `e` of layer `l` (`0` past the end, as `walkChain`). -/
def chainValue (l : Layer) (e : KeyIndex) (i : ChainIndex) : ℕ → Digest
  | 0 => v.chainStart l e i
  | j + 1 => if h : j < chainLength - 1 then truncateHash (v (.chain l e i ⟨j, h⟩)) else 0

/-- The chain ends of key `e` of layer `l`. -/
def endpoints (l : Layer) (e : KeyIndex) (i : ChainIndex) : Digest :=
  v.chainValue l e i (chainLength - 1)

/-- The tree value of layer `l` at `level`, index `index`: the leaf of key `leafKey index` at
level `0`, else the node (`0` outside the trees). -/
def treeValue (l : Layer) : ℕ → ℕ → Digest
  | 0, index => truncateHash (v (.leaf l (leafKey index)))
  | level + 1, index => if h : level < layerHeight ∧ index < 2 ^ (31 - level) then
      truncateHash (v (.node l ⟨level, h.1⟩ ⟨index, h.2⟩)) else 0

/-- The public key: the top root and `P`. -/
def publicKey : PublicKey :=
  ⟨v.treeValue topLayer layerHeight 0, v.param⟩

/-- The secret key: `S_0` and `P`. -/
def secretKey (S0 : MasterSeed) : SecretKey :=
  ⟨S0, v.param⟩

/-- The authentication path of key `e` of layer `l`. -/
def authPath (l : Layer) (e : KeyIndex) (level : Fin layerHeight) : Digest :=
  v.treeValue l level.val (Nat.xor (e.val / 2 ^ level.val) 1)

/-- The root of the bottom tree of a leaf index. -/
def bottomRoot (index : LeafIndex) : Digest :=
  v.treeValue bottomLayer layerHeight (keyIndexOnLayer index topLayer).val

variable (H : HashDomain → HashOutput)

/-- The message digest of key `e` of layer `l` for `message` and a randomizer, read from `H`. -/
def messageDigest (l : Layer) (e : KeyIndex) (message : MsgBytes) (randomizer : Randomizer) :
    Digest :=
  truncateHash (H (cell v.param (.msg l e) (message, randomizer)))

/-- The randomizer trials from `trial`, `attempts` of them: the first codeword's randomizer and
word. -/
def selectFrom (l : Layer) (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ℕ → ℕ → Option (Randomizer × Encoding)
  | 0, _ => none
  | attempts + 1, trial =>
    match Codeword.decode (v.messageDigest H l e message (base + BitVec.ofNat digestBits trial))
    with
    | some x => some (base + BitVec.ofNat digestBits trial, x)
    | none => selectFrom l e message base attempts (trial + 1)

/-- **The selection** of key `e` of layer `l` for `message` from the randomizer base `base`: the
first of the `2^32` trials whose digest is a codeword, its randomizer and word. -/
def select (l : Layer) (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    Option (Randomizer × Encoding) :=
  v.selectFrom H l e message base randomizerAttemptLimit 0

/-- The signature of key `e` of layer `l` on `message` from the randomizer base `base`: the
selection, the chains opened to its word, and the path. -/
def layerSignature (l : Layer) (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    Option LayerSignature :=
  (v.select H l e message base).map fun sel ↦
    ⟨sel.1, fun i ↦ v.chainValue l e i (sel.2 i).val, v.authPath l e⟩

/-- The randomizer base of the bottom key of a request. -/
def bottomBase (req : SigningRequest) : Randomizer :=
  truncateHash (v (.rndBottom (keyIndexOnLayer req.leafIndex bottomLayer) req.message))

/-- The randomizer base of the top key of a request. -/
def topBase (req : SigningRequest) : Randomizer :=
  truncateHash (v (.rndTop (keyIndexOnLayer req.leafIndex topLayer) (v.bottomRoot req.leafIndex)))

/-- The bottom layer's signature of a request. -/
def bottomSignature (req : SigningRequest) : Option LayerSignature :=
  v.layerSignature H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
    (messageBytes req.message) (v.bottomBase req)

/-- The top layer's signature of a request. -/
def topSignature (req : SigningRequest) : Option LayerSignature :=
  v.layerSignature H topLayer (keyIndexOnLayer req.leafIndex topLayer)
    (rootBytes (v.bottomRoot req.leafIndex)) (v.topBase req)

/-- **The honest signature** of a request. -/
def signature (req : SigningRequest) : Option Signature :=
  (v.bottomSignature H req).bind fun bottom ↦
    (v.topSignature H req).map fun top ↦
      ⟨req.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩

end QTable

/-! ## The cells and the lazy table -/

/-- The payload of a position's hash call, from `S_0` and the values. -/
def payload (S0 : MasterSeed) (v : QTable) : (p : Pos) → Payload p.slot
  | .seed => S0
  | .param => v.seed
  | .prf .. => v.seed
  | .chain l e i step => v.chainValue l e i step.val
  | .leaf l e => v.endpoints l e
  | .node l k x => (v.treeValue l k.val (2 * x.val), v.treeValue l k.val (2 * x.val + 1))
  | .rndBottom _ m => (v.seed, messageBytes m)
  | .rndTop _ d => (v.seed, rootBytes d)

/-- **The cell of a position**: the input hashed at `p`, given `S_0` and the values. -/
def cellOf (S0 : MasterSeed) (p : Pos) (v : QTable) : HashDomain :=
  cell v.param p.slot (payload S0 v p)

theorem cell_seed_eq (P P' : PublicParameter) (d : Payload .seed) :
    cell P .seed d = cell P' .seed d :=
  rfl

theorem cell_param_eq (P P' : PublicParameter) (d : Payload .param) :
    cell P .param d = cell P' .param d :=
  rfl

namespace QTable

variable {v v' : QTable}

theorem chainValue_congr {l : Layer} {e : KeyIndex} {i : ChainIndex} {j : ℕ}
    (h : ∀ q : Pos, q.rank < 3 + j → v q = v' q) :
    v.chainValue l e i j = v'.chainValue l e i j := by
  cases j with
  | zero => exact congrArg (hashHalfForChain i.val) (h _ (by simp [Pos.rank]))
  | succ j =>
    simp only [chainValue]
    split_ifs with hj
    · exact congrArg truncateHash (h _ (by simp [Pos.rank]))
    · rfl

theorem treeValue_congr {l : Layer} {level index : ℕ}
    (h : ∀ q : Pos, q.rank < 3 + chainLength + level → v q = v' q) :
    v.treeValue l level index = v'.treeValue l level index := by
  cases level with
  | zero => exact congrArg truncateHash (h _ (by simp [Pos.rank]))
  | succ level =>
    simp only [treeValue]
    split_ifs with hl
    · exact congrArg truncateHash (h _ (by simp [Pos.rank]))
    · rfl

end QTable

theorem one_le_chainLength : 1 ≤ chainLength :=
  Nat.one_le_two_pow

/-- A cell reads only the values of lower rank. -/
theorem cellOf_congr (S0 : MasterSeed) {p : Pos} {v v' : QTable}
    (h : ∀ q : Pos, q.rank < p.rank → v q = v' q) : cellOf S0 p v = cellOf S0 p v' := by
  have hS : 0 < p.rank → v.seed = v'.seed := fun hp ↦ h .seed hp
  have hP : 1 < p.rank → v.param = v'.param := fun hp ↦ congrArg truncateHash (h .param hp)
  have key : v.param = v'.param → payload S0 v p = payload S0 v' p →
      cellOf S0 p v = cellOf S0 p v' := fun h1 h2 ↦ by
    unfold cellOf
    rw [h1, h2]
  have hc := one_le_chainLength
  cases p with
  | seed => exact cell_seed_eq _ _ _
  | param =>
    unfold cellOf
    rw [show payload S0 v .param = payload S0 v' .param from hS (by simp [Pos.rank])]
    exact cell_param_eq _ _ _
  | prf l e t => exact key (hP (by simp [Pos.rank])) (hS (by simp [Pos.rank]))
  | chain l e i step =>
    exact key (hP (by simp [Pos.rank]; omega)) (QTable.chainValue_congr h)
  | leaf l e =>
    refine key (hP (by simp [Pos.rank]; omega)) ?_
    show v.endpoints l e = v'.endpoints l e
    exact funext fun _ ↦ QTable.chainValue_congr (j := chainLength - 1) fun q hq ↦
      h q (show q.rank < 2 + chainLength by omega)
  | node l k x =>
    exact key (hP (by simp [Pos.rank]; omega))
      (Prod.ext (QTable.treeValue_congr h) (QTable.treeValue_congr h))
  | rndBottom e m =>
    exact key (hP (by simp [Pos.rank])) (Prod.ext (hS (by simp [Pos.rank])) rfl)
  | rndTop e d =>
    exact key (hP (by simp [Pos.rank])) (Prod.ext (hS (by simp [Pos.rank])) rfl)

/-- The position a slot and a payload name, if any: the inverse of `p ↦ (p.slot, payload)`. -/
def posOf : (s : Slot) → Payload s → Option Pos
  | .seed, _ => some .seed
  | .param, _ => some .param
  | .prf l e t, _ => some (.prf l e t)
  | .chain l e step i, _ => some (.chain l e i step)
  | .leaf l e, _ => some (.leaf l e)
  | .node _ 0 _, _ => none
  | .node l (k + 1) x, _ =>
      if h : k < layerHeight ∧ x < 2 ^ (31 - k) then some (.node l ⟨k, h.1⟩ ⟨x, h.2⟩) else none
  | .rnd ⟨0, _⟩ e, d => some (.rndBottom e (sliceBits d.2.1 0 256))
  | .rnd ⟨1, _⟩ e, d => some (.rndTop e (sliceBits d.2.1 0 128))
  | .rnd ⟨_ + 2, _⟩ _, _ => none
  | .msg .., _ => none

theorem sliceBits_littleEndianBytes {n : ℕ} (w : BitVec (8 * n)) :
    sliceBits (littleEndianBytes n w) 0 (8 * n) = w :=
  sliceBits_eq fun j _ ↦ by rw [zero_add, inputBit_littleEndianBytes]

theorem posOf_payload (S0 : MasterSeed) (v : QTable) :
    ∀ p : Pos, posOf p.slot (payload S0 v p) = some p
  | .node _ k x => dite_eq_left ⟨k.isLt, x.isLt⟩
  | .rndBottom e m => congrArg (fun w ↦ some (Pos.rndBottom e w))
      (sliceBits_littleEndianBytes (n := 32) m)
  | .rndTop e d => congrArg (fun w ↦ some (Pos.rndTop e w))
      (sliceBits_littleEndianBytes (n := 16) d)
  | .seed | .param | .prf .. | .chain .. | .leaf .. => rfl

/-- A position is determined by its slot and payload. -/
theorem eq_of_slot_payload {S0 : MasterSeed} {v : QTable} {p p' : Pos}
    (h : (⟨p.slot, payload S0 v p⟩ : Σ s, Payload s) = ⟨p'.slot, payload S0 v p'⟩) : p = p' :=
  Option.some.inj ((posOf_payload S0 v p).symm.trans
    ((congrArg (fun x : Σ s, Payload s ↦ posOf x.1 x.2) h).trans (posOf_payload S0 v p')))

/-- **The honest table of leanXMSS at the master seed `S_0`**: positions `Pos`, cells `cellOf S0`,
ordered by rank; distinct positions hash distinct inputs by `cell_injective`. -/
def table (S0 : MasterSeed) : LazyTable Pos HashDomain HashOutput where
  cell := cellOf S0
  pre p q := p.rank < q.rank
  wf := (measure Pos.rank).wf
  dep _ _ _ h := cellOf_congr S0 h
  inj v _ _ h := eq_of_slot_payload
    (cell_injective (QTable.param v) (addressable_slot _) (addressable_slot _) h)

/-- **`H` holds the table's values at their cells.** -/
def Consistent (S0 : MasterSeed) (v : QTable) (H : HashDomain → HashOutput) : Prop :=
  ∀ p, H (cellOf S0 p v) = v p

theorem consistent_iff {S0 : MasterSeed} {v : QTable} {H : HashDomain → HashOutput} :
    Consistent S0 v H ↔ (table S0).tab H = v :=
  ⟨fun h ↦ (table S0).tab_unique (H := H) (v := v) h, fun h p ↦ (table S0).tab_eq_iff.1 h p⟩

/-- Every function is consistent with its table. -/
theorem consistent_tab (S0 : MasterSeed) (H : HashDomain → HashOutput) :
    Consistent S0 ((table S0).tab H) H :=
  consistent_iff.2 rfl

/-- A function overwritten at the cells of `v` by `v` is consistent with `v`. -/
theorem consistent_fill (S0 : MasterSeed) (v : QTable) (H : HashDomain → HashOutput) :
    Consistent S0 v ((table S0).fill v v H) :=
  fun p ↦ (table S0).fill_cell v v H p

/-! ## The honest computations as cell reads -/

/-- The model's oracles answered by `H` (coins by `0`; leanXMSS's algorithms flip none). -/
def romAnswers (H : HashDomain → HashOutput) : QueryImpl RomOracles Id
  | .inl n => (0 : Fin (n + 1))
  | .inr x => H x

/-- The hashed input of a query of the model, if any. -/
def hashRead : RomOracles.Domain → List HashDomain
  | .inl _ => []
  | .inr x => [x]

/-- **The honest evaluation**: a computation answered by `H`, its result and the cells it
hashes, in order. -/
def honestEval {α : Type} (H : HashDomain → HashOutput) (x : OracleComp RomOracles α) :
    α × List HashDomain :=
  (evalWithAnswerFn (romAnswers H) x, trace (romAnswers H) hashRead x)

/-- A query hashes a cell of the table. -/
def TableRead (S0 : MasterSeed) (v : QTable) (t : RomOracles.Domain) : Prop :=
  ∃ p, t = .inr (cellOf S0 p v)

/-- A query hashes a cell of the table or a message digest's input. -/
def SignRead (S0 : MasterSeed) (v : QTable) (t : RomOracles.Domain) : Prop :=
  TableRead S0 v t ∨ ∃ l e d, t = .inr (cell v.param (.msg l e) d)

theorem queriesSatisfy_mono {α : Type} {f : QueryImpl RomOracles Id}
    {P P' : RomOracles.Domain → Prop} (hP : ∀ t, P t → P' t) {x : OracleComp RomOracles α}
    (hx : QueriesSatisfy f P x) : QueriesSatisfy f P' x :=
  fun t ht ↦ hP t (hx t ht)

theorem queriesSatisfy_liftM_query {f : QueryImpl RomOracles Id}
    {P : RomOracles.Domain → Prop} {t : RomOracles.Domain} (h : P t) :
    QueriesSatisfy f P (liftM (RomOracles.query t) : OracleComp RomOracles _) := by
  intro q hq
  have e := trace_query_bind f (fun t ↦ [t]) t pure
  rw [bind_pure] at e
  rw [queries, e, Quantum.SufCma.trace_pure, List.append_nil, List.mem_singleton] at hq
  exact hq ▸ h

theorem queriesSatisfy_hashQ_slotInput {f : QueryImpl RomOracles Id}
    {P : RomOracles.Domain → Prop} {Q : PublicParameter} {s : Slot} {d : Payload s}
    (h : P (.inr (cell Q s d))) : QueriesSatisfy f P (hashQ (slotInput Q s d)) := by
  rw [hashQ_slotInput]
  exact queriesSatisfy_liftM_query h

/-- A query of `H`. -/
def IsHash (t : RomOracles.Domain) : Prop :=
  ∃ x, t = .inr x

theorem not_isHash_inl (n : ℕ) : ¬IsHash (.inl n) :=
  fun ⟨_, h⟩ ↦ Sum.inl_ne_inr h

/-- Every input's hash is a query of `H` or none. -/
theorem isHash_hashQ {f : QueryImpl RomOracles Id} (l : HashInput) :
    QueriesSatisfy f IsHash (hashQ l) := by
  unfold hashQ
  split
  · exact queriesSatisfy_liftM_query ⟨_, rfl⟩
  · exact queriesSatisfy_pure _

/-- **A computation that hashes only** (every query satisfying a predicate that excludes coins),
run by any implementation answering `H` purely, returns its evaluation. -/
theorem simulateQ_eq_pure_of_queriesSatisfy {r : Type → Type} [Monad r] [LawfulMonad r]
    {impl : QueryImpl RomOracles r} {H : HashDomain → HashOutput}
    (himpl : ∀ x, impl (.inr x) = pure (H x)) {P : RomOracles.Domain → Prop}
    (hP : ∀ n, ¬P (.inl n)) {α : Type} (x : OracleComp RomOracles α)
    (hx : QueriesSatisfy (romAnswers H) P x) :
    simulateQ impl x = pure (evalWithAnswerFn (romAnswers H) x) := by
  induction x using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    have hq : queries (romAnswers H) ((liftM (RomOracles.query t) : OracleComp _ _) >>= k) =
        [t] ++ queries (romAnswers H) (k (romAnswers H t)) :=
      trace_query_bind _ _ t k
    have ht : P t := hx t (by rw [hq]; exact List.mem_append_left _ (List.mem_singleton_self t))
    have hk : QueriesSatisfy (romAnswers H) P (k (romAnswers H t)) :=
      fun q hq' ↦ hx q (by rw [hq]; exact List.mem_append_right _ hq')
    rcases t with n | y
    · exact absurd ht (hP n)
    · simp only [simulateQ_bind, simulateQ_spec_query, himpl, pure_bind]
      exact ih _ hk

local notation "ev" H => evalWithAnswerFn (romAnswers H)

theorem eval_hashQ_slotInput (H : HashDomain → HashOutput) (P : PublicParameter) (s : Slot)
    (d : Payload s) : (ev H) (hashQ (slotInput P s d)) = H (cell P s d) := by
  rw [hashQ_slotInput]
  rfl

theorem eval_th {H : HashDomain → HashOutput} {P : PublicParameter} {fields : TweakFields}
    {p : HashInput} {Q : PublicParameter} {s : Slot} {d : Payload s}
    (h : thInput P fields p = slotInput Q s d) :
    (ev H) (Over.th hashQ P fields p) = truncateHash (H (cell Q s d)) := by
  simp only [Over.th, evalWithAnswerFn_bind, h, eval_hashQ_slotInput, evalWithAnswerFn_pure]

theorem queriesSatisfy_th {f : QueryImpl RomOracles Id} {P' : RomOracles.Domain → Prop}
    {P : PublicParameter} {fields : TweakFields} {p : HashInput} {Q : PublicParameter} {s : Slot}
    {d : Payload s} (h : thInput P fields p = slotInput Q s d) (hP : P' (.inr (cell Q s d))) :
    QueriesSatisfy f P' (Over.th hashQ P fields p) := by
  rw [Over.th, h]
  exact queriesSatisfy_bind (queriesSatisfy_hashQ_slotInput hP) (queriesSatisfy_pure _)

namespace QTable

variable {S0 : MasterSeed} {v : QTable} {H : HashDomain → HashOutput} (hv : Consistent S0 v H)

include hv

theorem eval_schemeSeedOf : (ev H) (Over.schemeSeedOf hashQ S0) = v.seed :=
  (eval_hashQ_slotInput H v.param .seed S0).trans (hv .seed)

theorem eval_publicParameterOf : (ev H) (Over.publicParameterOf hashQ v.seed) = v.param :=
  (eval_th (Q := v.param) (s := .param) rfl).trans (congrArg truncateHash (hv .param))

theorem eval_chainWalk (l : Layer) (e : KeyIndex) (i : ChainIndex) : ∀ j,
    (ev H) (Over.chainWalk hashQ v.param l e i 0 j (v.chainStart l e i)) = v.chainValue l e i j
  | 0 => rfl
  | j + 1 => by
    have ih := eval_chainWalk l e i j
    rw [Over.chainWalk] at ih ⊢
    rw [walkChain, evalWithAnswerFn_bind, ih, chainValue]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (by omega), dite_eq_left h]
      simp only [Nat.zero_add]
      exact (eval_th (Q := v.param) (s := .chain l e ⟨j, h⟩ i) rfl).trans
        (congrArg truncateHash (hv (.chain l e i ⟨j, h⟩)))
    · rw [dite_eq_right (by omega), dite_eq_right h]
      rfl

theorem eval_otsSecrets (l : Layer) (e : KeyIndex) :
    (ev H) (Over.otsSecrets hashQ v.param l e v.seed) = v.chainStart l e := by
  simp only [Over.otsSecrets, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    Over.thPair, evalWithAnswerFn_pure]
  funext i
  exact congrArg (hashHalfForChain i.val)
    ((eval_hashQ_slotInput H v.param (.prf l e (chainPair i)) v.seed).trans (hv (.prf l e _)))

theorem eval_oneTimePublicKey (l : Layer) (e : KeyIndex) :
    (ev H) (Over.oneTimePublicKey hashQ v.param l e v.seed) = v.endpoints l e := by
  simp only [Over.oneTimePublicKey, evalWithAnswerFn_bind, eval_otsSecrets hv,
    evalWithAnswerFn_sequenceFin, eval_chainWalk hv]
  rfl

theorem eval_treeNode (l : Layer) : ∀ level index, level ≤ layerHeight →
    index < 2 ^ (32 - level) →
    (ev H) (Over.treeNode hashQ v.param l v.seed level index) = v.treeValue l level index
  | 0, index, _, _ => by
    simp only [Over.treeNode, buildTree, evalWithAnswerFn_bind, eval_oneTimePublicKey hv]
    exact (eval_th (Q := v.param) (s := .leaf l (leafKey index)) rfl).trans
      (congrArg truncateHash (hv (.leaf l (leafKey index))))
  | level + 1, index, hl, hi => by
    have hl' : level < layerHeight := by omega
    have hi' : index < 2 ^ (31 - level) := by
      rw [show 31 - level = 32 - (level + 1) by omega]
      exact hi
    have h2 : 2 ^ (32 - level) = 2 * 2 ^ (32 - (level + 1)) := by
      rw [← pow_succ']
      congr 1
      simp only [layerHeight] at hl
      omega
    have h1 := eval_treeNode l level (2 * index) (by omega) (by omega)
    have h3 := eval_treeNode l level (2 * index + 1) (by omega) (by omega)
    simp only [Over.treeNode] at h1 h3 ⊢
    simp only [buildTree, evalWithAnswerFn_bind, h1, h3]
    rw [treeValue, dite_eq_left ⟨hl', hi'⟩]
    exact (eval_th (Q := v.param) (s := .node l (level + 1) index)
      (d := (v.treeValue l level (2 * index), v.treeValue l level (2 * index + 1))) rfl).trans
      (congrArg truncateHash (hv (.node l ⟨level, hl'⟩ ⟨index, hi'⟩)))

omit hv in
theorem sibling_lt (e : KeyIndex) (level : Fin layerHeight) :
    Nat.xor (e.val / 2 ^ level.val) 1 < 2 ^ (32 - level.val) := by
  have hlv : level.val < 16 := level.isLt
  have he : e.val < 2 ^ 32 := e.isLt
  have h1 : e.val / 2 ^ level.val < 2 ^ (32 - level.val) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
    exact he
  exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))

theorem eval_treePath (l : Layer) (e : KeyIndex) :
    (ev H) (Over.treePath hashQ v.param l v.seed e) = v.authPath l e := by
  simp only [Over.treePath, evalWithAnswerFn_sequenceFin]
  funext level
  exact eval_treeNode hv l _ _ level.isLt.le (sibling_lt e level)

/-- **Key generation returns the table's keys.** -/
theorem eval_generateKeys :
    (ev H) (xmssRom.generateKeys S0) = (v.publicKey, v.secretKey S0) := by
  change (ev H) (Over.keygenFromSeed hashQ S0) = _
  simp only [Over.keygenFromSeed, evalWithAnswerFn_bind, eval_schemeSeedOf hv,
    eval_publicParameterOf hv, evalWithAnswerFn_pure,
    eval_treeNode hv topLayer layerHeight 0 le_rfl (by positivity)]
  rfl

theorem eval_otsSignFrom (l : Layer) (e : KeyIndex) (message : MsgBytes) (base : Randomizer) :
    ∀ attempts trial, (ev H)
      (Over.otsSignFrom hashQ v.param l e v.seed message.1 base attempts trial) =
      (v.selectFrom H l e message base attempts trial).map fun sel ↦
        (sel.1, fun i ↦ v.chainValue l e i (sel.2 i).val)
  | 0, _ => rfl
  | attempts + 1, trial => by
    rw [Over.otsSignFrom, evalWithAnswerFn_bind, Over.messageDigest,
      eval_th (Q := v.param) (s := .msg l e) (d := (message, base + BitVec.ofNat digestBits trial))
        rfl, selectFrom]
    change _ = Option.map _ (match Codeword.decode (v.messageDigest H l e message _) with
      | some x => _ | none => _)
    rw [messageDigest]
    cases Codeword.decode (truncateHash (H (cell v.param (.msg l e)
        (message, base + BitVec.ofNat digestBits trial)))) with
    | none => exact eval_otsSignFrom l e message base attempts (trial + 1)
    | some x =>
      simp only [evalWithAnswerFn_bind, eval_otsSecrets hv, evalWithAnswerFn_sequenceFin,
        eval_chainWalk hv, evalWithAnswerFn_pure, Option.map_some]

theorem eval_signLayer (l : Layer) (e : KeyIndex) (message : MsgBytes) :
    (ev H) (Over.signLayer hashQ v.seed v.param l e message.1) =
      v.layerSignature H l e message
        (truncateHash (H (cell v.param (.rnd l e) (v.seed, message)))) := by
  simp only [Over.signLayer, Over.otsSign, evalWithAnswerFn_bind,
    eval_th (Q := v.param) (s := .rnd l e) (d := (v.seed, message)) rfl]
  rw [eval_otsSignFrom hv, layerSignature, select]
  cases v.selectFrom H l e message (truncateHash (H (cell v.param (.rnd l e) (v.seed, message))))
      randomizerAttemptLimit 0 with
  | none => rfl
  | some sel =>
    simp only [Option.map_some, evalWithAnswerFn_bind, eval_treePath hv, evalWithAnswerFn_pure]

omit hv in
theorem keyIndexOnLayer_top_lt (index : LeafIndex) :
    (keyIndexOnLayer index topLayer).val < 2 ^ (32 - layerHeight) := by
  have h : index.val < 2 ^ 32 := index.isLt
  simp only [keyIndexOnLayer, topLayer, layerHeight]
  omega

/-- **Signing returns the table's signature.** -/
theorem eval_sign (req : SigningRequest) :
    (ev H) (xmssRom.sign (v.secretKey S0) req) = v.signature H req := by
  change (ev H) (Over.sign hashQ (v.secretKey S0) req.leafIndex req.message) = _
  simp only [Over.sign, evalWithAnswerFn_bind, secretKey, eval_schemeSeedOf hv,
    Over.signWithSchemeSeed]
  rw [show littleEndianBytes 32 req.message = (messageBytes req.message).1 from rfl,
    eval_signLayer hv]
  rw [show truncateHash (H (cell v.param (.rnd bottomLayer _) (v.seed, messageBytes req.message)))
    = v.bottomBase req from congrArg truncateHash (hv (.rndBottom _ req.message))]
  simp only [signature, bottomSignature]
  cases v.layerSignature H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (messageBytes req.message) (v.bottomBase req) with
  | none => rfl
  | some bottom =>
    simp only [Option.bind_some, evalWithAnswerFn_bind,
      eval_treeNode hv bottomLayer layerHeight _ le_rfl (keyIndexOnLayer_top_lt req.leafIndex)]
    rw [show v.treeValue bottomLayer layerHeight (keyIndexOnLayer req.leafIndex topLayer).val =
      v.bottomRoot req.leafIndex from rfl,
      show littleEndianBytes 16 (v.bottomRoot req.leafIndex) =
        (rootBytes (v.bottomRoot req.leafIndex)).1 from rfl, eval_signLayer hv]
    rw [show truncateHash (H (cell v.param (.rnd topLayer _)
        (v.seed, rootBytes (v.bottomRoot req.leafIndex)))) = v.topBase req from
      congrArg truncateHash (hv (.rndTop _ _)), topSignature]
    cases v.layerSignature H topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (rootBytes (v.bottomRoot req.leafIndex)) (v.topBase req) with
    | none => rfl
    | some top => rfl

/-! ### The cells read -/

theorem cellReads_chainWalk (l : Layer) (e : KeyIndex) (i : ChainIndex) : ∀ j,
    QueriesSatisfy (romAnswers H) (TableRead S0 v)
      (Over.chainWalk hashQ v.param l e i 0 j (v.chainStart l e i))
  | 0 => queriesSatisfy_pure _
  | j + 1 => by
    have ih := cellReads_chainWalk l e i j
    have hval := eval_chainWalk hv l e i j
    rw [Over.chainWalk] at ih hval ⊢
    rw [walkChain]
    refine queriesSatisfy_bind ih ?_
    rw [hval]
    by_cases h : j < chainLength - 1
    · rw [dite_eq_left (show 0 + j < chainLength - 1 by omega)]
      simp only [Nat.zero_add]
      exact queriesSatisfy_th (Q := v.param) (s := .chain l e ⟨j, h⟩ i) rfl
        ⟨.chain l e i ⟨j, h⟩, rfl⟩
    · rw [dite_eq_right (show ¬(0 + j < chainLength - 1) by omega)]
      exact queriesSatisfy_pure _

omit hv in
theorem cellReads_otsSecrets (l : Layer) (e : KeyIndex) :
    QueriesSatisfy (romAnswers H) (TableRead S0 v) (Over.otsSecrets hashQ v.param l e v.seed) :=
  queriesSatisfy_bind (queriesSatisfy_sequenceFin fun t ↦
    queriesSatisfy_hashQ_slotInput (Q := v.param) (s := .prf l e t) ⟨.prf l e t, rfl⟩)
    (queriesSatisfy_pure _)

theorem cellReads_oneTimePublicKey (l : Layer) (e : KeyIndex) :
    QueriesSatisfy (romAnswers H) (TableRead S0 v)
      (Over.oneTimePublicKey hashQ v.param l e v.seed) := by
  refine queriesSatisfy_bind (cellReads_otsSecrets l e) ?_
  rw [eval_otsSecrets hv]
  exact queriesSatisfy_sequenceFin fun i ↦ cellReads_chainWalk hv l e i _

theorem cellReads_treeNode (l : Layer) : ∀ level index, level ≤ layerHeight →
    index < 2 ^ (32 - level) →
    QueriesSatisfy (romAnswers H) (TableRead S0 v)
      (Over.treeNode hashQ v.param l v.seed level index)
  | 0, index, _, _ => by
    simp only [Over.treeNode, buildTree]
    refine queriesSatisfy_bind (cellReads_oneTimePublicKey hv l _) ?_
    rw [eval_oneTimePublicKey hv]
    exact queriesSatisfy_th (Q := v.param) (s := .leaf l (leafKey index)) rfl
      ⟨.leaf l (leafKey index), rfl⟩
  | level + 1, index, hl, hi => by
    have hl' : level < layerHeight := by omega
    have hi' : index < 2 ^ (31 - level) := by
      rw [show 31 - level = 32 - (level + 1) by omega]
      exact hi
    have h2 : 2 ^ (32 - level) = 2 * 2 ^ (32 - (level + 1)) := by
      rw [← pow_succ']
      congr 1
      simp only [layerHeight] at hl
      omega
    have c1 := cellReads_treeNode l level (2 * index) (by omega) (by omega)
    have c3 := cellReads_treeNode l level (2 * index + 1) (by omega) (by omega)
    have v1 := eval_treeNode hv l level (2 * index) (by omega) (by omega)
    have v3 := eval_treeNode hv l level (2 * index + 1) (by omega) (by omega)
    simp only [Over.treeNode] at c1 c3 v1 v3 ⊢
    rw [buildTree]
    refine queriesSatisfy_bind c1 ?_
    rw [v1]
    refine queriesSatisfy_bind c3 ?_
    rw [v3]
    exact queriesSatisfy_th (Q := v.param) (s := Pos.slot (.node l ⟨level, hl'⟩ ⟨index, hi'⟩))
      (d := payload S0 v (.node l ⟨level, hl'⟩ ⟨index, hi'⟩)) rfl
      ⟨.node l ⟨level, hl'⟩ ⟨index, hi'⟩, rfl⟩

theorem cellReads_treePath (l : Layer) (e : KeyIndex) :
    QueriesSatisfy (romAnswers H) (TableRead S0 v) (Over.treePath hashQ v.param l v.seed e) :=
  queriesSatisfy_sequenceFin fun level ↦
    cellReads_treeNode hv l _ _ level.isLt.le (sibling_lt e level)

/-- **Key generation hashes cells of the table only.** -/
theorem cellReads_generateKeys :
    QueriesSatisfy (romAnswers H) (TableRead S0 v) (xmssRom.generateKeys S0) := by
  change QueriesSatisfy _ _ (Over.keygenFromSeed hashQ S0)
  rw [Over.keygenFromSeed]
  refine queriesSatisfy_bind (queriesSatisfy_hashQ_slotInput (Q := v.param) (s := .seed)
    ⟨.seed, rfl⟩) ?_
  refine queriesSatisfy_bind ?_ ?_
  · rw [show evalWithAnswerFn (romAnswers H) (Over.schemeSeedOf hashQ S0) = v.seed from
      eval_schemeSeedOf hv]
    exact queriesSatisfy_th (Q := v.param) (s := .param) rfl ⟨.param, rfl⟩
  · rw [show evalWithAnswerFn (romAnswers H) (Over.schemeSeedOf hashQ S0) = v.seed from
      eval_schemeSeedOf hv, eval_publicParameterOf hv]
    exact queriesSatisfy_bind
      (cellReads_treeNode hv topLayer layerHeight 0 le_rfl (by positivity))
      (queriesSatisfy_pure _)

theorem signReads_otsSignFrom (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (base : Randomizer) : ∀ attempts trial, QueriesSatisfy (romAnswers H) (SignRead S0 v)
      (Over.otsSignFrom hashQ v.param l e v.seed message.1 base attempts trial)
  | 0, _ => queriesSatisfy_pure _
  | attempts + 1, trial => by
    rw [Over.otsSignFrom]
    refine queriesSatisfy_bind (queriesSatisfy_th (Q := v.param) (s := .msg l e)
      (d := (message, base + BitVec.ofNat digestBits trial)) rfl
      (Or.inr ⟨l, e, _, rfl⟩)) ?_
    rw [Over.messageDigest, eval_th (Q := v.param) (s := .msg l e)
      (d := (message, base + BitVec.ofNat digestBits trial)) rfl]
    cases Codeword.decode (truncateHash (H (cell v.param (.msg l e)
        (message, base + BitVec.ofNat digestBits trial)))) with
    | none => exact signReads_otsSignFrom l e message base attempts (trial + 1)
    | some x =>
      refine queriesSatisfy_bind (queriesSatisfy_mono (fun _ h ↦ Or.inl h)
        (cellReads_otsSecrets l e)) ?_
      rw [eval_otsSecrets hv]
      exact queriesSatisfy_bind (queriesSatisfy_sequenceFin fun i ↦
        queriesSatisfy_mono (fun _ h ↦ Or.inl h) (cellReads_chainWalk hv l e i _))
        (queriesSatisfy_pure _)

/-- The signer of one layer hashes cells of the table and message-digest inputs, its randomizer
base's cell being a cell of the table. -/
theorem signReads_signLayer (l : Layer) (e : KeyIndex) (message : MsgBytes)
    (hR : TableRead S0 v (.inr (cell v.param (.rnd l e) (v.seed, message)))) :
    QueriesSatisfy (romAnswers H) (SignRead S0 v)
      (Over.signLayer hashQ v.seed v.param l e message.1) := by
  rw [Over.signLayer, Over.otsSign]
  refine queriesSatisfy_bind (queriesSatisfy_bind (queriesSatisfy_th (Q := v.param)
    (s := .rnd l e) (d := (v.seed, message)) rfl (Or.inl hR))
    (signReads_otsSignFrom hv l e message _ _ _)) ?_
  split
  · exact queriesSatisfy_bind
      (queriesSatisfy_mono (fun _ h ↦ Or.inl h) (cellReads_treePath hv l e))
      (queriesSatisfy_pure _)
  · exact queriesSatisfy_pure _

/-- **The signer hashes cells of the table and message-digest inputs only.** -/
theorem signReads_sign (req : SigningRequest) :
    QueriesSatisfy (romAnswers H) (SignRead S0 v) (xmssRom.sign (v.secretKey S0) req) := by
  change QueriesSatisfy _ _ (Over.sign hashQ (v.secretKey S0) req.leafIndex req.message)
  rw [Over.sign]
  refine queriesSatisfy_bind (queriesSatisfy_hashQ_slotInput (Q := v.param) (s := .seed)
    (Or.inl ⟨.seed, rfl⟩)) ?_
  simp only [secretKey, eval_schemeSeedOf hv, Over.signWithSchemeSeed]
  refine queriesSatisfy_bind (signReads_signLayer hv bottomLayer _ (messageBytes req.message)
    ⟨.rndBottom _ req.message, rfl⟩) ?_
  rw [show littleEndianBytes 32 req.message = (messageBytes req.message).1 from rfl,
    eval_signLayer hv]
  cases v.layerSignature H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (messageBytes req.message) _ with
  | none => exact queriesSatisfy_pure _
  | some bottom =>
    refine queriesSatisfy_bind (queriesSatisfy_mono (fun _ h ↦ Or.inl h)
      (cellReads_treeNode hv bottomLayer layerHeight _ le_rfl
        (keyIndexOnLayer_top_lt req.leafIndex))) ?_
    rw [eval_treeNode hv bottomLayer layerHeight _ le_rfl (keyIndexOnLayer_top_lt req.leafIndex)]
    refine queriesSatisfy_bind (signReads_signLayer hv topLayer _
      (rootBytes (v.bottomRoot req.leafIndex)) ⟨.rndTop _ (v.bottomRoot req.leafIndex), rfl⟩) ?_
    split <;> exact queriesSatisfy_pure _

omit hv in
theorem not_tableRead_inl (n : ℕ) : ¬TableRead S0 v (.inl n) :=
  fun ⟨_, h⟩ ↦ Sum.inl_ne_inr h

omit hv in
theorem not_signRead_inl (n : ℕ) : ¬SignRead S0 v (.inl n) :=
  fun h ↦ h.elim (fun ⟨_, h⟩ ↦ Sum.inl_ne_inr h) fun ⟨_, _, _, h⟩ ↦ Sum.inl_ne_inr h

variable {r : Type → Type} [Monad r] [LawfulMonad r] {impl : QueryImpl RomOracles r}

/-- **Key generation, run by any implementation answering a consistent `H`**, returns the table's
keys. -/
theorem simulateQ_generateKeys (himpl : ∀ x, impl (.inr x) = pure (H x)) :
    simulateQ impl (xmssRom.generateKeys S0) = pure (v.publicKey, v.secretKey S0) := by
  rw [simulateQ_eq_pure_of_queriesSatisfy himpl not_tableRead_inl _ (cellReads_generateKeys hv),
    eval_generateKeys hv]

/-- **The signer, run by any implementation answering a consistent `H`**, returns the table's
signature. -/
theorem simulateQ_sign (himpl : ∀ x, impl (.inr x) = pure (H x)) (req : SigningRequest) :
    simulateQ impl (xmssRom.sign (v.secretKey S0) req) = pure (v.signature H req) := by
  rw [simulateQ_eq_pure_of_queriesSatisfy himpl not_signRead_inl _ (signReads_sign hv req),
    eval_sign hv]

end QTable

/-! ## Structural slots: honest cells and digests -/

theorem slotOf_cellOf (S0 : MasterSeed) (v : QTable) (p : Pos) :
    slotOf (cellOf S0 p v) = some p.slot :=
  slotOf_cell v.param (addressable_slot p) _

namespace QTable

/-- **The honest cell and digest of a structural slot**: for the chain step, leaf or node slot of
a position `p` of the table, the cell of `p` and the truncation of its value; `none` at every
other slot. -/
def honCell (S0 : MasterSeed) (v : QTable) : Slot → Option (HashDomain × Digest)
  | .chain l e step i =>
      some (cellOf S0 (.chain l e i step) v, truncateHash (v (.chain l e i step)))
  | .leaf l e => some (cellOf S0 (.leaf l e) v, truncateHash (v (.leaf l e)))
  | .node _ 0 _ => none
  | .node l (level + 1) index =>
      if h : level < layerHeight ∧ index < 2 ^ (31 - level) then
        some (cellOf S0 (.node l ⟨level, h.1⟩ ⟨index, h.2⟩) v,
          truncateHash (v (.node l ⟨level, h.1⟩ ⟨index, h.2⟩)))
      else none
  | .msg .. | .prf .. | .rnd .. | .param | .seed => none

/-- **The honest cell of a slot lies in that slot.** -/
theorem slotOf_honCell {S0 : MasterSeed} {v : QTable} {s : Slot} {c : HashDomain} {d : Digest}
    (h : honCell S0 v s = some (c, d)) : slotOf c = some s := by
  cases s with
  | chain l e step i =>
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact slotOf_cellOf S0 v (.chain l e i step)
  | leaf l e =>
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact slotOf_cellOf S0 v (.leaf l e)
  | node l level index =>
    cases level with
    | zero => exact absurd h (by simp [honCell])
    | succ level =>
      simp only [honCell] at h
      split_ifs at h with hb
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact slotOf_cellOf S0 v (.node l ⟨level, hb.1⟩ ⟨index, hb.2⟩)
  | msg => exact absurd h (by simp [honCell])
  | prf => exact absurd h (by simp [honCell])
  | rnd => exact absurd h (by simp [honCell])
  | param => exact absurd h (by simp [honCell])
  | seed => exact absurd h (by simp [honCell])

/-- The honest cell of a chain step, leaf or node position's slot is its cell, holding its
truncated value. -/
theorem honCell_slot (S0 : MasterSeed) (v : QTable) :
    ∀ p : Pos, (∃ l e i step, p = .chain l e i step) ∨ (∃ l e, p = .leaf l e) ∨
      (∃ l k x, p = .node l k x) →
      honCell S0 v p.slot = some (cellOf S0 p v, truncateHash (v p))
  | .chain .., _ => rfl
  | .leaf .., _ => rfl
  | .node _ k x, _ => dite_eq_left ⟨k.isLt, x.isLt⟩
  | .seed, h | .param, h | .prf .., h | .rndBottom .., h | .rndTop .., h => by
    rcases h with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h

end QTable

/-! ## Disclosures -/

/-- The symbolic position (`Quantum.Xmss.Pos`) of a chain step's, leaf's or node's value. -/
def Pos.out : Pos → Option Quantum.Xmss.Pos
  | .chain l e i step => some (.chain l e i (step.val + 1))
  | .leaf l e => some (.tree l 0 e.val)
  | .node l k x => some (.tree l (k.val + 1) x.val)
  | .seed | .param | .prf .. | .rndBottom .. | .rndTop .. => none

/-- The symbolic output of a position's slot is the position's symbolic position. -/
theorem slotOutput_slot : ∀ p : Pos, Quantum.Xmss.slotOutput p.slot = p.out
  | .node l k x => by simp [Quantum.Xmss.slotOutput, Pos.slot, Pos.out]
  | .seed | .param | .prf .. | .chain .. | .leaf .. | .rndBottom .. | .rndTop .. => rfl

namespace QTable

variable (v : QTable)

/-- The value at a symbolic position. -/
def value : Quantum.Xmss.Pos → Digest
  | .chain l e i j => v.chainValue l e i j
  | .tree l level index => v.treeValue l level index

/-- **The value at a position's symbolic position is its truncated value.** -/
theorem value_out : ∀ {p : Pos} {q : Quantum.Xmss.Pos}, p.out = some q →
    v.value q = truncateHash (v p)
  | .chain l e i step, _, h => by
    obtain rfl := Option.some.inj h
    exact dite_eq_left step.isLt
  | .leaf l e, _, h => by
    obtain rfl := Option.some.inj h
    change truncateHash (v (.leaf l (leafKey e.val))) = _
    rw [leafKey_val]
  | .node l k x, _, h => by
    obtain rfl := Option.some.inj h
    exact dite_eq_left ⟨k.isLt, x.isLt⟩
  | .seed, _, h | .param, _, h | .prf .., _, h | .rndBottom .., _, h | .rndTop .., _, h =>
    by cases h

variable (H : HashDomain → HashOutput)

/-- **The symbolic positions the signature of a request discloses**: both layers' opened chain
positions and paths, when the signer returns a signature; none otherwise. -/
def disclosedBy (req : SigningRequest) : Set Quantum.Xmss.Pos :=
  match v.select H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (messageBytes req.message) (v.bottomBase req),
    v.select H topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (rootBytes (v.bottomRoot req.leafIndex)) (v.topBase req) with
  | some bottom, some top =>
      layerDisclosed bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer) bottom.2 ∪
        layerDisclosed topLayer (keyIndexOnLayer req.leafIndex topLayer) top.2
  | _, _ => ∅

/-- The symbolic positions disclosed after the requests `reqs`: the public key's root and each
request's signature. -/
def disclosures (reqs : List SigningRequest) : Set Quantum.Xmss.Pos :=
  {.tree topLayer layerHeight 0} ∪ ⋃ req ∈ reqs, v.disclosedBy H req

theorem disclosures_mono {reqs reqs' : List SigningRequest} (h : reqs ⊆ reqs') :
    v.disclosures H reqs ⊆ v.disclosures H reqs' :=
  Set.union_subset_union_right _ (Set.biUnion_subset_biUnion_left fun _ hr ↦ h hr)

/-- A signature is returned exactly when the request discloses positions. -/
theorem signature_isSome_iff (req : SigningRequest) :
    (v.signature H req).isSome ↔ v.disclosedBy H req ≠ ∅ := by
  simp only [signature, bottomSignature, topSignature, disclosedBy, layerSignature]
  cases v.select H bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (messageBytes req.message) (v.bottomBase req) with
  | none => simp
  | some bottom =>
    cases v.select H topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (rootBytes (v.bottomRoot req.leafIndex)) (v.topBase req) with
    | none => simp
    | some top =>
      simp only [Option.map_some, Option.bind_some, Option.isSome_some, ne_eq, true_iff]
      exact Set.Nonempty.ne_empty ⟨_, Or.inl (Or.inl ⟨⟨0, by decide⟩, rfl⟩)⟩

end QTable

end Quantum.Qrom.Xmss

end
