module

public import Quantum.Xmss.HonestTable
public import Quantum.Sponge.Target
public import XmssSecurity.Proof.EncodingLemmas
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# The deterministic core of leanXMSS's QRPM proof: a win is a target hit

A database `D` of the Msponge's `h`, `k`, `k'` (the union of the hardwired cells and the adversary's
database) answers a hash call when the sponge evaluation of its blocks is a path of `D`.

* `viewPerm π D`, `viewOut π D`: the sponge and the hash with `D`'s values, `0` outside its points
  (`Dbs.fill`); `OnPath π D input`: `D` holds every read of hashing `input`; `viewHash π D`: the
  partial hash, defined on those inputs. An input on a path reaches its digest
  (`reaches_of_onPath`).
* `Memory`, `xmssTgt`, `xmssBad`: the challenger's memory of each signed key's selected
  message-digest input and digest, and the target of a tail (design 3.3): at a chain, leaf or node
  slot the honest digest for a tail of the honest input's length (`fullTarget`; not the prefixes of
  a multi-block input), except for the honest tail of an exempted slot (`Ex`, the hardwired honest
  paths); at a message slot of a signed key the selected digest, except for the selected input.
* `win_imp_bad`: a forgery that verifies with every hash on a path of `D`, against a valid
  transcript of honest signatures and not returned by the signer, puts `D` in
  `TargetBad π trunc128 (xmssTgt L Ex M)`, provided the exempted slots are public (`Public`) and
  held by `D` with their honest values (`HonestTable.HeldIn`), and `M` records the signer's
  selections (`Memory.Records`).

The proof is by last divergence along each walk the verifier makes. The forged Merkle path reaches
the honest root, so either a node input differs from the honest one while its output is honest (a
target hit), or the forged leaf and path are the honest ones; likewise down the leaf to the chain
ends and down each chain to its forged start. A chain whose forged start is the honest value at
position `x_i < 3` hits the target of its first step unless that step's slot is exempted, hence
public, hence opened by a signature of the same key at a position `≤ x_i`. The forged word is then
pointwise above the signed word, so equal to it (`TargetSum.eq_of_pointwiseLE_of_valid`), and the
forged layer is the signed one unless its message-digest input differs, an encoding hit. A fresh key
has no opened position, and a codeword has a chain below `3`. Both layers: the top layer's message is
the bottom root, so a forged top layer equal to a signed one fixes the bottom root to the honest
root of its tree.

The classification of `XmssSecurity.Proof.ForgeryCases` evaluates the signed and the forged
signature under the same hash functions. Here the signed side's honest values are not those of the
view where the honest cells are hidden (a fresh key's whole chains), so the last-divergence walks
replace it; they cover its encoding, backward-witness, suffix, leaf and Merkle outcomes and the fresh
chain value.
-/

open OracleComp OracleSpec

namespace Quantum.Xmss

open Quantum.Sponge HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel
open Verification

local notation "Comp" => OracleComp LeanXmss.HashSpec

/-! ## Evaluations and queries of hash computations -/

section Queries

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type} {f : QueryImpl spec Id}
  {P : spec.Domain → Prop}

theorem queriesSatisfy_bind_iff {x : OracleComp spec α} {k : α → OracleComp spec β} :
    QueriesSatisfy f P (x >>= k) ↔
      QueriesSatisfy f P x ∧ QueriesSatisfy f P (k (evalWithAnswerFn f x)) := by
  simp only [QueriesSatisfy, queries, trace_bind, List.mem_append]
  exact ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
    fun h q hq ↦ hq.elim (h.1 q) (h.2 q)⟩

theorem queriesSatisfy_query_iff {t : spec.Domain} :
    QueriesSatisfy f P (HasQuery.query (spec := spec) (m := OracleComp spec) t) ↔ P t := by
  simp only [QueriesSatisfy, queries_hasQuery, List.mem_singleton, forall_eq]

theorem QueriesSatisfy.of_sequenceFin :
    ∀ {n : ℕ} {c : Fin n → OracleComp spec β}, QueriesSatisfy f P (sequenceFin c) →
      ∀ i, QueriesSatisfy f P (c i)
  | 0, _, _, i => i.elim0
  | n + 1, c, h, i => by
    simp only [sequenceFin] at h
    obtain ⟨h0, h1⟩ := queriesSatisfy_bind_iff.1 h
    obtain ⟨h1, -⟩ := queriesSatisfy_bind_iff.1 h1
    exact Fin.cases h0 (fun j ↦ QueriesSatisfy.of_sequenceFin h1 j) i

end Queries

section Hash

variable (H : QueryImpl LeanXmss.HashSpec Id)

theorem evalWith_oracleHash (input : HashInput) :
    evalWithAnswerFn H (oracleHashWithHash (m := Comp) input) = H input :=
  simulateQ_HasQuery_query (r := Id) H input

theorem evalWith_th (Q : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    evalWithAnswerFn H (thWithHash (m := Comp) Q fields payload) =
      truncateHash (H (thInput Q fields payload)) := by
  simp only [thWithHash, evalWithAnswerFn_bind, evalWith_oracleHash, evalWithAnswerFn_pure]

variable {H} {Q : HashInput → Prop}

theorem queriesSatisfy_th {P : PublicParameter} {fields : TweakFields} {payload : HashInput}
    (h : QueriesSatisfy H Q (thWithHash (m := Comp) P fields payload)) :
    Q (thInput P fields payload) :=
  queriesSatisfy_query_iff.1 (queriesSatisfy_bind_iff.1 h).1

/-! ### The inputs of verification's hash calls -/

/-- The message-digest input of key `e` of layer `l`. -/
def msgInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (message : HashInput)
    (randomizer : Randomizer) : HashInput :=
  thInput P (hashDomainFields (.message l e)) (message ++ littleEndianBytes 16 randomizer)

/-- The input of the step leaving position `j` of chain `i` of key `e` of layer `l`, at value `v`. -/
def chainInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex) (j : ℕ)
    (v : Digest) : HashInput :=
  thInput P (tweakFields 1 j (layerHi l 0) e) (chainPayload i v)

/-- The leaf input of key `e` of layer `l` with chain ends `E`. -/
def leafInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (E : ChainIndex → Digest) :
    HashInput :=
  thInput P (hashDomainFields (.leaf l e)) (digestsPayload E)

/-- The sibling at level `k` of an authentication path, `0` above the tree. -/
def sibling (path : Fin layerHeight → Digest) (k : ℕ) : Digest :=
  if h : k < layerHeight then path ⟨k, h⟩ else 0

/-- The input of the node at level `k + 1` on the path of key `e` of layer `l`, from the value
`cur` at level `k` and the siblings `sib`. -/
def nodeInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (sib : ℕ → Digest) (k : ℕ)
    (cur : Digest) : HashInput :=
  thInput P (hashDomainFields (.node l (k + 1) (e.val / 2 ^ (k + 1))))
    (if e.val.testBit k then nodePayload (sib k) cur else nodePayload cur (sib k))

variable (H) in
theorem evalWith_chainWalk_succ (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (a k : ℕ) (v : Digest) (h : a + k < chainLength - 1) :
    evalWithAnswerFn H (chainWalkWithHash (m := Comp) P l e i a (k + 1) v) =
      truncateHash (H (chainInput P l e i (a + k)
        (evalWithAnswerFn H (chainWalkWithHash (m := Comp) P l e i a k v)))) := by
  rw [chainWalkWithHash, walkChain, evalWithAnswerFn_bind]
  simp only [h, ↓reduceDIte]
  exact evalWith_th H _ _ _

theorem queriesSatisfy_chainWalk {P : PublicParameter} {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {a : ℕ} {v : Digest} : ∀ {n : ℕ},
      QueriesSatisfy H Q (chainWalkWithHash (m := Comp) P l e i a n v) →
      ∀ k < n, a + k < chainLength - 1 →
        Q (chainInput P l e i (a + k)
          (evalWithAnswerFn H (chainWalkWithHash (m := Comp) P l e i a k v)))
  | 0, _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, hQ, k, hk, h => by
    rw [chainWalkWithHash, walkChain] at hQ
    obtain ⟨h1, h2⟩ := queriesSatisfy_bind_iff.1 hQ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact queriesSatisfy_chainWalk h1 k hk h
    · simp only [h, ↓reduceDIte] at h2
      exact queriesSatisfy_th h2

variable (H) in
theorem evalWith_treeFold_succ (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (path : Fin layerHeight → Digest) (k : ℕ) (v : Digest) :
    evalWithAnswerFn H (treeFoldWithHash (m := Comp) P l e path (k + 1) v) =
      truncateHash (H (nodeInput P l e (sibling path) k
        (evalWithAnswerFn H (treeFoldWithHash (m := Comp) P l e path k v)))) := by
  rw [treeFoldWithHash, foldPath, evalWithAnswerFn_bind]
  exact evalWith_th H _ _ _

theorem queriesSatisfy_treeFold {P : PublicParameter} {l : Layer} {e : KeyIndex}
    {path : Fin layerHeight → Digest} {v : Digest} : ∀ {n : ℕ},
      QueriesSatisfy H Q (treeFoldWithHash (m := Comp) P l e path n v) →
      ∀ k < n, Q (nodeInput P l e (sibling path) k
        (evalWithAnswerFn H (treeFoldWithHash (m := Comp) P l e path k v)))
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hQ, k, hk => by
    rw [treeFoldWithHash, foldPath] at hQ
    obtain ⟨h1, h2⟩ := queriesSatisfy_bind_iff.1 hQ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact queriesSatisfy_treeFold h1 k hk
    · exact queriesSatisfy_th h2

/-- **What an accepted layer computes**: the message digest decodes to a word `x`, the chains are
walked from the signature's values at `x` to their ends `E`, the leaf of `E` is folded along the
path to the root; with every hash input satisfying `Q` when the layer's queries do. -/
theorem layerRoot_spec {P : PublicParameter} {l : Layer} {e : KeyIndex} {msg : HashInput}
    {part : LayerSignature} {root : Digest}
    (hQ : QueriesSatisfy H Q (layerRootWithHash (m := Comp) P l e msg part))
    (hr : evalWithAnswerFn H (layerRootWithHash (m := Comp) P l e msg part) = some root) :
    ∃ x E, Codeword.decode (truncateHash (H (msgInput P l e msg part.randomizer))) = some x ∧
      Q (msgInput P l e msg part.randomizer) ∧
      (∀ i, QueriesSatisfy H Q
        (recoverChainWithHash (m := Comp) P l e i (x i) (part.chainValues i))) ∧
      (∀ i, E i = evalWithAnswerFn H
        (recoverChainWithHash (m := Comp) P l e i (x i) (part.chainValues i))) ∧
      Q (leafInput P l e E) ∧
      QueriesSatisfy H Q (treeFoldWithHash (m := Comp) P l e part.authenticationPath layerHeight
        (truncateHash (H (leafInput P l e E)))) ∧
      evalWithAnswerFn H (treeFoldWithHash (m := Comp) P l e part.authenticationPath layerHeight
        (truncateHash (H (leafInput P l e E)))) = root := by
  rw [layerRootWithHash, evalWithAnswerFn_bind] at hr
  rw [layerRootWithHash] at hQ
  obtain ⟨hQ1, hQ2⟩ := queriesSatisfy_bind_iff.1 hQ
  rw [otsLeafWithHash] at hQ1
  obtain ⟨hQm, hQ1⟩ := queriesSatisfy_bind_iff.1 hQ1
  have hd : evalWithAnswerFn H (messageDigestWithHash (m := Comp) P l e msg part.randomizer) =
      truncateHash (H (msgInput P l e msg part.randomizer)) := evalWith_th H _ _ _
  rw [hd] at hQ1
  generalize hleaf : evalWithAnswerFn H
    (otsLeafWithHash (m := Comp) P l e msg part.randomizer part.chainValues) = leaf at hr hQ2
  rw [otsLeafWithHash, evalWithAnswerFn_bind, hd] at hleaf
  cases hx : Codeword.decode (truncateHash (H (msgInput P l e msg part.randomizer))) with
  | none =>
    simp only [hx] at hleaf
    subst hleaf
    simp at hr
  | some x =>
    simp only [hx] at hleaf hQ1
    obtain ⟨hQc, hQ1⟩ := queriesSatisfy_bind_iff.1 hQ1
    obtain ⟨hQl, -⟩ := queriesSatisfy_bind_iff.1 hQ1
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_sequenceFin,
      leafHashWithHash, tweakableHashWithHash, evalWith_th] at hleaf
    subst hleaf
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at hr
    simp only [evalWithAnswerFn_sequenceFin] at hQl
    simp only [queriesSatisfy_bind_iff] at hQ2
    exact ⟨x, _, rfl, queriesSatisfy_th hQm, QueriesSatisfy.of_sequenceFin hQc, fun _ ↦ rfl,
      queriesSatisfy_th hQl, hQ2.1, hr⟩

end Hash

/-! ## The view of a database -/

section View

variable (π : Equiv.Perm (X × Z)) (D : Dbs X Z)

/-- The sponge with `D`'s values, `0` outside its points. -/
def viewPerm : Equiv.Perm (X × Z) :=
  spongePerm D.fill π

/-- **The total view**: the hash of an input under `viewPerm π D`, the default completion of
`viewHash`. -/
def viewOut : QueryImpl LeanXmss.HashSpec Id :=
  spongeOut (viewPerm π D)

/-- `D` holds every read of hashing `input`: the sponge evaluation of its blocks is a path of `D`. -/
def OnPath (input : HashInput) : Prop :=
  ∀ e ∈ inputReads D.fill π input, e.HeldBy D

open Classical in
/-- **The union view as a hash function**: the hash of the inputs whose evaluation is a path of
`D`. -/
noncomputable def viewHash (input : HashInput) : Option HashOutput :=
  if OnPath π D input then some (viewOut π D input) else none

variable {π D}

theorem viewHash_eq_some_iff {input : HashInput} {o : HashOutput} :
    viewHash π D input = some o ↔ OnPath π D input ∧ viewOut π D input = o := by
  unfold viewHash
  split_ifs with h <;> simp [h]

theorem blocks_ne_nil (input : HashInput) : blocks input ≠ [] := by
  intro h
  have := length_blocks input
  rw [h, List.length_nil] at this
  omega

/-- **An input on a path reaches its view digest.** -/
theorem reaches_of_onPath {input : HashInput} (h : OnPath π D input) :
    Reaches π D trunc128 (absorbTail (viewPerm π D) (blocks input))
      (truncateHash (viewOut π D input)) :=
  reaches_of_agrees π D.fill.1 D.fill.2.1 D.fill.2.2 (blocks_ne_nil input)
    (agreesRounds_of_heldBy π D.fill.1 D.fill.2.1 D.fill.2.2 h).1
    ((agreesRounds_of_heldBy π D.fill.1 D.fill.2.1 D.fill.2.2 h).2 (blocks_ne_nil input))

theorem _root_.Quantum.Sponge.SpongeRead.answeredBy_fill {e : SpongeRead X Z} (h : e.HeldBy D) :
    e.AnsweredBy D.fill := by
  cases e with
  | h z a => exact Dbs.fill_h h
  | k x a => exact Dbs.fill_k h
  | k' x a => exact Dbs.fill_k' h

/-- Keys agreeing on the reads of a message give it the same tail. -/
theorem absorbTail_congr {t t' : SpongeKeys X Z} (msg : List X)
    (h : ∀ e ∈ spongeReads π t.1 t.2.1 t.2.2 msg, e.AnsweredBy t') :
    absorbTail (spongePerm t' π) msg = absorbTail (spongePerm t π) msg := by
  induction msg using List.reverseRecOn with
  | nil => rfl
  | append_singleton msg b ih =>
    have h' : ∀ e ∈ spongeReads π t.1 t.2.1 t.2.2 msg, e.AnsweredBy t' := fun e he ↦
      h e (by rw [spongeReads_append_singleton]; exact List.mem_append_left _ he)
    rw [absorbTail_append_singleton, absorbTail_append_singleton, ih h',
      (spongeReads_congr π msg h').2]

/-- A one-block input is its own tail. -/
theorem absorbTail_blocks_of_lt (φ : Equiv.Perm (X × Z)) {u : HashInput} (h : u.length < 136) :
    absorbTail φ (blocks u) = blocks u := by
  have hl := length_blocks u
  rw [Nat.div_eq_of_lt h] at hl
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hl
  rw [hb]
  have := absorbTail_append_singleton φ [] b
  rw [List.nil_append, absorbTail_nil, List.nil_append] at this
  rw [this, show (Sponge.absorb φ []).1 = 0 from rfl, zero_add]

end View

/-! ## The target function -/

/-- **The challenger's memory**: for each signed key, its selected message-digest input and digest. -/
abbrev Memory := Layer → KeyIndex → Option (HashInput × Digest)

/-- The honest digest of slot `s` as the target of a tail `t` of its honest tail's length (the full
absorbed input of the slot); none for the other tails, such as the prefixes of a multi-block
input. -/
def fullTarget (L : HonestTable) (t : List X) (s : Slot) : Option Digest :=
  if (L.honestTail s).map List.length = some t.length then L.target s else none

/-- The target of a tail at a chain, leaf or node slot: the honest digest for a tail of the honest
length (`fullTarget`), unless the tail is the honest tail of an exempted slot. -/
noncomputable def structTgt (L : HonestTable) (Ex : Set Slot) (t : List X) (s : Slot) :
    Option Digest := by
  classical
  exact if L.honestTail s = some t ∧ s ∈ Ex then none else fullTarget L t s

/-- The target of a tail at a slot: `structTgt`, and at the message slot of a signed key its
selected digest unless the tail is the selected input's (a one-block input, its own tail). -/
noncomputable def slotTgt (L : HonestTable) (Ex : Set Slot) (M : Memory) (t : List X) :
    Slot → Option Digest
  | .msg l e => (M l e).bind fun sel ↦ by
      classical
      exact if t = blocks sel.1 then none else some sel.2
  | s => structTgt L Ex t s

/-- **The XMSS target function** (design 3.3): a tail's target, read from its slot. -/
noncomputable def xmssTgt (L : HonestTable) (Ex : Set Slot) (M : Memory) (t : List X) :
    Option Digest :=
  (slotOf L.param t).bind (slotTgt L Ex M t)

/-- **The XMSS bad databases**: bad, or a tail reaching its target. -/
abbrev xmssBad (L : HonestTable) (Ex : Set Slot) (M : Memory) : Set (Dbs X Z) :=
  TargetBad L.perm trunc128 (xmssTgt L Ex M)

theorem slotTgt_of_structural {L : HonestTable} {Ex : Set Slot} {M : Memory} {t : List X}
    {s : Slot} (h : Structural s) : slotTgt L Ex M t s = structTgt L Ex t s := by
  cases s <;> first | rfl | exact h.elim

/-! ## Signed keys -/

/-- The message a request's signature signs on layer `l`: the message at the bottom, the root of
the bottom tree at the top. -/
def layerMessage (L : HonestTable) (req : SigningRequest) (l : Layer) : HashInput :=
  if l = bottomLayer then littleEndianBytes 32 req.message
  else littleEndianBytes 16 (L.bottomRoot req.leafIndex)

/-- `M` records the selections of the signer of `req`: each layer's selected message-digest input
and digest. -/
def Memory.Records (M : Memory) (L : HonestTable) (req : SigningRequest) : Prop :=
  ∀ l sel, L.select l (keyIndexOnLayer req.leafIndex l) (layerMessage L req l) = some sel →
    M l (keyIndexOnLayer req.leafIndex l) =
      some (msgInput L.param l (keyIndexOnLayer req.leafIndex l) (layerMessage L req l) sel.1,
        L.messageDigest l (keyIndexOnLayer req.leafIndex l) (layerMessage L req l) sel.1)

/-- The cells of the honest path of slot `s` are points of `D` with their honest values. -/
def HonestTable.HeldIn (L : HonestTable) (D : Dbs X Z) (s : Slot) : Prop :=
  ∀ input, L.honestInput s = some input → ∀ e ∈ inputReads L.keys L.perm input, e.HeldBy D

/-! ## Codewords -/

theorem Codeword.sum_eq_of_decode {d : Digest} {x : Encoding} (h : Codeword.decode d = some x) :
    Codeword.sum x = targetSum := by
  unfold Codeword.decode at h
  split_ifs at h with hv
  obtain rfl := Option.some.inj h
  exact hv.2

/-- A codeword is determined by its word. -/
theorem Codeword.eq_of_decode {d d' : Digest} {x : Encoding} (h : Codeword.decode d = some x)
    (h' : Codeword.decode d' = some x) : d = d' := by
  unfold Codeword.decode at h h'
  split_ifs at h h' with hv hv'
  have hx := (Option.some.inj h).trans (Option.some.inj h').symm
  have hlt : ∀ c : Digest, c.toNat / 2 ^ (winternitzBits * chainCount) = 0 → c.toNat < 2 ^ 116 :=
    fun c hc ↦ by
      rw [Nat.div_eq_zero_iff] at hc
      simpa [winternitzBits, chainCount] using hc.resolve_left (by positivity)
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  by_cases hb' : b < 116
  · have hi : b / 2 < chainCount := by simp only [chainCount]; omega
    have hdig := congrArg (fun y : Encoding ↦ (y ⟨b / 2, hi⟩).val) hx
    simp only [digestDigits] at hdig
    have hv2 : d.extractLsb' (winternitzBits * (b / 2)) winternitzBits =
        d'.extractLsb' (winternitzBits * (b / 2)) winternitzBits := BitVec.toNat_inj.1 hdig
    have := congrArg (fun y ↦ y.getLsbD (b % 2)) hv2
    simp only [BitVec.getLsbD_extractLsb', winternitzBits] at this
    have hb2 : 2 * (b / 2) + b % 2 = b := Nat.div_add_mod b 2
    simpa [Nat.mod_lt b (show 2 > 0 by norm_num), hb2] using this
  · rw [BitVec.getLsbD, BitVec.getLsbD,
      Nat.testBit_lt_two_pow ((hlt d hv.1).trans_le (Nat.pow_le_pow_right (by norm_num)
        (by omega))),
      Nat.testBit_lt_two_pow ((hlt d' hv'.1).trans_le (Nat.pow_le_pow_right (by norm_num)
        (by omega)))]

/-- A codeword has a chain opened below its end. -/
theorem Codeword.exists_lt_of_sum {x : Encoding} (hx : Codeword.sum x = targetSum) :
    ∃ i, (x i).val < chainLength - 1 := by
  by_contra h
  push Not at h
  have hc : chainLength = 4 := rfl
  have hs : Codeword.sum x = ∑ _i : ChainIndex, 3 :=
    Finset.sum_congr rfl fun i _ ↦ by have := (x i).isLt; have := h i; omega
  rw [hx] at hs
  simp [targetSum, chainCount] at hs

/-- **Incomparability**: a codeword pointwise below another is equal to it
(`TargetSum.eq_of_pointwiseLE_of_valid`). -/
theorem Codeword.eq_of_le {x y : Encoding} (hx : Codeword.sum x = targetSum)
    (hy : Codeword.sum y = targetSum) (hle : ∀ i, x i ≤ y i) : x = y :=
  XmssSecurity.TargetSum.eq_of_pointwiseLE_of_valid hx hy hle

/-! ## Injectivity of the inputs -/

theorem littleEndianBytes_injective (n : ℕ) : Function.Injective (littleEndianBytes n) :=
  fun v w h ↦ BitVec.eq_of_getLsbD_eq fun j _ ↦ bitOf_injective (by
    rw [← inputBit_littleEndianBytes, h, inputBit_littleEndianBytes])

theorem chainPayload_injective {i : ChainIndex} {v w : Digest}
    (h : chainPayload i v = chainPayload i w) : v = w :=
  littleEndianBytes_injective 16 (List.append_inj h
    (by simp only [littleEndianBytes, List.length_ofFn])).1

theorem nodePayload_injective {a b a' b' : Digest} (h : nodePayload a b = nodePayload a' b') :
    a = a' ∧ b = b' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp only [littleEndianBytes, List.length_ofFn])
  exact ⟨littleEndianBytes_injective 16 h1, littleEndianBytes_injective 16 h2⟩

theorem flatMap_littleEndianBytes_injective :
    ∀ {a b : List (BitVec (8 * 16))}, a.length = b.length →
      a.flatMap (littleEndianBytes 16) = b.flatMap (littleEndianBytes 16) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h
      (by simp only [littleEndianBytes, List.length_ofFn])
    rw [littleEndianBytes_injective 16 h1,
      flatMap_littleEndianBytes_injective (by simpa using hl) h2]

theorem digestsPayload_injective {E E' : ChainIndex → Digest}
    (h : digestsPayload E = digestsPayload E') : E = E' :=
  List.ofFn_injective (flatMap_littleEndianBytes_injective
    (by exact List.length_ofFn.trans List.length_ofFn.symm) h)

theorem chainInput_inj {P : PublicParameter} {l : Layer} {e : KeyIndex} {i : ChainIndex} {j : ℕ}
    {v w : Digest} (h : chainInput P l e i j v = chainInput P l e i j w) : v = w :=
  chainPayload_injective (thInput_injective P h).2

theorem nodeInput_inj {P : PublicParameter} {l : Layer} {e : KeyIndex} {sib sib' : ℕ → Digest}
    {k : ℕ} {cur cur' : Digest} (h : nodeInput P l e sib k cur = nodeInput P l e sib' k cur') :
    cur = cur' ∧ sib k = sib' k := by
  have hp := (thInput_injective P h).2
  split_ifs at hp
  · exact (nodePayload_injective hp).symm
  · exact nodePayload_injective hp

theorem length_chainInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (j : ℕ) (v : Digest) : (chainInput P l e i j v).length = 64 := by
  simp [chainInput, length_thInput, chainPayload, littleEndianBytes]

theorem length_nodeInput (P : PublicParameter) (l : Layer) (e : KeyIndex) (sib : ℕ → Digest)
    (k : ℕ) (cur : Digest) : (nodeInput P l e sib k cur).length = 64 := by
  unfold nodeInput
  split <;> simp [length_thInput, nodePayload, littleEndianBytes]

theorem length_leafInput (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (E : ChainIndex → Digest) : (leafInput P l e E).length = 32 + 16 * chainCount := by
  rw [leafInput, length_thInput]
  exact congrArg (32 + ·) ((length_flatMap_littleEndianBytes (List.ofFn E)).trans
    (congrArg (16 * ·) (List.length_ofFn (f := E))))

/-! ## Last divergence -/

/-- **Last divergence.** A walk of `n` steps, step `k` querying `u k` (the honest input `w k`) and
outputting `f (k + 1)` (honestly `g (k + 1)`), whose end is honest: either some step's input is not
the honest one while its output is, or every input is honest. An honest input after a step carries
that step's honest output. -/
theorem last_divergence {β γ : Type} (u w : ℕ → β) (f g : ℕ → γ) (n : ℕ) (hn : f n = g n)
    (hstep : ∀ k, k + 1 < n → u (k + 1) = w (k + 1) → f (k + 1) = g (k + 1)) :
    (∃ k < n, u k ≠ w k ∧ f (k + 1) = g (k + 1)) ∨ ∀ k < n, u k = w k := by
  induction n with
  | zero => exact Or.inr fun k hk ↦ absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    by_cases hu : u n = w n
    · rcases n with _ | m
      · exact Or.inr fun k hk ↦ by rw [show k = 0 by omega]; exact hu
      · rcases ih (hstep m (by omega) hu) (fun k hk ↦ hstep k (by omega)) with ⟨k, hk, h⟩ | h
        · exact Or.inl ⟨k, by omega, h⟩
        · exact Or.inr fun k hk ↦ by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
            · exact h k hk
            · exact hu
    · exact Or.inl ⟨n, by omega, hu, hn⟩

/-! ## Target hits -/

section Hits

variable {L : HonestTable} {Ex : Set Slot} {M : Memory} {D : Dbs X Z}

/-- **A structural hit**: an input on a path at a chain, leaf or node slot, of the length of the
slot's honest input, whose view digest is the slot's honest digest, other than the honest input of
an exempted slot. -/
theorem mem_xmssBad_of_struct (hHeld : ∀ s ∈ Ex, L.HeldIn D s) {u : HashInput} {s : Slot}
    (hu : OnPath L.perm D u)
    (hs : slotOf L.param (absorbTail (viewPerm L.perm D) (blocks u)) = some s)
    (hst : Structural s) (ht : L.target s = some (truncateHash (viewOut L.perm D u)))
    (hne : L.honestInput s = some u → s ∉ Ex)
    (hlen : ∀ h0, L.honestInput s = some h0 → h0.length = u.length) : D ∈ xmssBad L Ex M := by
  refine Or.inr ⟨_, _, ?_, reaches_of_onPath hu⟩
  obtain ⟨h1, hh1⟩ : ∃ h1, L.honestInput s = some h1 := by
    cases hi : L.honestInput s with
    | none => simp [HonestTable.target, hi] at ht
    | some h1 => exact ⟨h1, rfl⟩
  have hfull : (L.honestTail s).map List.length =
      some (absorbTail (viewPerm L.perm D) (blocks u)).length := by
    simp only [HonestTable.honestTail, hh1, Option.map_some, length_absorbTail, length_blocks,
      hlen h1 hh1]
  have hnex : ¬(L.honestTail s = some (absorbTail (viewPerm L.perm D) (blocks u)) ∧ s ∈ Ex) := by
    rintro ⟨htail, hEx⟩
    simp only [HonestTable.honestTail, Option.map_eq_some_iff] at htail
    obtain ⟨h0, hh0, heq⟩ := htail
    have hc := absorbTail_congr (π := L.perm) (t := L.keys) (t' := D.fill) (blocks h0)
      fun e he ↦ SpongeRead.answeredBy_fill (hHeld s hEx h0 hh0 e he)
    have : h0 = u := blocks_injective (absorbTail_injective (viewPerm L.perm D) (hc.trans heq))
    exact hne (this ▸ hh0) hEx
  rw [xmssTgt, hs, Option.bind_some, slotTgt_of_structural hst, structTgt, ite_eq_right hnex,
    fullTarget, ite_eq_left hfull, ht]

/-- **An encoding hit**: a one-block input on a path at the message slot of a signed key, other
than the selected input, whose view digest is the selected digest. -/
theorem mem_xmssBad_of_enc {u c : HashInput} {l : Layer} {e : KeyIndex} {y : Digest}
    (hu : OnPath L.perm D u)
    (hs : slotOf L.param (absorbTail (viewPerm L.perm D) (blocks u)) = some (.msg l e))
    (hM : M l e = some (c, y)) (hlen : u.length < 136) (hne : u ≠ c)
    (hy : truncateHash (viewOut L.perm D u) = y) : D ∈ xmssBad L Ex M := by
  refine Or.inr ⟨_, _, ?_, reaches_of_onPath hu⟩
  rw [xmssTgt, hs, Option.bind_some]
  show (M l e).bind _ = _
  rw [hM, Option.bind_some, absorbTail_blocks_of_lt _ hlen,
    ite_eq_right fun h ↦ hne (blocks_injective h), hy]

end Hits

/-! ## Walks meeting the honest table -/

section Meet

variable {L : HonestTable} {Ex : Set Slot} {M : Memory} {D : Dbs X Z}

/-- **A chain walk ending at the honest chain** (no hit): it starts at the honest value, and the
slot of its first step is exempted. -/
theorem chain_meet (hHeld : ∀ s ∈ Ex, L.HeldIn D s) (hnb : D ∉ xmssBad L Ex M) {l : Layer}
    {e : KeyIndex} (he : e.val < keyCount l) {i : ChainIndex} {a n : ℕ} (hn : 0 < n)
    (han : a + n ≤ chainLength - 1) {v : Digest}
    (hQ : QueriesSatisfy (viewOut L.perm D) (OnPath L.perm D)
      (chainWalkWithHash (m := Comp) L.param l e i a n v))
    (hend : evalWithAnswerFn (viewOut L.perm D)
      (chainWalkWithHash (m := Comp) L.param l e i a n v) = L.chainValue l e i (a + n)) :
    v = L.chainValue l e i a ∧ ∀ h : a < chainLength - 1, Slot.chain l e ⟨a, h⟩ i ∈ Ex := by
  set H := viewOut L.perm D
  let f : ℕ → Digest := fun k ↦
    evalWithAnswerFn H (chainWalkWithHash (m := Comp) L.param l e i a k v)
  let g : ℕ → Digest := fun k ↦ L.chainValue l e i (a + k)
  let u : ℕ → HashInput := fun k ↦ chainInput L.param l e i (a + k) (f k)
  let w : ℕ → HashInput := fun k ↦ chainInput L.param l e i (a + k) (g k)
  have hit : ∀ k (hk : k < n), f (k + 1) = g (k + 1) →
      (u k = w k → Slot.chain l e ⟨a + k, by omega⟩ i ∉ Ex) → False := by
    intro k hk hfg hne
    apply hnb
    refine mem_xmssBad_of_struct hHeld (queriesSatisfy_chainWalk hQ k hk (by omega))
      (slotOf_chain _ _ l e ⟨a + k, by omega⟩ i _) trivial ?_ ?_ ?_
    · exact (L.target_eq_some (s := .chain l e ⟨a + k, by omega⟩ i) he rfl).trans
        (congrArg some (hfg.symm.trans (evalWith_chainWalk_succ H _ _ _ _ a k v (by omega))))
    · intro hh
      exact hne (Option.some.inj (hh.symm.trans (HonestTable.honestInput_chain he _ i)))
    · intro h0 hh0
      obtain rfl := Option.some.inj ((HonestTable.honestInput_chain he _ i).symm.trans hh0)
      exact (length_chainInput L.param l e i (a + k) _).trans
        (length_chainInput L.param l e i (a + k) _).symm
  have hstep : ∀ k, k + 1 < n → u (k + 1) = w (k + 1) → f (k + 1) = g (k + 1) :=
    fun _ _ h ↦ chainInput_inj h
  rcases last_divergence u w f g n hend hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exact (hit k hk hfg fun h ↦ absurd h hne).elim
  · have h0 : f 0 = g 0 := chainInput_inj (hall 0 hn)
    refine ⟨h0, fun ha ↦ ?_⟩
    by_contra hEx
    have h1 : f 1 = g 1 := by
      rcases Nat.lt_or_ge 1 n with h | h
      · exact chainInput_inj (hall 1 h)
      · obtain rfl : n = 1 := by omega
        exact hend
    exact hit 0 hn h1 fun _ ↦ hEx

theorem slotOf_nodeInput (φ : Equiv.Perm (X × Z)) (P : PublicParameter) {l : Layer}
    {e : KeyIndex} (he : e.val < keyCount l) (sib : ℕ → Digest) {k : ℕ} (hk : k < layerHeight)
    (cur : Digest) :
    slotOf P (absorbTail φ (blocks (nodeInput P l e sib k cur))) =
      some (.node l (k + 1) (e.val / 2 ^ (k + 1))) := by
  have hlevel : k + 1 < 2 ^ 23 := by norm_num [layerHeight] at hk ⊢; omega
  have hindex : e.val / 2 ^ (k + 1) < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (lt_of_lt_of_le he (keyCount_le l))
  unfold nodeInput
  split <;> exact slotOf_node φ P l (k + 1) _ hlevel hindex _ _

theorem inTable_node {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) {k : ℕ}
    (hk : k < layerHeight) : InTable (.node l (k + 1) (e.val / 2 ^ (k + 1))) := by
  have hK := le_keyBits l
  have hLH : layerHeight = 16 := rfl
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel (by omega)]
  exact he

/-- The honest input of the node above level `k` on the path of key `e`: the honest value and
sibling at level `k`, ordered by bit `k` of `e`. -/
theorem honestInput_node_path {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) {k : ℕ}
    (hk : k < layerHeight) :
    L.honestInput (.node l (k + 1) (e.val / 2 ^ (k + 1))) =
      some (nodeInput L.param l e (fun k ↦ L.treeValue l k (e.val / 2 ^ k ^^^ 1)) k
        (L.treeValue l k (e.val / 2 ^ k))) := by
  rw [HonestTable.honestInput_node (by omega) (inTable_node he hk).2.2, Option.some.injEq]
  unfold nodeInput
  congr 1
  have hj : e.val / 2 ^ (k + 1) = e.val / 2 ^ k / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hj, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (e.val / 2 ^ k) with h | h
  · have hx : e.val / 2 ^ k ^^^ 1 = e.val / 2 ^ k + 1 := Nat.xor_one_of_even (Nat.even_iff.2 h)
    simp only [h, hx, zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
    congr 2 <;> omega
  · have hx : e.val / 2 ^ k ^^^ 1 = e.val / 2 ^ k - 1 := Nat.xor_one_of_odd (Nat.odd_iff.2 h)
    simp only [h, hx, decide_true, ↓reduceIte]
    congr 2 <;> omega

/-- **A Merkle path ending at the honest root** (no hit): it starts at the honest leaf and its
siblings are the honest authentication path. -/
theorem path_meet (hHeld : ∀ s ∈ Ex, L.HeldIn D s) (hnb : D ∉ xmssBad L Ex M) {l : Layer}
    {e : KeyIndex} (he : e.val < keyCount l) {path : Fin layerHeight → Digest} {v : Digest}
    (hQ : QueriesSatisfy (viewOut L.perm D) (OnPath L.perm D)
      (treeFoldWithHash (m := Comp) L.param l e path layerHeight v))
    (hroot : evalWithAnswerFn (viewOut L.perm D)
      (treeFoldWithHash (m := Comp) L.param l e path layerHeight v) =
        L.treeValue l layerHeight (e.val / 2 ^ layerHeight)) :
    v = L.treeValue l 0 e.val ∧ path = L.authPath l e := by
  set H := viewOut L.perm D
  let f : ℕ → Digest := fun k ↦
    evalWithAnswerFn H (treeFoldWithHash (m := Comp) L.param l e path k v)
  let g : ℕ → Digest := fun k ↦ L.treeValue l k (e.val / 2 ^ k)
  let hs : ℕ → Digest := fun k ↦ L.treeValue l k (e.val / 2 ^ k ^^^ 1)
  let u : ℕ → HashInput := fun k ↦ nodeInput L.param l e (sibling path) k (f k)
  let w : ℕ → HashInput := fun k ↦ nodeInput L.param l e hs k (g k)
  have hstep : ∀ k, k + 1 < layerHeight → u (k + 1) = w (k + 1) → f (k + 1) = g (k + 1) :=
    fun _ _ h ↦ (nodeInput_inj h).1
  rcases last_divergence u w f g layerHeight hroot hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exfalso
    apply hnb
    refine mem_xmssBad_of_struct hHeld (queriesSatisfy_treeFold hQ k hk)
      (slotOf_nodeInput _ _ he _ hk _) trivial ?_ ?_ ?_
    · exact (L.target_eq_some (p := .tree l (k + 1) (e.val / 2 ^ (k + 1))) (inTable_node he hk)
        (by simp [slotOutput])).trans
        (congrArg some (hfg.symm.trans (evalWith_treeFold_succ H _ _ _ _ k v)))
    · intro hh
      exact absurd (Option.some.inj (hh.symm.trans (honestInput_node_path he hk))) hne
    · intro h0 hh0
      obtain rfl := Option.some.inj ((honestInput_node_path he hk).symm.trans hh0)
      exact (length_nodeInput _ _ _ _ _ _).trans (length_nodeInput _ _ _ _ _ _).symm
  · have h0 := (nodeInput_inj (hall 0 (by decide))).1
    change v = L.treeValue l 0 (e.val / 2 ^ 0) at h0
    rw [pow_zero, Nat.div_one] at h0
    refine ⟨h0, funext fun k ↦ ?_⟩
    have hk := (nodeInput_inj (hall k.val k.isLt)).2
    simp only [sibling, k.isLt, ↓reduceDIte] at hk
    exact hk

end Meet

/-! ## Signed keys and the opened chain positions -/

section Signed

variable {L : HonestTable}

theorem layerMessage_bottom (L : HonestTable) (req : SigningRequest) :
    layerMessage L req bottomLayer = littleEndianBytes 32 req.message :=
  ite_eq_left rfl

theorem layerMessage_top (L : HonestTable) (req : SigningRequest) :
    layerMessage L req topLayer = littleEndianBytes 16 (L.bottomRoot req.leafIndex) :=
  ite_eq_right (by decide)

theorem eq_topLayer {l : Layer} (h : l ≠ bottomLayer) : l = topLayer := by
  have h2 : l.val < 2 := l.isLt
  have h0 : l.val ≠ 0 := fun h' ↦ h (Fin.ext h')
  exact Fin.ext (show l.val = 1 by omega)

/-- A signature is its leaf index and its two layers. -/
theorem signature_eq_layers (σ : Signature) :
    (⟨σ.leafIndex, fun lay ↦ if lay = bottomLayer then σ.layers bottomLayer
      else σ.layers topLayer⟩ : Signature) = σ := by
  rcases σ with ⟨i, ls⟩
  congr 1
  funext lay
  split_ifs with h
  · rw [h]
  · rw [eq_topLayer h]

/-- The selection decodes its digest to its word. -/
theorem HonestTable.decode_of_selectFrom (L : HonestTable) {l : Layer} {e : KeyIndex}
    {msg : HashInput} {base : Randomizer} :
    ∀ attempts trial {sel : Randomizer × Encoding},
      L.selectFrom l e msg base attempts trial = some sel →
        Codeword.decode (L.messageDigest l e msg sel.1) = some sel.2
  | 0, _, _, h => by simp [HonestTable.selectFrom] at h
  | n + 1, trial, sel, h => by
    rw [HonestTable.selectFrom] at h
    split at h
    · next x hx =>
      obtain rfl := Option.some.inj h
      exact hx
    · exact L.decode_of_selectFrom n (trial + 1) h

theorem HonestTable.decode_of_select (L : HonestTable) {l : Layer} {e : KeyIndex}
    {msg : HashInput} {sel : Randomizer × Encoding} (h : L.select l e msg = some sel) :
    Codeword.decode (L.messageDigest l e msg sel.1) = some sel.2 :=
  L.decode_of_selectFrom _ _ h

/-- A chain position computable from disclosed positions lies above a disclosed one. -/
theorem known_chain {K : Set Pos} {p : Pos} (h : Known K p) :
    ∀ l e i j, p = .chain l e i j → ∃ j' ≤ j, Pos.chain l e i j' ∈ K := by
  induction h with
  | disclosed p hp =>
    rintro l e i j rfl
    exact ⟨j, le_rfl, hp⟩
  | chain l e i step _ ih =>
    intro l' e' i' j' hp
    simp only [Pos.chain.injEq] at hp
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
    obtain ⟨j'', hj, hm⟩ := ih l e i step.val rfl
    exact ⟨j'', by omega, hm⟩
  | leaf => intro _ _ _ _ hp; cases hp
  | node => intro _ _ _ _ hp; cases hp

/-- **An opened chain position comes from a signature by its key**: the key's selection for the
request's message opens the chain at or below it. -/
theorem exists_signed_of_known {reqs : List SigningRequest} {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {j : ℕ} (h : Known (L.disclosures reqs) (.chain l e i j)) :
    ∃ req ∈ reqs, keyIndexOnLayer req.leafIndex l = e ∧
      ∃ sel, L.select l e (layerMessage L req l) = some sel ∧ (sel.2 i).val ≤ j := by
  obtain ⟨j', hj', hm⟩ := known_chain h l e i j rfl
  rcases hm with hm | hm
  · simp at hm
  simp only [Set.mem_iUnion] at hm
  obtain ⟨req, hreq, hd⟩ := hm
  refine ⟨req, hreq, ?_⟩
  unfold HonestTable.disclosedBy at hd
  rcases hb : L.select bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message) with _ | b <;>
    rcases ht : L.select topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with _ | tp <;>
    simp only [hb, ht, Set.mem_empty_iff_false] at hd
  rcases hd with (⟨i', hi'⟩ | ⟨lv, hlv⟩) | (⟨i', hi'⟩ | ⟨lv, hlv⟩)
  · simp only [Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, b, by rw [layerMessage_bottom]; exact hb, hj'⟩
  · cases hlv
  · simp only [Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, tp, by rw [layerMessage_top]; exact ht, hj'⟩
  · cases hlv

/-- **One selection per key**: in a valid transcript, two requests signing with the same key of a
layer sign the same message on it (the same request at the bottom, the same bottom root at the
top). -/
theorem layerMessage_eq_of_key {log : QueryLog SigningOracleSpec}
    (hvalid : SigningTranscript.NoLeafIndexReused log) {r r' : (_ : SigningRequest) × Option Signature}
    (hr : r ∈ log) (hr' : r' ∈ log) {l : Layer}
    (hk : keyIndexOnLayer r.1.leafIndex l = keyIndexOnLayer r'.1.leafIndex l) :
    layerMessage L r.1 l = layerMessage L r'.1 l := by
  by_cases hl : l = bottomLayer
  · subst hl
    have hidx : r.1.leafIndex = r'.1.leafIndex := by
      apply Fin.ext
      have := congrArg Fin.val hk
      simpa [keyIndexOnLayer, bottomLayer] using this
    rw [List.inj_on_of_nodup_map hvalid hr hr' hidx]
  · obtain rfl := eq_topLayer hl
    rw [layerMessage_top, layerMessage_top, HonestTable.bottomRoot, HonestTable.bottomRoot, hk]

end Signed

/-! ## Both layers -/

section Layers

variable {L : HonestTable} {Ex : Set Slot} {M : Memory} {D : Dbs X Z}
  {log : QueryLog SigningOracleSpec}

/-- **A layer reaching the honest root of its tree** (no hit) is the signature of that layer by a
signed request with the same key, on the same message. -/
theorem layer_meet (hM : ∀ r ∈ log, M.Records L r.1)
    (hEx : Ex ⊆ Public (L.disclosures (log.map Sigma.fst))) (hHeld : ∀ s ∈ Ex, L.HeldIn D s)
    (hvalid : SigningTranscript.NoLeafIndexReused log) (hnb : D ∉ xmssBad L Ex M)
    {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) {msg : HashInput}
    (hmsg : 16 ≤ msg.length ∧ msg.length ≤ 32) {part : LayerSignature}
    (hQ : QueriesSatisfy (viewOut L.perm D) (OnPath L.perm D)
      (layerRootWithHash (m := Comp) L.param l e msg part))
    (hr : evalWithAnswerFn (viewOut L.perm D) (layerRootWithHash (m := Comp) L.param l e msg part) =
      some (L.treeValue l layerHeight (e.val / 2 ^ layerHeight))) :
    ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex l = e ∧ msg = layerMessage L r.1 l ∧
      L.layerSignature l e msg = some part := by
  obtain ⟨x, E, hx, hQm, hQc, hEeq, hQl, hQt, hroot⟩ := layerRoot_spec hQ hr
  obtain ⟨hleaf, hpath⟩ := path_meet hHeld hnb he hQt hroot
  -- The leaf: the forged chain ends are the honest ones.
  have hE : E = L.endpoints l e := by
    by_contra hne
    apply hnb
    refine mem_xmssBad_of_struct hHeld hQl (slotOf_leaf _ _ l e E) trivial ?_ ?_ ?_
    · exact (L.target_eq_some (s := .leaf l e) he rfl).trans (congrArg some hleaf.symm)
    · intro hh
      exact absurd (digestsPayload_injective (thInput_injective _
        (Option.some.inj (hh.symm.trans (HonestTable.honestInput_leaf he)))).2) hne
    · intro h0 hh0
      obtain rfl := Option.some.inj ((HonestTable.honestInput_leaf he).symm.trans hh0)
      exact (length_leafInput L.param l e (L.endpoints l e)).trans
        (length_leafInput L.param l e E).symm
  -- The chains: the forged values are honest, and the steps leaving them exempted.
  have hchain : ∀ i, part.chainValues i = L.chainValue l e i (x i).val ∧
      ∀ h : (x i).val < chainLength - 1, Slot.chain l e ⟨(x i).val, h⟩ i ∈ Ex := by
    intro i
    have hEi : E i = L.chainValue l e i (chainLength - 1) := congrFun hE i
    rw [hEeq i] at hEi
    by_cases h3 : (x i).val < chainLength - 1
    · have hsum : (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 := by omega
      exact chain_meet hHeld hnb he (a := (x i).val) (n := chainLength - 1 - (x i).val)
        (by omega) (by omega) (hQc i) (hEi.trans (congrArg (L.chainValue l e i) hsum.symm))
    · have h3' : (x i).val = chainLength - 1 := by have := (x i).isLt; omega
      refine ⟨?_, fun h ↦ absurd h h3⟩
      have hv : evalWithAnswerFn (viewOut L.perm D) (recoverChainWithHash (m := Comp) L.param l e
          i (x i) (part.chainValues i)) = part.chainValues i := by
        show evalWithAnswerFn (viewOut L.perm D) (chainWalkWithHash (m := Comp) L.param l e i
          (x i).val (chainLength - 1 - (x i).val) (part.chainValues i)) = _
        rw [h3', Nat.sub_self]
        rfl
      exact hv.symm.trans (hEi.trans (congrArg (L.chainValue l e i) h3'.symm))
  -- An exempted step is public: a signature by the same key opened its chain at or below it.
  have hvx := Codeword.sum_eq_of_decode hx
  have hknown : ∀ i (h : (x i).val < chainLength - 1),
      Known (L.disclosures (log.map Sigma.fst)) (.chain l e i (x i).val) :=
    fun i h ↦ (hEx ((hchain i).2 h)).2
  obtain ⟨i0, hi0⟩ := Codeword.exists_lt_of_sum hvx
  obtain ⟨req, hreq, hkey, sel, hsel, -⟩ := exists_signed_of_known (hknown i0 hi0)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hreq
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨req', hreq', hkey', sel', hsel', hj⟩ := exists_signed_of_known (hknown i h)
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hreq'
      rw [layerMessage_eq_of_key hvalid hr hr' (hkey.trans hkey'.symm), hsel'] at hsel
      obtain rfl := Option.some.inj hsel
      exact hj
    · show (sel.2 i).val ≤ (x i).val
      have := (sel.2 i).isLt
      omega
  -- Incomparability: the forged word is the selected one.
  have hvs := L.decode_of_select hsel
  have hxs : sel.2 = x := Codeword.eq_of_le (Codeword.sum_eq_of_decode hvs) hvx hle
  -- The message-digest input is the selected one, or an encoding hit.
  have hmeq : msgInput L.param l e msg part.randomizer =
      msgInput L.param l e (layerMessage L r.1 l) sel.1 := by
    by_contra hne
    apply hnb
    have hMr := hM r hr l sel (by rw [hkey]; exact hsel)
    rw [hkey] at hMr
    refine mem_xmssBad_of_enc hQm (slotOf_msg _ _ l e msg hmsg.1 _) hMr ?_ hne ?_
    · simp only [msgInput, length_thInput, List.length_append, littleEndianBytes,
        List.length_ofFn]
      omega
    · exact Codeword.eq_of_decode hx (hxs ▸ hvs)
  obtain ⟨-, hpay⟩ := thInput_injective _ hmeq
  obtain ⟨hmsgEq, hρ⟩ := List.append_inj' hpay (by simp only [littleEndianBytes, List.length_ofFn])
  have hρ' : part.randomizer = sel.1 := littleEndianBytes_injective 16 hρ
  refine ⟨r, hr, hkey, hmsgEq, ?_⟩
  have hcv : (fun i ↦ L.chainValue l e i (sel.2 i).val) = part.chainValues :=
    funext fun i ↦ (congrArg (fun y : Encoding ↦ L.chainValue l e i (y i).val) hxs).trans
      ((hchain i).1).symm
  rw [hmsgEq, HonestTable.layerSignature, hsel, Option.map_some, hcv, ← hρ', ← hpath]

/-- **A win is a target hit** (slice S7, both layers): a forgery that verifies with every hash
computed on a path of `D`, against a valid transcript of honest signatures and not returned by the
signer, puts `D` in `xmssBad`, when the exempted slots are public and held by `D` with their honest
values and `M` records the signer's selections. -/
theorem win_imp_bad (L : HonestTable) (Ex : Set Slot) (M : Memory) (D : Dbs X Z)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = L.signature r.1) (hM : ∀ r ∈ log, M.Records L r.1)
    (hEx : Ex ⊆ Public (L.disclosures (log.map Sigma.fst))) (hHeld : ∀ s ∈ Ex, L.HeldIn D s)
    (hwin : SigningTranscript.NoLeafIndexReused log ∧
      ¬SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature)
    (hverify :
      (honestEval D.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).1 = true)
    (hreads : ∀ e ∈ (honestEval D.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).2,
      e.HeldBy D) :
    D ∈ xmssBad L Ex M := by
  by_contra hnb
  set H := viewOut L.perm D
  have hv : evalWithAnswerFn H
      (verifyWithHash (m := Comp) L.publicKey forgery.message forgery.signature) = true := by
    rw [fst_honestEval] at hverify
    exact hverify
  have hq : QueriesSatisfy H (OnPath L.perm D)
      (verifyWithHash (m := Comp) L.publicKey forgery.message forgery.signature) := by
    intro q hq e he
    exact hreads e (by rw [snd_honestEval]; exact List.mem_flatMap.2 ⟨q, hq, he⟩)
  set idx := forgery.signature.leafIndex
  simp only [verifyWithHash, evalWithAnswerFn_bind] at hv
  simp only [verifyWithHash] at hq
  obtain ⟨hqb, hq⟩ := queriesSatisfy_bind_iff.1 hq
  split at hv
  · next R hb =>
    rw [hb] at hq
    dsimp only at hq hv
    rw [evalWithAnswerFn_bind] at hv
    obtain ⟨hqt, -⟩ := queriesSatisfy_bind_iff.1 hq
    split at hv
    · next R' ht =>
      simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hv
      -- The top layer: a signed top key's layer, on the honest bottom root.
      have he1 := keyIndexOnLayer_lt idx topLayer
      have hdiv1 : (keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight = 0 :=
        Nat.div_eq_of_lt he1
      have hrt : evalWithAnswerFn H (layerRootWithHash (m := Comp) L.param topLayer
          (keyIndexOnLayer idx topLayer) (littleEndianBytes 16 R) (forgery.signature.layers topLayer)) =
          some (L.treeValue topLayer layerHeight
            ((keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv1]
        exact ht.trans (congrArg some hv)
      obtain ⟨r1, -, hkey1, hmsg1, hsig1⟩ := layer_meet hM hEx hHeld hwin.1 hnb he1
        ⟨(length_littleEndianBytes 16 R).ge, (length_littleEndianBytes 16 R).le.trans (by norm_num)⟩
        hqt hrt
      rw [layerMessage_top] at hmsg1
      have hR : R = L.treeValue bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val := by
        rw [littleEndianBytes_injective 16 hmsg1, HonestTable.bottomRoot, hkey1]
      -- The bottom layer: a signed request's layer, on the forged message.
      have he0 := keyIndexOnLayer_lt idx bottomLayer
      have hdiv0 : (keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight =
          (keyIndexOnLayer idx topLayer).val := by
        simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
      have hrb : evalWithAnswerFn H (layerRootWithHash (m := Comp) L.param bottomLayer
          (keyIndexOnLayer idx bottomLayer) (littleEndianBytes 32 forgery.message)
          (forgery.signature.layers bottomLayer)) =
          some (L.treeValue bottomLayer layerHeight
            ((keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv0, ← hR]
        exact hb
      obtain ⟨r0, hr0, hkey0, hmsg0, hsig0⟩ := layer_meet hM hEx hHeld hwin.1 hnb he0
        ⟨(length_littleEndianBytes 32 _).ge.trans' (by norm_num),
          (length_littleEndianBytes 32 _).le⟩ hqb hrb
      rw [layerMessage_bottom] at hmsg0
      have hidx : r0.1.leafIndex = idx := Fin.ext (by
        have := congrArg Fin.val hkey0
        simpa [keyIndexOnLayer, bottomLayer] using this)
      have hm : r0.1.message = forgery.message := (littleEndianBytes_injective 32 hmsg0).symm
      -- The forgery is the signature of that request.
      have hsig : L.signature r0.1 = some forgery.signature := by
        rw [HonestTable.signature, hidx, hm, hsig0, Option.bind_some,
          show L.bottomRoot idx = R from hR.symm, hsig1, Option.map_some, signature_eq_layers]
      exact hwin.2 ⟨r0, hr0, hm, (hlog r0 hr0).trans hsig⟩
    · simp at hv
  · simp at hv

end Layers

end Quantum.Xmss

end
