module

public import Quantum.StdModel.Xmss.PrfRed
public import Quantum.StdModel.Xmss.EncRed
public import Quantum.StdModel.Xmss.CpreRed
public import Quantum.StdModel.Xmss.TcrRed
public import Common.CostCombinators
public import Common.Lemmas
public import Common.Rerun

@[expose] public section

/-!
# The honest work of the leanXMSS reductions, and their calls at the challenge tweaks

The charge corollaries of the reductions B1 to B4 (`isChargeBound_prfRed`, `isChargeBound_encRed`,
`isChargeBound_cpreRed`, `isChargeBound_tcrRed`) take bounds on the world calls of each
reduction's setup, handler and output. This file proves them, for every world and every weight
on the world's queries, in units of the reductions' own hash calls, then instantiates them.

Units. A reduction hashes only four kinds of input: chain steps, leaves, tree nodes and message
digests (`slotInput` of `.chain`, `.leaf`, `.node`, `.msg`). `KindBound hash w a` bounds the weight
`w` of one hash call of each kind (`a : Kinds`); every bound below is a linear form in `a`.

* `romKinds`: in the QROM a hash call is one query, `a = ⟨1, 1, 1, 1⟩`.
* `keccakKinds`: over Keccak-f (`keccakWorld`, `rpmWorld`) a call costs its blocks
  `⌊n / 136⌋ + 1`, `a = ⟨1, 8, 1, 1⟩` (64-byte chain steps and nodes, 960-byte leaves, 64- or
  80-byte digests).
* Coins weigh nothing in either (`CoinsFree`); SM-TCR-C layouts at any tweak are bounded by
  `TcrBound` (a leaf target as a leaf, a node target as a node).

Counts (setup `c₀`, handler `k` per signing request, output `c₁`), as forms in `a`
(`cost_prfPre`, `cost_prfSigner`, `cost_prfPost`, …, `cost_tcrPost`), then in the QROM and
over Keccak-f (`prfCosts_rom`, `prfCosts_keccak`, …). `treeNodeCost` is a whole tree of `2^16`
key leaves (58 chains of 3 steps and the leaf) and `2^16 - 1` nodes; the abstract signer
recomputes each authentication-path node's subtree (`signCost`); grinding makes at most
`randomizerAttemptLimit = 2^32` digests per encoding.

* B1: the top tree; the signer; two layer roots. QROM 11534335, 8624537563, 384; Keccak-f
  11993087, 8625913805, 398.
* B2: the top tree; the bottom tree, two grindings and the signer; a digest and a layer root.
  QROM 11534335, 8636071898, 193; Keccak-f 11993087, 8637906892, 200.
* B3 (chain values from the challenger): the top tree without chains; the signer without
  chains; a layer root and the readings of both layers. QROM 131071, 8590327771, 890; Keccak-f
  589823, 8591704013, 897.
* B4 (leaves and nodes from the challenger): nothing; the signer without leaves and nodes; the
  candidates of both layers and their digests. QROM 0, 8624144384, 818; Keccak-f 0, 8624144384,
  853.

The charge corollaries at these numerals (`isChargeBound_prfRed_rom`, …,
`isChargeBound_tcrRed_keccak`): if `A` makes at most `n` hash calls and `m` signing calls, B
makes at most `n + k m + (c₀ + c₁)`.

**Calls at the challenge tweaks (design R3).** In the QROM the weight `slotCost S` counts the
random-oracle queries whose input names a slot in `S` (`Qrom.Xmss.slotOf`); every other query of
the reduction is at a slot outside `S`. With `S` the challenge slots of each property:

* B1, `prfSlots` (the inputs keyed by `S_0` or `S`: `.seed`, `.param`, `.prf`, `.rnd`): none
  (`prfRed_onChallenge`); B1 asks the PRF port for every keyed value.
* B2, `msgSlots`: its own grinding at tweaks already sent to the challenger, `2 · 2^32` per
  request, and 2 in the output (`encRed_onChallenge`); none in the setup.
* B3, `chainSlots`: only the output's walks (the honest walks above openings and the
  verification walks), 870 (`cpreRed_onChallenge`); its setup and handler read every chain value
  from the challenger.
* B4, `treeSlots` (`.leaf`, `.node`): only the output, after the reveal, 293
  (`tcrRed_onChallenge`); its setup asks every leaf and node as a target, its handler reads them
  back.
-/

open OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot)
open Quantum.Qrom.Xmss (slotInput Payload Addressable length_thInput_eq length_digestsPayload)

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props Common

-- A bound on a whole tree, or on a hash of a long input, is otherwise unfolded by `whnf`.
attribute [local irreducible] QueryCostAtMost Gen.treeNode grind preTrees sequenceFin walkChain
  foldPath

/-! ## Weights on a reduction's oracles -/

section Weights

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- A weight on the world's queries, extended by `0` on the challenger's queries. -/
def sumCost (w : ι → ℕ) : ι ⊕ ι' → ℕ
  | .inl t => w t
  | .inr _ => 0

/-- A reduction's world calls are the sum weight of the world's port calls. -/
theorem hcallCost_eq_sumCost (W : OracleWorld) {Q' : Type} (R' : OracleSpec.{0, 0} Q') :
    hcallCost W (R' := R') = sumCost W.cost := by
  funext t
  rcases t with t | q <;> rfl

/-- A computation lifted to the left of a sum keeps its weight. -/
theorem cost_liftComp (w : ι → ℕ) {α : Type} {oa : OracleComp spec α} {n : ℕ}
    (h : QueryCostAtMost oa w n) :
    QueryCostAtMost (liftComp oa (spec + spec')) (sumCost w) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => exact isWeightBound_pure _ _ _
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    change QueryCostAtMost (liftM ((spec + spec').query (.inl t)) >>= fun u ↦
      liftComp (k u) (spec + spec')) (sumCost w) n
    exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨h.1, fun u ↦ ih u (h.2 u)⟩

/-- A computation simulated by the left queries of a sum keeps its weight. -/
theorem cost_simulateQ_inl (w : ι → ℕ) {α : Type} {oa : OracleComp spec α} {n : ℕ}
    (h : QueryCostAtMost oa w n) :
    QueryCostAtMost (simulateQ (fun t ↦ (liftM ((spec + spec').query (.inl t)) :
      OracleComp (spec + spec') _)) oa) (sumCost w) n :=
  isWeightBound_simulateQ _ w (sumCost w) (fun t ↦ isWeightBound_query (sumCost w) (.inl t)) h

/-- A challenger query weighs nothing. -/
theorem cost_inr (w : ι → ℕ) (q : ι') :
    QueryCostAtMost (liftM ((spec + spec').query (.inr q)) : OracleComp (spec + spec') _)
      (sumCost w) 0 :=
  isWeightBound_query (sumCost w) (.inr q)

/-- A map keeps the queries. -/
theorem cost_map_iff {α β : Type} (f : α → β) (oa : OracleComp spec α) (w : ι → ℕ) (n : ℕ) :
    QueryCostAtMost (f <$> oa) w n ↔ QueryCostAtMost oa w n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a =>
    rw [map_pure]
    exact ⟨fun _ ↦ isWeightBound_pure _ _ _, fun _ ↦ isWeightBound_pure _ _ _⟩
  | query_bind t k ih =>
    rw [map_bind, isWeightBound_query_bind_iff, isWeightBound_query_bind_iff]
    exact and_congr_right fun _ ↦ forall_congr' fun u ↦ ih u _

theorem cost_dite {p : Prop} [Decidable p] {α : Type} {x : p → OracleComp spec α}
    {y : ¬p → OracleComp spec α} {w : ι → ℕ} {n : ℕ} (hx : ∀ h, QueryCostAtMost (x h) w n)
    (hy : ∀ h, QueryCostAtMost (y h) w n) : QueryCostAtMost (dite p x y) w n := by
  split
  · exact hx _
  · exact hy _

theorem cost_bind_pure {α β : Type} {oa : OracleComp spec α} {f : α → β} {w : ι → ℕ} {n : ℕ}
    (h : QueryCostAtMost oa w n) : QueryCostAtMost (oa >>= fun x ↦ pure (f x)) w n :=
  (h.bind fun x ↦ isWeightBound_pure (f x) w 0).mono (Nat.add_zero n).le

/-- `sequenceFin` weighs the sum of its steps' bounds. -/
theorem cost_sequenceFin_sum {w : ι → ℕ} {α : Type} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α) (b : Fin n → ℕ),
      (∀ i, QueryCostAtMost (c i) w (b i)) → QueryCostAtMost (sequenceFin c) w (∑ i, b i)
  | 0, c, b, _ => by
    simp only [sequenceFin]
    exact isWeightBound_pure _ _ _
  | n + 1, c, b, h => by
    simp only [sequenceFin]
    refine ((h 0).bind fun _ ↦ (cost_sequenceFin_sum (fun i : Fin n ↦ c i.succ)
      (fun i ↦ b i.succ) (fun i ↦ h i.succ)).bind fun _ ↦ isWeightBound_pure _ w 0).mono ?_
    rw [Fin.sum_univ_succ]
    omega

/-- The world's coins weigh nothing. -/
def CoinsFree (W : OracleWorld) (w : W.Oracles.Domain → ℕ) : Prop :=
  ∀ n, w (.inl n) = 0

theorem cost_sample (W : OracleWorld) {w : W.Oracles.Domain → ℕ} (hw : CoinsFree W w)
    (α : Type) [SampleableType α] : QueryCostAtMost (sample W α) w 0 :=
  isWeightBound_liftM_probComp w hw _

end Weights

/-! ## Hash calls by kind -/

/-- Bounds per hash call of the four kinds the reductions make. -/
structure Kinds where
  /-- A chain step. -/
  chain : ℕ
  /-- A leaf. -/
  leaf : ℕ
  /-- A tree node. -/
  node : ℕ
  /-- A message digest. -/
  msg : ℕ

section Kind

variable {ι ι' : Type} {spec : OracleSpec.{0, 0} ι} {spec' : OracleSpec.{0, 0} ι'}

/-- **A hash within the bounds `a`** under the weight `w`: a chain step, a leaf, a node and a
message digest of a layer's message weigh at most `a.chain`, `a.leaf`, `a.node`, `a.msg`. -/
structure KindBound (hash : HashInput → OracleComp spec HashOutput) (w : ι → ℕ) (a : Kinds) :
    Prop where
  chain : ∀ (P : PublicParameter) (l : Layer) (e : KeyIndex) (s : ChainStep) (i : ChainIndex)
    (v : Digest), QueryCostAtMost (hash (slotInput P (.chain l e s i) v)) w a.chain
  leaf : ∀ (P : PublicParameter) (l : Layer) (e : KeyIndex) (ends : ChainIndex → Digest),
    QueryCostAtMost (hash (slotInput P (.leaf l e) ends)) w a.leaf
  node : ∀ (P : PublicParameter) (l : Layer) (k j : ℕ) (c : Payload (.node l k j)),
    QueryCostAtMost (hash (slotInput P (.node l k j) c)) w a.node
  msg : ∀ (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg) (ρ : Randomizer),
    QueryCostAtMost (hash (slotInput P (.msg l e) (M.mb, ρ))) w a.msg

variable {hash : HashInput → OracleComp spec HashOutput} {w : ι → ℕ} {a : Kinds}

theorem KindBound.lift (hb : KindBound hash w a) :
    KindBound (fun x ↦ liftComp (hash x) (spec + spec')) (sumCost w) a :=
  ⟨fun P l e s i v ↦ cost_liftComp w (hb.chain P l e s i v),
    fun P l e ends ↦ cost_liftComp w (hb.leaf P l e ends),
    fun P l k j c ↦ cost_liftComp w (hb.node P l k j c),
    fun P l e M ρ ↦ cost_liftComp w (hb.msg P l e M ρ)⟩

theorem KindBound.sim (hb : KindBound hash w a) :
    KindBound (fun x ↦ simulateQ (fun t ↦ (liftM ((spec + spec').query (.inl t)) :
      OracleComp (spec + spec') _)) (hash x)) (sumCost w) a :=
  ⟨fun P l e s i v ↦ cost_simulateQ_inl w (hb.chain P l e s i v),
    fun P l e ends ↦ cost_simulateQ_inl w (hb.leaf P l e ends),
    fun P l k j c ↦ cost_simulateQ_inl w (hb.node P l k j c),
    fun P l e M ρ ↦ cost_simulateQ_inl w (hb.msg P l e M ρ)⟩

theorem KindBound.map {hash' : HashInput → OracleComp spec HashOutput}
    (hb : KindBound hash w a) (h : ∀ x n, QueryCostAtMost (hash x) w n →
      QueryCostAtMost (hash' x) w n) : KindBound hash' w a :=
  ⟨fun P l e s i v ↦ h _ _ (hb.chain P l e s i v), fun P l e ends ↦ h _ _ (hb.leaf P l e ends),
    fun P l k j c ↦ h _ _ (hb.node P l k j c), fun P l e M ρ ↦ h _ _ (hb.msg P l e M ρ)⟩

/-! ### The scheme's hashing -/

variable (hb : KindBound hash w a)
include hb

theorem cost_chainStep (P : PublicParameter) (l : Layer) (e : KeyIndex) (s : ChainStep)
    (i : ChainIndex) (v : Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.tweakableHash hash P (.chain l e s)
      (Verification.chainPayload i v)) w a.chain := by
  rw [xmss_chainStep_eq]
  exact cost_bind_pure (hb.chain P l e s i v)

theorem cost_leafHash (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (ends : ChainIndex → Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.leafHash hash P l e ends) w a.leaf := by
  rw [xmss_leaf_eq]
  exact cost_bind_pure (hb.leaf P l e ends)

theorem cost_node (P : PublicParameter) (l : Layer) (k j : ℕ) (x y : Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.tweakableHash hash P (.node l k j) (nodePayload x y)) w
      a.node := by
  rw [xmss_node_eq]
  exact cost_bind_pure (hb.node P l k j (x, y))

theorem cost_messageDigest (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg)
    (ρ : Randomizer) :
    QueryCostAtMost (Qrom.Xmss.Over.messageDigest hash P l e M.bytes ρ) w a.msg := by
  show QueryCostAtMost (Qrom.Xmss.Over.messageDigest hash P l e M.mb.1 ρ) w a.msg
  rw [xmss_messageDigest_eq]
  exact cost_bind_pure (hb.msg P l e M ρ)

theorem cost_chainWalk (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (s n : ℕ) (v : Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.chainWalk hash P l e i s n v) w (n * a.chain) := by
  unfold Qrom.Xmss.Over.chainWalk
  exact Common.walkChain_cost _ a.chain (fun t v ↦ cost_chainStep hb P l e t i v) s n v

theorem cost_grind (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg)
    (r0 : Randomizer) : ∀ n t : ℕ,
    QueryCostAtMost (grind hash P l e M.bytes r0 n t) w (n * a.msg)
  | 0, t => by
    rw [grind]
    exact isWeightBound_pure _ _ _
  | n + 1, t => by
    rw [grind]
    refine ((cost_messageDigest hb P l e M _).bind (b := n * a.msg) fun d ↦ ?_).mono
      (le_of_eq (by ring))
    split
    · exact isWeightBound_pure _ _ _
    · exact cost_grind P l e M r0 n (t + 1)

theorem cost_recoverChain (P : PublicParameter) (l : Layer) (e : KeyIndex) (i : ChainIndex)
    (d : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.recoverChain hash P l e i d v) w
      ((chainLength - 1) * a.chain) := by
  unfold Qrom.Xmss.Over.recoverChain
  exact (cost_chainWalk hb P l e i _ _ v).mono (Nat.mul_le_mul_right _ (Nat.sub_le _ _))

theorem cost_treeFold (P : PublicParameter) (l : Layer) (e : KeyIndex)
    (path : Fin layerHeight → Digest) (k : ℕ) (v : Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.treeFold hash P l e path k v) w (k * a.node) := by
  unfold Qrom.Xmss.Over.treeFold
  exact Common.foldPath_cost _ a.node (fun lv j x y ↦ cost_node hb P l (lv + 1) j x y) _ _ k v

theorem cost_otsLeaf (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg)
    (ρ : Randomizer) (vals : ChainIndex → Digest) :
    QueryCostAtMost (Qrom.Xmss.Over.otsLeaf hash P l e M.bytes ρ vals) w
      (a.msg + (chainCount * ((chainLength - 1) * a.chain) + a.leaf)) := by
  unfold Qrom.Xmss.Over.otsLeaf
  refine (cost_messageDigest hb P l e M ρ).bind fun d ↦ ?_
  split
  · exact (Common.sequenceFin_cost _ _ fun i ↦ cost_recoverChain hb P l e i _ _).bind fun _ ↦
      cost_bind_pure (cost_leafHash hb P l e _)
  · exact isWeightBound_pure _ _ _

/-- The hash calls of a layer's root: the digest, the chains up from the signature's values, the
leaf and the path. -/
def layerRootCost (a : Kinds) : ℕ :=
  a.msg + (chainCount * ((chainLength - 1) * a.chain) + a.leaf) + layerHeight * a.node

theorem cost_layerRoot (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg)
    (σ : LayerSignature) :
    QueryCostAtMost (Qrom.Xmss.Over.layerRoot hash P l e M.bytes σ) w (layerRootCost a) := by
  unfold Qrom.Xmss.Over.layerRoot
  refine (cost_otsLeaf hb P l e M _ _).bind fun r ↦ ?_
  split
  · exact cost_bind_pure (cost_treeFold hb P l e _ _ _)
  · exact isWeightBound_pure _ _ _

theorem cost_verify (pk : PublicKey) (msg : Message) (sig : Signature) :
    QueryCostAtMost (Qrom.Xmss.Over.verify hash pk msg sig) w
      (layerRootCost a + layerRootCost a) := by
  unfold Qrom.Xmss.Over.verify
  dsimp only
  refine (cost_layerRoot hb _ _ _ (.inl msg) _).bind fun r ↦ ?_
  split
  · refine ((cost_layerRoot hb _ _ _ (.inr _) _).bind fun r' ↦ ?_).mono (Nat.add_zero _).le
    split <;> exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

end Kind

/-! ## The abstract signer -/

section Signer

variable {ι : Type} {spec : OracleSpec.{0, 0} ι}

/-- **Operations within the bounds `b`**: a chain value up to the end, a leaf, a node and an
encoding weigh at most `b.chain`, `b.leaf`, `b.node`, `b.msg`. -/
structure OpsBound (o : Ops (OracleComp spec)) (w : ι → ℕ) (b : Kinds) : Prop where
  chain : ∀ l e i μ, μ ≤ chainLength - 1 → QueryCostAtMost (o.chain l e i μ) w b.chain
  leaf : ∀ l e ends, QueryCostAtMost (o.leaf l e ends) w b.leaf
  node : ∀ l k j x y, QueryCostAtMost (o.node l k j x y) w b.node
  encode : ∀ e M, QueryCostAtMost (o.encode e M) w b.msg

/-- A key's leaf: its chain ends and the leaf. -/
def keyLeafCost (b : Kinds) : ℕ :=
  chainCount * b.chain + b.leaf

/-- The tree of height `k`: `2^k` key leaves and `2^k - 1` nodes. -/
def treeNodeCost (b : Kinds) (k : ℕ) : ℕ :=
  2 ^ k * keyLeafCost b + (2 ^ k - 1) * b.node

/-- An authentication path, each node's subtree recomputed. -/
def treePathCost (b : Kinds) : ℕ :=
  (2 ^ layerHeight - 1) * keyLeafCost b + (2 ^ layerHeight - 1 - layerHeight) * b.node

/-- One layer's signature: the encoding, the openings and the path. -/
def signLayerCost (b : Kinds) : ℕ :=
  b.msg + (chainCount * b.chain + treePathCost b)

/-- The signer: two layers and the bottom root. -/
def signCost (b : Kinds) : ℕ :=
  signLayerCost b + (treeNodeCost b layerHeight + signLayerCost b)

theorem sum_treeNodeCost (b : Kinds) :
    ∑ k : Fin layerHeight, treeNodeCost b k = treePathCost b := by
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ treeNodeCost b k) layerHeight]
  simp only [layerHeight, Finset.sum_range_succ, Finset.sum_range_zero, treeNodeCost,
    treePathCost]
  norm_num
  ring

variable {o : Ops (OracleComp spec)} {w : ι → ℕ} {b : Kinds} (ho : OpsBound o w b)
include ho

theorem cost_keyLeaf (l : Layer) (e : KeyIndex) :
    QueryCostAtMost (Gen.keyLeaf o l e) w (keyLeafCost b) := by
  unfold Gen.keyLeaf Gen.otsPublicKey
  exact (Common.sequenceFin_cost _ _ fun i ↦ ho.chain l e i _ le_rfl).bind fun ends ↦
    ho.leaf l e ends

theorem cost_treeNode (l : Layer) : ∀ k j : ℕ,
    QueryCostAtMost (Gen.treeNode o l k j) w (treeNodeCost b k)
  | 0, j => by
    rw [Gen.treeNode]
    exact (cost_keyLeaf ho l _).mono (by simp [treeNodeCost])
  | k + 1, j => by
    rw [Gen.treeNode]
    refine ((cost_treeNode l k (2 * j)).bind fun _ ↦ (cost_treeNode l k (2 * j + 1)).bind
      fun _ ↦ ho.node l k j _ _).mono ?_
    obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 :=
      ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
    have h2 : 2 ^ (k + 1) = 2 * q + 2 := by rw [pow_succ, hq]; ring
    simp only [treeNodeCost, hq, h2, Nat.add_sub_cancel, show 2 * q + 2 - 1 = 2 * q + 1 by omega]
    apply le_of_eq
    ring

theorem cost_treePath (l : Layer) (e : KeyIndex) :
    QueryCostAtMost (Gen.treePath o l e) w (treePathCost b) := by
  unfold Gen.treePath
  rw [← sum_treeNodeCost]
  exact cost_sequenceFin_sum _ _ fun k ↦ cost_treeNode ho l k.val _

theorem cost_root : QueryCostAtMost (Gen.root o) w (treeNodeCost b layerHeight) :=
  cost_treeNode ho topLayer layerHeight 0

theorem cost_signLayer (e : KeyIndex) (M : LayerMsg) :
    QueryCostAtMost (Gen.signLayer o e M) w (signLayerCost b) := by
  unfold Gen.signLayer
  refine (ho.encode e M).bind fun r ↦ ?_
  split
  · split
    · exact ((Common.sequenceFin_cost _ _ fun i ↦ ho.chain _ e i _
        (Nat.le_sub_one_of_lt (Fin.isLt _))).bind fun _ ↦
          cost_bind_pure (cost_treePath ho _ e))
    · exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

theorem cost_sign (idx : LeafIndex) (msg : Message) :
    QueryCostAtMost (Gen.sign o idx msg) w (signCost b) := by
  unfold Gen.sign
  refine (cost_signLayer ho _ _).bind fun r ↦ ?_
  split
  · refine (cost_treeNode ho _ _ _).bind fun _ ↦ ?_
    refine ((cost_signLayer ho _ _).bind fun r' ↦ ?_).mono (Nat.add_zero _).le
    split <;> exact isWeightBound_pure _ _ _
  · exact isWeightBound_pure _ _ _

theorem cost_preTrees : ∀ n : ℕ,
    QueryCostAtMost (preTrees o n) w (n * treeNodeCost b layerHeight)
  | 0 => by
    rw [preTrees]
    exact isWeightBound_pure _ _ _
  | n + 1 => by
    rw [preTrees]
    refine ((cost_preTrees n).bind fun _ ↦
      cost_bind_pure (cost_treeNode ho bottomLayer layerHeight n)).mono (le_of_eq (by ring))

end Signer

/-! ## The worlds -/

section Worlds

/-- A hash call in the QROM: one query. -/
def romKinds : Kinds := ⟨1, 1, 1, 1⟩

/-- A hash call over Keccak-f: its blocks. -/
def keccakKinds : Kinds := ⟨1, 8, 1, 1⟩

theorem cost_hashQ (l : HashInput) : QueryCostAtMost (Qrom.hashQ l) Qrom.hashCallCost 1 := by
  unfold Qrom.hashQ
  split
  · exact isWeightBound_query _ _
  · exact isWeightBound_pure _ _ _

theorem romWorld_hash_eq (l : HashInput) : romWorld.hash l = Qrom.hashQ l :=
  rfl

theorem romWorld_hash_cost (l : HashInput) : QueryCostAtMost (romWorld.hash l) romWorld.cost 1 :=
  cost_hashQ l

/-- **The QROM's hash calls**: one query each. -/
theorem romWorld_kinds : KindBound romWorld.hash romWorld.cost romKinds :=
  ⟨fun _ _ _ _ _ _ ↦ romWorld_hash_cost _, fun _ _ _ _ ↦ romWorld_hash_cost _,
    fun _ _ _ _ _ ↦ romWorld_hash_cost _, fun _ _ _ _ _ ↦ romWorld_hash_cost _⟩

theorem romWorld_coinsFree : CoinsFree romWorld romWorld.cost :=
  fun _ ↦ rfl

section Keccak

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℕ}

open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (absorbWith absorbBlockWith)

theorem cost_absorbWith {π : KeccakState → OracleComp spec KeccakState}
    (hπ : ∀ s, QueryCostAtMost (π s) w 1) :
    ∀ (n : ℕ) (s : KeccakState) (d : List UInt8),
      QueryCostAtMost (absorbWith π n s d) w (n + 1)
  | 0, s, d => by
    rw [absorbWith, absorbBlockWith]
    exact hπ _
  | n + 1, s, d => by
    rw [absorbWith, absorbBlockWith]
    exact ((hπ _).bind fun s' ↦ cost_absorbWith hπ n s' _).mono (by omega)

/-- Keccak-256 over a permutation call of weight one: `⌊n / 136⌋ + 1` for `n` bytes. -/
theorem cost_keccakHash {π : KeccakState → OracleComp spec KeccakState}
    (hπ : ∀ s, QueryCostAtMost (π s) w 1) (l : HashInput) :
    QueryCostAtMost (keccakHash π l) w (l.length / 136 + 1) := by
  unfold keccakHash LeanVM.Protocol.KeccakHash.keccak256With
  exact isWeightBound_map _ (cost_bind_pure (cost_absorbWith hπ _ _ _))

/-- **Keccak-256's blocks** on the inputs of the reductions. -/
theorem kindBound_keccak {hash : HashInput → OracleComp spec HashOutput}
    (h : ∀ l, QueryCostAtMost (hash l) w (l.length / 136 + 1)) :
    KindBound hash w keccakKinds where
  chain P l e s i v := (h _).mono (by
    change (thInput P _ (Verification.chainPayload i v)).length / 136 + 1 ≤ 1
    rw [length_thInput_eq]
    simp [Verification.chainPayload, littleEndianBytes])
  leaf P l e ends := (h _).mono (by
    change (thInput P _ (digestsPayload ends)).length / 136 + 1 ≤ 8
    rw [length_thInput_eq, length_digestsPayload]
    simp [chainCount])
  node P l k j c := (h _).mono (by
    change (thInput P _ (nodePayload c.1 c.2)).length / 136 + 1 ≤ 1
    rw [length_thInput_eq]
    simp [nodePayload, littleEndianBytes])
  msg P l e M ρ := (h _).mono (by
    change (thInput P _ (M.bytes ++ littleEndianBytes 16 ρ)).length / 136 + 1 ≤ 1
    rw [length_thInput_eq]
    cases M <;> simp [LayerMsg.bytes, littleEndianBytes])

end Keccak

/-- **The standard model's hash**: `⌊n / 136⌋ + 1` Keccak-f calls on `n` bytes. -/
theorem keccakWorld_hash_cost : ∀ l : HashInput,
    QueryCostAtMost (keccakWorld.hash l) keccakWorld.cost (l.length / 136 + 1) :=
  cost_keccakHash fun _ ↦ isWeightBound_map _ (isWeightBound_query _ _)

/-- **The standard model's hash calls**: Keccak-256 over Keccak-f, its blocks each. -/
theorem keccakWorld_kinds : KindBound keccakWorld.hash keccakWorld.cost keccakKinds :=
  kindBound_keccak keccakWorld_hash_cost

theorem keccakWorld_coinsFree : CoinsFree keccakWorld keccakWorld.cost :=
  fun _ ↦ rfl

/-- **The QRPM's hash**: `⌊n / 136⌋ + 1` calls of the permutation on `n` bytes. -/
theorem rpmWorld_hash_cost (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) (l : HashInput) :
    QueryCostAtMost ((rpmWorld S e).hash l) (rpmWorld S e).cost (l.length / 136 + 1) :=
  Common.keccakHash_cost l

/-- **The QRPM's hash calls**: Keccak-256 over the permutation, its blocks each. -/
theorem rpmWorld_kinds (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) :
    KindBound (rpmWorld S e).hash (rpmWorld S e).cost keccakKinds :=
  kindBound_keccak (rpmWorld_hash_cost S e)

theorem rpmWorld_coinsFree (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) : CoinsFree (rpmWorld S e) (rpmWorld S e).cost :=
  fun _ ↦ rfl

/-! ### Counting the queries at given slots -/

/-- **The weight of the random-oracle queries at the slots `S`**: one for a query whose input
names a slot in `S` (`Qrom.Xmss.slotOf`), nothing for any other query or coin. -/
def slotCost (S : Slot → Bool) : Qrom.RomOracles.Domain → ℕ
  | .inl _ => 0
  | .inr x => if (Qrom.Xmss.slotOf x).any S then 1 else 0

/-- The KIM-PRF's challenge slots: the inputs keyed by `S_0` or `S`. -/
def prfSlots : Slot → Bool
  | .seed | .param | .prf .. | .rnd .. => true
  | _ => false

/-- The EncTCR$ challenge slots: the message digests. -/
def msgSlots : Slot → Bool
  | .msg .. => true
  | _ => false

/-- The CPRE challenge slots: the chain steps. -/
def chainSlots : Slot → Bool
  | .chain .. => true
  | _ => false

/-- The SM-TCR-C challenge slots: the leaves and the nodes. -/
def treeSlots : Slot → Bool
  | .leaf .. | .node .. => true
  | _ => false

theorem cost_slotInput (S : Slot → Bool) (P : PublicParameter) {s : Slot} (hs : Addressable s)
    (d : Payload s) :
    QueryCostAtMost (Qrom.hashQ (slotInput P s d)) (slotCost S) (if S s then 1 else 0) := by
  rw [Qrom.Xmss.hashQ_slotInput]
  refine (isWeightBound_query (slotCost S) (.inr (Qrom.Xmss.cell P s d))).mono (le_of_eq ?_)
  simp only [slotCost, Qrom.Xmss.slotOf_cell P hs d, Option.any_some]

/-- Every node input names a node slot. -/
theorem slotOf_cell_node (P : PublicParameter) (l : Layer) (k j : ℕ) (c : Payload (.node l k j)) :
    ∃ l' k' j', Qrom.Xmss.slotOf (Qrom.Xmss.cell P (.node l k j) c) = some (.node l' k' j') := by
  have hl : (nodePayload c.1 c.2).length = 32 := by
    simp only [nodePayload, littleEndianBytes, List.length_append, List.length_ofFn]
  rw [Qrom.Xmss.slotOf, Qrom.Xmss.decodeInput_cell]
  change ∃ l' k' j', Qrom.Xmss.slotOfInput (thInput P _ (nodePayload c.1 c.2)) = _
  rw [Qrom.Xmss.slotOfInput_thInput _ _ _ (by omega),
    Quantum.Xmss.slotOfAddress_self _ _ _ (by show BitVec.ofNat 5 3 ≠ 5; decide)]
  simp [Quantum.Xmss.fieldsSlot, hashDomainFields, tweakFields]

/-- **Counting the queries at the slots `S`** by kind: a hash call of a kind weighs one if `S`
contains a slot of that kind. -/
theorem slotCost_kinds (S : Slot → Bool) (a : Kinds)
    (hc : ∀ l e s i, (if S (.chain l e s i) then 1 else 0) ≤ a.chain)
    (hl : ∀ l e, (if S (.leaf l e) then 1 else 0) ≤ a.leaf)
    (hn : ∀ l k j, (if S (.node l k j) then 1 else 0) ≤ a.node)
    (hm : ∀ l e, (if S (.msg l e) then 1 else 0) ≤ a.msg) :
    KindBound romWorld.hash (slotCost S) a where
  chain P l e s i v := by
    rw [romWorld_hash_eq]
    exact (cost_slotInput S P trivial (s := .chain l e s i) v).mono (hc l e s i)
  leaf P l e ends := by
    rw [romWorld_hash_eq]
    exact (cost_slotInput S P trivial (s := .leaf l e) ends).mono (hl l e)
  node P l k j c := by
    rw [romWorld_hash_eq, Qrom.Xmss.hashQ_slotInput]
    refine (isWeightBound_query (slotCost S) (.inr (Qrom.Xmss.cell P _ c))).mono ?_
    obtain ⟨l', k', j', h⟩ := slotOf_cell_node P l k j c
    simp only [slotCost, h, Option.any_some]
    exact hn l' k' j'
  msg P l e M ρ := by
    rw [romWorld_hash_eq]
    exact (cost_slotInput S P trivial (s := .msg l e) (M.mb, ρ)).mono (hm l e)

theorem slotCost_coinsFree (S : Slot → Bool) : CoinsFree romWorld (slotCost S) :=
  fun _ ↦ rfl

end Worlds

/-! ## B1 -/

section Prf

variable {W : OracleWorld} {w : W.Oracles.Domain → ℕ} {a : Kinds} (hb : KindBound W.hash w a)
include hb

/-- B1's operations: the chain walks from PRF answers, grinding to the cap. -/
def prfKinds (a : Kinds) : Kinds :=
  ⟨(chainLength - 1) * a.chain, a.leaf, a.node, randomizerAttemptLimit * a.msg⟩

theorem kindBound_prfHash :
    KindBound (prfHash W) (sumCost (ι' := PrfDom) w) a :=
  hb.lift

theorem opsBound_prfOps (P : PublicParameter) :
    OpsBound (prfOps W P) (sumCost (ι' := PrfDom) w) (prfKinds a) where
  chain l e i μ hμ := by
    dsimp only [prfOps]
    exact ((cost_inr w _).bind fun o ↦ cost_chainWalk (kindBound_prfHash hb) P l e i 0 μ _).mono
      (by rw [Nat.zero_add]; exact Nat.mul_le_mul_right _ hμ)
  leaf l e ends := cost_leafHash (kindBound_prfHash hb) P l e ends
  node l k j x y := cost_node (kindBound_prfHash hb) P l (k + 1) j x y
  encode e M := by
    dsimp only [prfOps]
    exact ((cost_inr w _).bind fun o ↦ cost_grind (kindBound_prfHash hb) P _ e M _ _ _).mono
      (Nat.zero_add _).le

/-- B1's setup: the top tree. -/
def prfPreCost (a : Kinds) : ℕ :=
  treeNodeCost (prfKinds a) layerHeight

/-- B1's handler: the signer over its operations. -/
def prfSignCost (a : Kinds) : ℕ :=
  signCost (prfKinds a)

/-- B1's output: verification. -/
def prfPostCost (a : Kinds) : ℕ :=
  layerRootCost a + layerRootCost a

theorem cost_prfPre : QueryCostAtMost (prfPre W) (sumCost w) (prfPreCost a) := by
  unfold prfPre
  exact ((cost_inr w _).bind fun _ ↦ cost_bind_pure (cost_root (opsBound_prfOps hb _))).mono
    (Nat.zero_add _).le

theorem cost_prfSigner (s : PrfSt) (r : SigningRequest) :
    QueryCostAtMost (prfSigner W s r) (sumCost w) (prfSignCost a) := by
  unfold prfSigner
  exact cost_bind_pure (cost_sign (opsBound_prfOps hb _) _ _)

theorem cost_prfPost (pk : PublicKey) (F : Forgery) (s : PrfSt) :
    QueryCostAtMost (prfPost W pk F s) (sumCost w) (prfPostCost a) := by
  unfold prfPost
  exact cost_bind_pure (cost_verify (kindBound_prfHash hb) _ _ _)

end Prf

/-- **B1's hash calls**, for hash calls within `a` and free coins. -/
theorem isChargeBound_prfRed_kinds {W : OracleWorld} {a : Kinds}
    (hb : KindBound W.hash W.cost a)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {n m : ℕ}
    (hn : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IPFunctor.IFreeM.IsChargeBound (prfRed W A u) (cmdCharge hashCharge)
      (prfPreCost a + ((n + prfSignCost a * m) + prfPostCost a)) :=
  isChargeBound_prfRed W A (by rw [hcallCost_eq_sumCost]; exact cost_prfPre hb)
    (fun s q ↦ by rw [hcallCost_eq_sumCost]; exact cost_prfSigner hb s q)
    (fun pk F s ↦ by rw [hcallCost_eq_sumCost]; exact cost_prfPost hb pk F s) hn hm u

/-! ## B2 -/

section Enc

variable {W : OracleWorld} {w : W.Oracles.Domain → ℕ} {a : Kinds} (hb : KindBound W.hash w a)
include hb

/-- B2's honest operations: chain walks from the starts, no encoding. -/
def hKinds (a : Kinds) : Kinds :=
  ⟨(chainLength - 1) * a.chain, a.leaf, a.node, 0⟩

theorem opsBound_hOps (P : PublicParameter) (c : Starts) (enc : KeyIndex → LayerMsg → EncAns) :
    OpsBound (hOps W P c enc) w (hKinds a) where
  chain l e i μ hμ := (cost_chainWalk hb P l e i 0 μ _).mono (Nat.mul_le_mul_right _ hμ)
  leaf l e ends := cost_leafHash hb P l e ends
  node l k j x y := cost_node hb P l (k + 1) j x y
  encode _ _ := isWeightBound_pure _ _ _

/-- The EncTCR$ grinding: one digest per trial. -/
theorem cost_xmssGrind (P : PublicParameter) (l : Layer) (e : KeyIndex) (M : LayerMsg)
    (r0 : Randomizer) : ∀ c n : ℕ,
    QueryCostAtMost (xmssEnc.grind W P (l, e) M.mb r0 c n) w (n * a.msg)
  | c, 0 => by
    rw [SaltEnc.grind]
    exact isWeightBound_pure _ _ _
  | c, n + 1 => by
    rw [SaltEnc.grind]
    refine ((isWeightBound_map _ (hb.msg P l e M _)).bind (b := n * a.msg) fun d ↦ ?_).mono
      (le_of_eq (by ring))
    split
    · exact isWeightBound_pure _ _ _
    · exact cost_xmssGrind P l e M r0 (c + 1) n

variable (hw : CoinsFree W w)
include hw

theorem cost_encStep (P : PublicParameter) (s : EncSt) (e : KeyIndex) (msg : LayerMsg) :
    QueryCostAtMost (encStep W P s e msg) (sumCost w) (randomizerAttemptLimit * a.msg) := by
  unfold encStep
  split
  · exact isWeightBound_pure _ _ _
  · dsimp only
    split
    · exact cost_bind_pure ((cost_inr w _).mono (Nat.zero_le _))
    · exact cost_bind_pure (cost_liftComp w (((cost_sample W hw _).bind fun r0 ↦
        cost_xmssGrind hb P _ e msg r0 0 _).mono (le_of_eq (Nat.zero_add _))))

/-- B2's setup: the top tree. -/
def encPreCost (a : Kinds) : ℕ :=
  treeNodeCost (hKinds a) layerHeight

/-- B2's handler: the bottom root, two encodings at the cap, the signer. -/
def encSignCost (a : Kinds) : ℕ :=
  treeNodeCost (hKinds a) layerHeight + (randomizerAttemptLimit * a.msg +
    (randomizerAttemptLimit * a.msg + signCost (hKinds a)))

/-- B2's output: the bottom digest and the bottom layer's root. -/
def encPostCost (a : Kinds) : ℕ :=
  a.msg + layerRootCost a

theorem cost_encPre (P : PublicParameter) :
    QueryCostAtMost (encPre W P) (sumCost w) (encPreCost a) := by
  unfold encPre
  exact cost_liftComp w (((cost_sample W hw _).bind fun c ↦
    cost_bind_pure (cost_root (opsBound_hOps hb P c noEnc))).mono (le_of_eq (Nat.zero_add _)))

theorem cost_encSign (P : PublicParameter) (s : EncSt) (r : SigningRequest) :
    QueryCostAtMost (encSign W P s r) (sumCost w) (encSignCost a) := by
  unfold encSign
  exact (cost_liftComp w (cost_treeNode (opsBound_hOps hb P s.starts noEnc) _ _ _)).bind
    fun _ ↦ (cost_encStep hb hw P s _ _).bind fun p1 ↦ (cost_encStep hb hw P p1.2 _ _).bind
      fun _ ↦ cost_bind_pure (cost_liftComp w (cost_sign (opsBound_hOps hb P s.starts _) _ _))

omit hw in
theorem cost_encPost (P : PublicParameter) (s0 : Starts × Digest) (F : Forgery) (s : EncSt) :
    QueryCostAtMost (encPost W P s0 F s) (sumCost w) (encPostCost a) := by
  unfold encPost encOut
  dsimp only
  refine cost_liftComp w ((cost_messageDigest hb P bottomLayer _ (.inl F.message) _).bind
    fun _ ↦ ?_)
  split
  · exact isWeightBound_pure _ _ _
  · refine ((cost_layerRoot hb P bottomLayer _ (.inl F.message) _).bind fun r ↦ ?_).mono
      (le_of_eq (Nat.add_zero _))
    split <;> exact isWeightBound_pure _ _ _

end Enc

/-- **B2's hash calls**, for hash calls within `a` and free coins. -/
theorem isChargeBound_encRed_kinds {W : OracleWorld} {a : Kinds}
    (hb : KindBound W.hash W.cost a) (hw : CoinsFree W W.cost)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {n m : ℕ}
    (hn : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m)
    (P : PublicParameter) :
    IPFunctor.IFreeM.IsChargeBound (encRed W A P) (cmdCharge hashCharge)
      (encPreCost a + ((n + encSignCost a * m) + encPostCost a)) :=
  isChargeBound_encRed W A (fun P ↦ by rw [hcallCost_eq_sumCost]; exact cost_encPre hb hw P)
    (fun P s q ↦ by rw [hcallCost_eq_sumCost]; exact cost_encSign hb hw P s q)
    (fun P s0 F s ↦ by rw [hcallCost_eq_sumCost]; exact cost_encPost hb P s0 F s) hn hm P

/-! ## B3 -/

section Cpre

open CpreRed

/-- The value of a program writing CPRE entries, the entries forgotten. -/
def wFst {M : Type → Type} [Monad M] [LawfulMonad M] : WriterT CLog M →ᵐ M where
  toFun _ x := Prod.fst <$> x.run
  toFun_pure' {α} a := by
    show Prod.fst <$> (pure (a, ([] : CLog)) : M (α × CLog)) = pure a
    rw [map_pure]
  toFun_bind' x f := by
    show Prod.fst <$> (x.run >>= fun p ↦ (fun q ↦ (q.1, p.2 ++ q.2)) <$> (f p.1).run) =
      (Prod.fst <$> x.run) >>= fun a ↦ Prod.fst <$> (f a).run
    rw [map_bind, bind_map_left]
    congr 1
    funext p
    rw [Functor.map_map]

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℕ}

theorem cost_run_iff {α : Type} (x : WriterT CLog (OracleComp spec) α) (n : ℕ) :
    QueryCostAtMost x.run w n ↔ QueryCostAtMost (wFst x) w n :=
  (cost_map_iff Prod.fst x.run w n).symm

/-- B3's operations: chain values from the challenger, no hash. -/
def cKinds (a : Kinds) : Kinds :=
  ⟨0, a.leaf, a.node, randomizerAttemptLimit * a.msg⟩

theorem opsBound_bOps {a : Kinds} {hash : HashInput → OracleComp spec HashOutput}
    {val : CJ → ℕ → OracleComp spec Digest} (hb : KindBound hash w a)
    (hv : ∀ j μ, QueryCostAtMost (val j μ) w 0) (P : PublicParameter) (g : Bases) :
    OpsBound (bOps hash val P g) w (cKinds a) where
  chain l e i μ hμ := by
    show QueryCostAtMost (if μ ≤ chainLength - 1 then val (l, e, i) μ else pure 0) w 0
    simp only [hμ, ↓reduceIte]
    exact hv _ _
  leaf l e ends := cost_leafHash hb P l e ends
  node l k j x y := cost_node hb P l (k + 1) j x y
  encode e M := cost_grind hb P _ e M _ _ _

/-- The values the output reads on a forged layer: the digest, the forged chains walked up and
the known values walked up. -/
def readCost (a : Kinds) : ℕ :=
  a.msg + (chainCount * ((chainLength - 1) * a.chain) + chainCount * ((chainLength - 1) * a.chain))

/-- B3's output: the bottom layer's root and the readings of both layers. -/
def cprePostCost (a : Kinds) : ℕ :=
  layerRootCost a + 2 * readCost a

theorem sum_layer (f : Layer → ℕ) : ∑ l : Layer, f l = f bottomLayer + f topLayer :=
  Fin.sum_univ_two f

section Pick

variable {a : Kinds} {hash : HashInput → OracleComp spec HashOutput} (hb : KindBound hash w a)
include hb

theorem cost_knownG (P : PublicParameter) (rec : CLog) (j : CJ) {μ : ℕ}
    (hμ : μ ≤ chainLength - 1) :
    QueryCostAtMost (knownG hash P rec j μ) w ((chainLength - 1) * a.chain) := by
  unfold knownG
  split
  · exact isWeightBound_pure _ _ _
  · exact isWeightBound_map _ ((cost_chainWalk hb P _ _ _ _ _ _).mono
      (Nat.mul_le_mul_right _ (by omega)))

theorem cost_layerData (P : PublicParameter) (F : Forgery) (rec : CLog) (l : Layer)
    (M : LayerMsg) : QueryCostAtMost (layerData hash P F rec l M) w (readCost a) := by
  unfold layerData
  refine (cost_messageDigest hb P l _ M _).bind fun d ↦ ?_
  split
  · exact isWeightBound_pure _ _ _
  · unfold decodeData
    exact ((Common.sequenceFin_cost _ _ fun i ↦ cost_recoverChain hb P l _ i _ _).bind fun _ ↦
      (Common.sequenceFin_cost _ _ fun i ↦ cost_knownG hb P rec _
        (Nat.le_sub_one_of_lt (Fin.isLt _))).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (le_of_eq (Nat.add_zero _ ▸ rfl))

theorem cost_forgedMsgG (P : PublicParameter) (F : Forgery) (l : Layer) :
    QueryCostAtMost (forgedMsgG hash P F l) w (if l = bottomLayer then 0 else layerRootCost a) := by
  unfold forgedMsgG
  split_ifs
  · exact isWeightBound_pure _ _ _
  · exact isWeightBound_map _ (cost_layerRoot hb P bottomLayer _ (.inl F.message) _)

theorem cost_pickG (P : PublicParameter) (F : Forgery) (rec : CLog)
    (ends : Layer → ChainIndex → Digest) :
    QueryCostAtMost (pickG hash P F rec ends) w (cprePostCost a) := by
  unfold pickG
  refine ((cost_sequenceFin_sum _
    (fun l ↦ (if l = bottomLayer then 0 else layerRootCost a) + readCost a) fun l ↦ ?_).bind
      fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  · unfold chainData
    refine (cost_forgedMsgG hb P F l).bind fun mo ↦ ?_
    split
    · exact isWeightBound_pure _ _ _
    · exact cost_layerData hb P F rec l _
  · simp only [sum_layer, topLayer_ne_bottomLayer, ↓reduceIte, cprePostCost]
    omega

end Pick

variable {W : OracleWorld} {w : W.Oracles.Domain → ℕ} {a : Kinds} (hb : KindBound W.hash w a)
include hb

theorem kindBound_wFst_hashC :
    KindBound (fun x ↦ wFst (hashC W x)) (sumCost (ι' := CQ) w) a :=
  (hb.sim (spec' := CSpec)).map fun x n h ↦ by
    show QueryCostAtMost (Prod.fst <$> ((fun a ↦ (a, ([] : CLog))) <$> hashB W x)) _ _
    exact isWeightBound_map _ (isWeightBound_map _ h)

omit hb in
theorem cost_wFst_queryV (j : CJ) (μ : ℕ) :
    QueryCostAtMost (wFst (queryV W j μ)) (sumCost (ι' := CQ) w) 0 := by
  show QueryCostAtMost (Prod.fst <$> (queryB W (.value j μ) >>= fun a ↦
    pure (a, [(⟨.value j μ, a⟩ : CEnt)]))) _ 0
  exact isWeightBound_map _ (cost_bind_pure (cost_inr w _))

theorem cost_cOps_root (P : PublicParameter) (g : Bases) :
    QueryCostAtMost (Gen.root (cOps W P g)).run (sumCost (ι' := CQ) w)
      (treeNodeCost (cKinds a) layerHeight) := by
  rw [cost_run_iff, Gen.mmap_root]
  unfold cOps
  rw [bOps_map]
  exact cost_root (opsBound_bOps (kindBound_wFst_hashC hb) (cost_wFst_queryV) P g)

theorem cost_cOps_sign (P : PublicParameter) (g : Bases) (idx : LeafIndex) (msg : Message) :
    QueryCostAtMost (Gen.sign (cOps W P g) idx msg).run (sumCost (ι' := CQ) w)
      (signCost (cKinds a)) := by
  rw [cost_run_iff, Gen.mmap_sign]
  unfold cOps
  rw [bOps_map]
  exact cost_sign (opsBound_bOps (kindBound_wFst_hashC hb) (cost_wFst_queryV) P g) idx msg

theorem cost_cpre_pre (hw : CoinsFree W w) :
    QueryCostAtMost (pre W) (sumCost w) (treeNodeCost (cKinds a) layerHeight) := by
  unfold pre
  refine ((cost_inr w _).bind (b := treeNodeCost (cKinds a) layerHeight) fun P ↦ ?_).mono
    (le_of_eq (Nat.zero_add _))
  refine ((cost_simulateQ_inl w (cost_sample W hw _)).bind
    (b := treeNodeCost (cKinds a) layerHeight) fun g ↦ ?_).mono (le_of_eq (Nat.zero_add _))
  exact cost_bind_pure (cost_cOps_root hb P g)

theorem cost_cpre_handler (st : St) (r : SigningRequest) :
    QueryCostAtMost (handler W st r) (sumCost w) (signCost (cKinds a)) := by
  unfold handler
  exact cost_bind_pure (cost_cOps_sign hb st.1 st.2.1 r.leafIndex r.message)

omit hb in
theorem cost_endsQ (F : Forgery) : QueryCostAtMost (endsQ W F) (sumCost (ι' := CQ) w) 0 := by
  unfold endsQ
  rw [cost_map_iff, cost_run_iff, mmap_sequenceFin]
  refine (Common.sequenceFin_cost 0 _ fun l ↦ ?_).mono (le_of_eq (Nat.mul_zero _))
  rw [mmap_sequenceFin]
  exact (Common.sequenceFin_cost 0 _ fun i ↦ cost_wFst_queryV _ _).mono
    (le_of_eq (Nat.mul_zero _))

theorem cost_cpre_post (s0 : S0) (F : Forgery) (st : St) :
    QueryCostAtMost (post W s0 F st) (sumCost w) (cprePostCost a) := by
  unfold post
  exact ((cost_endsQ F).bind fun ends ↦ cost_simulateQ_inl w (cost_pickG hb _ F _ ends)).mono
    (le_of_eq (Nat.zero_add _))

end Cpre

/-- **B3's hash calls**, for hash calls within `a` and free coins. -/
theorem isChargeBound_cpreRed_kinds {W : OracleWorld} {a : Kinds}
    (hb : KindBound W.hash W.cost a) (hw : CoinsFree W W.cost)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {n m : ℕ}
    (hn : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IPFunctor.IFreeM.IsChargeBound (cpreRed W A ()) (cmdCharge hashCharge)
      (treeNodeCost (cKinds a) layerHeight + ((n + signCost (cKinds a) * m) + cprePostCost a)) :=
  isChargeBound_cpreRed W A (by rw [hcallCost_eq_sumCost]; exact cost_cpre_pre hb hw)
    (fun st r ↦ by rw [hcallCost_eq_sumCost]; exact cost_cpre_handler hb st r)
    (fun s0 F st ↦ by rw [hcallCost_eq_sumCost]; exact cost_cpre_post hb s0 F st) hn hm

/-! ## B4 -/

/-- The cost of a target function's hash. -/
def tcrFnCost (a : Kinds) : TcrFn → ℕ
  | .leaf => a.leaf
  | .node => a.node

/-- **The SM-TCR-C layouts within the bounds `a`**: a leaf target's input at most `a.leaf`, a
node target's at most `a.node`, at any tweak. -/
def TcrBound {ι : Type} {spec : OracleSpec.{0, 0} ι} (hash : HashInput → OracleComp spec HashOutput)
    (w : ι → ℕ) (a : Kinds) : Prop :=
  ∀ f P t m, QueryCostAtMost (hash (xmssTcrC.layout f P t m)) w (tcrFnCost a f)

theorem sum_fin_val_mul (n c : ℕ) : ∑ k : Fin n, k.val * c = n * (n - 1) / 2 * c := by
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k ↦ k) n, Finset.sum_range_id]

/-- One forged layer's candidates: the digest, the chains, the leaf and the path's folds. -/
def layerCandsCost (a : Kinds) : ℕ :=
  a.msg + (chainCount * ((chainLength - 1) * a.chain) +
    (a.leaf + layerHeight * (layerHeight - 1) / 2 * a.node))

/-- B4's output: both layers' candidates, the bottom root, and the digest of each candidate. -/
def tcrPostCost (a : Kinds) : ℕ :=
  layerCandsCost a + (layerRootCost a + layerCandsCost a) + 2 * (a.leaf + layerHeight * a.node)

/-- B4's signing operations: chain walks and grinding, leaves and nodes read back. -/
def sKinds (a : Kinds) : Kinds :=
  ⟨(chainLength - 1) * a.chain, 0, 0, randomizerAttemptLimit * a.msg⟩

/-- No hash calls. -/
def zeroKinds : Kinds :=
  ⟨0, 0, 0, 0⟩

section Cands

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℕ} {a : Kinds}
  {hash : HashInput → OracleComp spec HashOutput}

theorem cost_withDigests (hT : TcrBound hash w a) (P : PublicParameter) :
    ∀ cs : List TcrOut,
      QueryCostAtMost (withDigests hash P cs) w (cs.map fun c ↦ tcrFnCost a c.1).sum
  | [] => by
    rw [withDigests]
    exact isWeightBound_pure _ _ _
  | c :: cs => by
    rw [withDigests]
    refine ((hT c.1 P c.2.1 c.2.2).bind fun _ ↦ (cost_withDigests hT P cs).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (le_of_eq ?_)
    rw [List.map_cons, List.sum_cons, Nat.add_zero]

theorem candSum_layerCands (P : PublicParameter) (F : Forgery) (l : Layer) (M : LayerMsg) :
    ∀ cs ∈ support (layerCands hash P F l M),
      (cs.map fun c ↦ tcrFnCost a c.1).sum ≤ a.leaf + layerHeight * a.node := by
  intro cs hcs
  unfold layerCands at hcs
  rw [mem_support_bind_iff] at hcs
  obtain ⟨d, -, hcs⟩ := hcs
  cases hx : Codeword.decode d with
  | none =>
    rw [hx] at hcs
    simp only [Option.elim, support_pure, Set.mem_singleton_iff] at hcs
    subst hcs
    exact Nat.zero_le _
  | some x =>
    rw [hx] at hcs
    simp only [Option.elim, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hcs
    obtain ⟨_, -, _, -, _, -, rfl⟩ := hcs
    simp [List.sum_ofFn, tcrFnCost]

theorem candSum_allCands (P : PublicParameter) (F : Forgery) :
    ∀ cs ∈ support (allCands hash P F),
      (cs.map fun c ↦ tcrFnCost a c.1).sum ≤ 2 * (a.leaf + layerHeight * a.node) := by
  intro cs hcs
  unfold allCands at hcs
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hcs
  obtain ⟨cb, hcb, r, -, ct, hct, rfl⟩ := hcs
  have h1 := candSum_layerCands (a := a) P F _ _ cb hcb
  have h2 : (ct.map fun c ↦ tcrFnCost a c.1).sum ≤ a.leaf + layerHeight * a.node := by
    cases r with
    | none =>
      simp only [Option.elim, support_pure, Set.mem_singleton_iff] at hct
      subst hct
      exact Nat.zero_le _
    | some r => exact candSum_layerCands P F _ _ ct hct
  rw [List.map_append, List.sum_append]
  omega

variable (hb : KindBound hash w a)
include hb

theorem cost_layerCands (P : PublicParameter) (F : Forgery) (l : Layer) (M : LayerMsg) :
    QueryCostAtMost (layerCands hash P F l M) w (layerCandsCost a) := by
  unfold layerCands
  refine (cost_messageDigest hb P l _ M _).bind (b := chainCount * ((chainLength - 1) * a.chain) +
    (a.leaf + layerHeight * (layerHeight - 1) / 2 * a.node)) fun d ↦ ?_
  cases Codeword.decode d with
  | none => exact isWeightBound_pure _ _ _
  | some x =>
    dsimp only [Option.elim]
    refine ((Common.sequenceFin_cost _ _ fun i ↦ cost_recoverChain hb P l _ i _ _).bind fun _ ↦
      (cost_leafHash hb P l _ _).bind fun leaf ↦ (cost_sequenceFin_sum _
        (fun k : Fin layerHeight ↦ k.val * a.node) fun k ↦ cost_treeFold hb P l _ _ k.val leaf).bind
          fun _ ↦ isWeightBound_pure _ _ 0).mono (le_of_eq ?_)
    rw [sum_fin_val_mul, Nat.add_zero]

theorem cost_allCands (P : PublicParameter) (F : Forgery) :
    QueryCostAtMost (allCands hash P F) w
      (layerCandsCost a + (layerRootCost a + layerCandsCost a)) := by
  unfold allCands
  refine (cost_layerCands hb P F _ _).bind fun _ ↦
    (cost_layerRoot hb P bottomLayer _ (.inl F.message) _).bind (b := layerCandsCost a) fun r ↦ ?_
  refine ((?_ : QueryCostAtMost (r.elim (pure []) fun r ↦ layerCands hash P F topLayer (.inr r))
    w (layerCandsCost a)).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))
  cases r with
  | none => exact isWeightBound_pure _ _ _
  | some r => exact cost_layerCands hb P F _ _

theorem cost_postCands (hT : TcrBound hash w a) (P : PublicParameter) (F : Forgery) :
    QueryCostAtMost (postCands hash P F) w (tcrPostCost a) := by
  unfold postCands
  exact QueryCostAtMost.bind_of_support (cost_allCands hb P F) fun cs hcs ↦
    (cost_withDigests hT P cs).mono (candSum_allCands P F cs hcs)

end Cands

section Tcr

variable {W : OracleWorld} {w : W.Oracles.Domain → ℕ} {a : Kinds}

theorem cost_tcrCall (q : TcrQ) : QueryCostAtMost (tcrCall W q) (sumCost w) 0 :=
  cost_inr w q

theorem opsBound_preOps (c : Layer → KeyIndex → ChainIndex → Digest) :
    OpsBound (preOps W c) (sumCost w) zeroKinds where
  chain l e i μ _ := by
    show QueryCostAtMost (walkChain (fun s x ↦ tcrCall W (.eval () (chainTw l e s i) x)) 0 μ
      (c l e i)) _ 0
    exact (Common.walkChain_cost _ 0 (fun _ _ ↦ cost_tcrCall _) 0 μ _).mono
      (le_of_eq (Nat.mul_zero _))
  leaf _ _ _ := cost_tcrCall _
  node _ _ _ _ _ := cost_dite (fun _ ↦ cost_tcrCall _) (fun _ ↦ isWeightBound_pure _ _ _)
  encode _ _ := isWeightBound_pure _ _ _

theorem cost_preAll (c : Layer → KeyIndex → ChainIndex → Digest) :
    QueryCostAtMost (preAll (preOps W c)) (sumCost w) 0 := by
  unfold preAll
  exact ((cost_root (opsBound_preOps c)).bind fun _ ↦ (cost_preTrees (opsBound_preOps c) _).bind
    fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp [treeNodeCost, keyLeafCost, zeroKinds])

theorem cost_recImpl : ∀ (t : (W.Oracles + TcrPorts).Domain) (s : QueryLog TcrPorts),
    QueryCostAtMost ((recImpl W t).run s) (sumCost w) (sumCost w t)
  | .inl q, s => by
    change QueryCostAtMost ((StateT.lift (liftM ((W.Oracles + TcrPorts).query (.inl q)) :
      OracleComp (W.Oracles + TcrPorts) _)).run s) _ _
    rw [StateT.run_lift]
    exact cost_bind_pure (isWeightBound_query _ _)
  | .inr q, s => by
    change QueryCostAtMost ((fun a ↦ (a, s ++ [⟨q, a⟩])) <$> tcrCall W q) _ _
    exact isWeightBound_map _ (isWeightBound_query _ _)

theorem cost_tcrPre (hw : CoinsFree W w) : QueryCostAtMost (tcrPre W) (sumCost w) 0 := by
  unfold tcrPre
  exact ((cost_simulateQ_inl w (cost_sample W hw _)).bind fun (cg : TcrCoins) ↦
    (isWeightBound_run_simulateQ (recImpl W) (sumCost w) (sumCost w) cost_recImpl
      (cost_preAll cg.1) []).bind fun _ ↦ (cost_inr w _).bind fun _ ↦
        isWeightBound_pure _ _ 0).mono (le_of_eq (by rfl))

variable (hb : KindBound W.hash w a)
include hb

theorem kindBound_tcrHash : KindBound (tcrHash W) (sumCost (ι' := TcrQ) w) a :=
  hb.sim

theorem opsBound_signOps (d : TcrData) : OpsBound (signOps W d) (sumCost w) (sKinds a) where
  chain l e i μ hμ := (cost_chainWalk (kindBound_tcrHash hb) d.P l e i 0 μ _).mono
    (Nat.mul_le_mul_right _ hμ)
  leaf _ _ _ := isWeightBound_pure _ _ _
  node _ _ _ _ _ := isWeightBound_pure _ _ _
  encode e M := cost_grind (kindBound_tcrHash hb) d.P _ e M _ _ _

theorem cost_tcrSigner (s : TcrSt) (r : SigningRequest) :
    QueryCostAtMost (tcrSigner W s r) (sumCost w) (signCost (sKinds a)) := by
  unfold tcrSigner
  exact cost_bind_pure (cost_sign (opsBound_signOps hb s.1) _ _)

theorem cost_tcrPost (hT : TcrBound W.hash w a) (d : TcrData) (F : Forgery) (s : TcrSt) :
    QueryCostAtMost (tcrPost W d F s) (sumCost w) (tcrPostCost a) := by
  unfold tcrPost
  exact (cost_map_iff _ _ _ _).mpr (cost_postCands (kindBound_tcrHash hb)
    (fun f P t m ↦ cost_simulateQ_inl w (hT f P t m)) d.P F)

end Tcr

/-- **B4's hash calls**, for hash calls within `a` and free coins. -/
theorem isChargeBound_tcrRed_kinds {W : OracleWorld} {a : Kinds}
    (hb : KindBound W.hash W.cost a) (hT : TcrBound W.hash W.cost a) (hw : CoinsFree W W.cost)
    (A : SufAdversary W PublicKey SigningRequest (Option Signature) Forgery) {n m : ℕ}
    (hn : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IPFunctor.IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IPFunctor.IFreeM.IsChargeBound (tcrRed W A ()) (cmdCharge hashCharge)
      (0 + ((n + signCost (sKinds a) * m) + tcrPostCost a)) :=
  isChargeBound_tcrRed W A (by rw [hcallCost_eq_sumCost]; exact cost_tcrPre hw)
    (fun s r ↦ by rw [hcallCost_eq_sumCost]; exact cost_tcrSigner hb s r)
    (fun d F s ↦ by rw [hcallCost_eq_sumCost]; exact cost_tcrPost hb hT d F s) hn hm

/-! ## The worlds' numerals -/

section Numerals

theorem romWorld_tcr : TcrBound romWorld.hash romWorld.cost romKinds :=
  fun f _ _ _ ↦ (romWorld_hash_cost _).mono (by cases f <;> exact le_rfl)

/-- The blocks of an SM-TCR-C layout: a leaf target's at most 8, a node target's 1. -/
theorem tcrLayout_blocks (P : PublicParameter) (f : TcrFn) (s : Slot) (m : TcrMsg f) :
    (tcrLayout P f s m).length / 136 + 1 ≤ tcrFnCost keccakKinds f := by
  cases f
  case leaf =>
    cases s
    case leaf l e =>
      change (thInput P _ (digestsPayload (n := chainCount) m)).length / 136 + 1 ≤ 8
      rw [length_thInput_eq, length_digestsPayload]
      decide
    all_goals
      change (littleEndianBytes 16 P ++ tcrBytes .leaf m).length / 136 + 1 ≤ 8
      rcases length_tcrJunk P .leaf m with h | h <;> rw [h] <;> decide
  case node =>
    cases s
    case node l k j =>
      change (thInput P _ (nodePayload m.1 m.2)).length / 136 + 1 ≤ 1
      rw [length_thInput_eq]
      simp [nodePayload, littleEndianBytes]
    all_goals
      change (littleEndianBytes 16 P ++ nodePayload m.1 m.2).length / 136 + 1 ≤ 1
      simp [nodePayload, littleEndianBytes]

theorem tcrBound_keccak {ι : Type} {spec : OracleSpec.{0, 0} ι} {w : ι → ℕ}
    {hash : HashInput → OracleComp spec HashOutput}
    (h : ∀ l, QueryCostAtMost (hash l) w (l.length / 136 + 1)) :
    TcrBound hash w keccakKinds :=
  fun f P t m ↦ (h _).mono (tcrLayout_blocks P f t.1 m)

theorem keccakWorld_tcr : TcrBound keccakWorld.hash keccakWorld.cost keccakKinds :=
  tcrBound_keccak keccakWorld_hash_cost

theorem rpmWorld_tcr (S : Type) [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) :
    TcrBound (rpmWorld S e).hash (rpmWorld S e).cost keccakKinds :=
  tcrBound_keccak (rpmWorld_hash_cost S e)

theorem prfCosts_rom : prfPreCost romKinds = 11534335 ∧ prfSignCost romKinds = 8624537563 ∧
    prfPostCost romKinds = 384 := by
  decide

theorem prfCosts_keccak : prfPreCost keccakKinds = 11993087 ∧
    prfSignCost keccakKinds = 8625913805 ∧ prfPostCost keccakKinds = 398 := by
  decide

theorem encCosts_rom : encPreCost romKinds = 11534335 ∧ encSignCost romKinds = 8636071898 ∧
    encPostCost romKinds = 193 := by
  decide

theorem encCosts_keccak : encPreCost keccakKinds = 11993087 ∧
    encSignCost keccakKinds = 8637906892 ∧ encPostCost keccakKinds = 200 := by
  decide

theorem cpreCosts_rom : treeNodeCost (cKinds romKinds) layerHeight = 131071 ∧
    signCost (cKinds romKinds) = 8590327771 ∧ cprePostCost romKinds = 890 := by
  decide

theorem cpreCosts_keccak : treeNodeCost (cKinds keccakKinds) layerHeight = 589823 ∧
    signCost (cKinds keccakKinds) = 8591704013 ∧ cprePostCost keccakKinds = 897 := by
  decide

theorem tcrCosts_rom : signCost (sKinds romKinds) = 8624144384 ∧ tcrPostCost romKinds = 818 := by
  decide

theorem tcrCosts_keccak : signCost (sKinds keccakKinds) = 8624144384 ∧
    tcrPostCost keccakKinds = 853 := by
  decide

end Numerals

/-! ## The charge corollaries at the numerals -/

section Charges

open IPFunctor

variable {n m : ℕ}

/-- **B1 in the QROM**: `n + 8624537563 m + 11534719` hash calls. -/
theorem isChargeBound_prfRed_rom
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (prfRed romWorld A u) (cmdCharge hashCharge)
      (n + 8624537563 * m + 11534719) := by
  refine (isChargeBound_prfRed_kinds romWorld_kinds A hn hm u).mono ?_
  obtain ⟨h0, hk, h1⟩ := prfCosts_rom
  rw [h0, hk, h1]
  omega

/-- **B1 in the standard model**: `n + 8625913805 m + 11993485` Keccak-f calls. -/
theorem isChargeBound_prfRed_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (u : Unit) :
    IFreeM.IsChargeBound (prfRed keccakWorld A u) (cmdCharge hashCharge)
      (n + 8625913805 * m + 11993485) := by
  refine (isChargeBound_prfRed_kinds keccakWorld_kinds A hn hm u).mono ?_
  obtain ⟨h0, hk, h1⟩ := prfCosts_keccak
  rw [h0, hk, h1]
  omega

/-- **B2 in the QROM**: `n + 8636071898 m + 11534528` hash calls. -/
theorem isChargeBound_encRed_rom
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (P : PublicParameter) :
    IFreeM.IsChargeBound (encRed romWorld A P) (cmdCharge hashCharge)
      (n + 8636071898 * m + 11534528) := by
  refine (isChargeBound_encRed_kinds romWorld_kinds romWorld_coinsFree A hn hm P).mono ?_
  obtain ⟨h0, hk, h1⟩ := encCosts_rom
  rw [h0, hk, h1]
  omega

/-- **B2 in the standard model**: `n + 8637906892 m + 11993287` Keccak-f calls. -/
theorem isChargeBound_encRed_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) (P : PublicParameter) :
    IFreeM.IsChargeBound (encRed keccakWorld A P) (cmdCharge hashCharge)
      (n + 8637906892 * m + 11993287) := by
  refine (isChargeBound_encRed_kinds keccakWorld_kinds keccakWorld_coinsFree A hn hm P).mono ?_
  obtain ⟨h0, hk, h1⟩ := encCosts_keccak
  rw [h0, hk, h1]
  omega

/-- **B3 in the QROM**: `n + 8590327771 m + 131961` hash calls. -/
theorem isChargeBound_cpreRed_rom
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (cpreRed romWorld A ()) (cmdCharge hashCharge)
      (n + 8590327771 * m + 131961) := by
  refine (isChargeBound_cpreRed_kinds romWorld_kinds romWorld_coinsFree A hn hm).mono ?_
  obtain ⟨h0, hk, h1⟩ := cpreCosts_rom
  rw [h0, hk, h1]
  omega

/-- **B3 in the standard model**: `n + 8591704013 m + 590720` Keccak-f calls. -/
theorem isChargeBound_cpreRed_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (cpreRed keccakWorld A ()) (cmdCharge hashCharge)
      (n + 8591704013 * m + 590720) := by
  refine (isChargeBound_cpreRed_kinds keccakWorld_kinds keccakWorld_coinsFree A hn hm).mono ?_
  obtain ⟨h0, hk, h1⟩ := cpreCosts_keccak
  rw [h0, hk, h1]
  omega

/-- **B4 in the QROM**: `n + 8624144384 m + 818` hash calls. -/
theorem isChargeBound_tcrRed_rom
    (A : SufAdversary romWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (tcrRed romWorld A ()) (cmdCharge hashCharge)
      (n + 8624144384 * m + 818) := by
  refine (isChargeBound_tcrRed_kinds romWorld_kinds romWorld_tcr romWorld_coinsFree A hn
    hm).mono ?_
  obtain ⟨hk, h1⟩ := tcrCosts_rom
  rw [hk, h1]
  omega

/-- **B4 in the standard model**: `n + 8624144384 m + 853` Keccak-f calls. -/
theorem isChargeBound_tcrRed_keccak
    (A : SufAdversary keccakWorld PublicKey SigningRequest (Option Signature) Forgery)
    (hn : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge hashCharge) n)
    (hm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge callCharge) m) :
    IFreeM.IsChargeBound (tcrRed keccakWorld A ()) (cmdCharge hashCharge)
      (n + 8624144384 * m + 853) := by
  refine (isChargeBound_tcrRed_kinds keccakWorld_kinds keccakWorld_tcr keccakWorld_coinsFree A
    hn hm).mono ?_
  obtain ⟨hk, h1⟩ := tcrCosts_keccak
  rw [hk, h1]
  omega

end Charges

/-! ## The calls at the challenge tweaks (R3) -/

section Challenge

theorem slotCost_le_one (S : Slot → Bool) : ∀ t, slotCost S t ≤ 1
  | .inl _ => Nat.zero_le _
  | .inr x => by
    show (if (Qrom.Xmss.slotOf x).any S then 1 else 0) ≤ 1
    split <;> omega

/-- Kinds counting the message digests only. -/
def msgKinds : Kinds :=
  ⟨0, 0, 0, 1⟩

/-- Kinds counting the chain steps only. -/
def chainKinds : Kinds :=
  ⟨1, 0, 0, 0⟩

/-- Kinds counting the leaves and nodes only. -/
def treeKinds : Kinds :=
  ⟨0, 1, 1, 0⟩

theorem prfSlots_kinds : KindBound romWorld.hash (slotCost prfSlots) zeroKinds :=
  slotCost_kinds prfSlots zeroKinds (fun _ _ _ _ ↦ by simp [prfSlots, zeroKinds])
    (fun _ _ ↦ by simp [prfSlots, zeroKinds]) (fun _ _ _ ↦ by simp [prfSlots, zeroKinds])
    (fun _ _ ↦ by simp [prfSlots, zeroKinds])

theorem msgSlots_kinds : KindBound romWorld.hash (slotCost msgSlots) msgKinds :=
  slotCost_kinds msgSlots msgKinds (fun _ _ _ _ ↦ by simp [msgSlots, msgKinds])
    (fun _ _ ↦ by simp [msgSlots, msgKinds]) (fun _ _ _ ↦ by simp [msgSlots, msgKinds])
    (fun _ _ ↦ by simp [msgSlots, msgKinds])

theorem chainSlots_kinds : KindBound romWorld.hash (slotCost chainSlots) chainKinds :=
  slotCost_kinds chainSlots chainKinds (fun _ _ _ _ ↦ by simp [chainSlots, chainKinds])
    (fun _ _ ↦ by simp [chainSlots, chainKinds]) (fun _ _ _ ↦ by simp [chainSlots, chainKinds])
    (fun _ _ ↦ by simp [chainSlots, chainKinds])

theorem treeSlots_kinds : KindBound romWorld.hash (slotCost treeSlots) treeKinds :=
  slotCost_kinds treeSlots treeKinds (fun _ _ _ _ ↦ by simp [treeSlots, treeKinds])
    (fun _ _ ↦ by simp [treeSlots, treeKinds]) (fun _ _ _ ↦ by simp [treeSlots, treeKinds])
    (fun _ _ ↦ by simp [treeSlots, treeKinds])

theorem treeSlots_tcr : TcrBound romWorld.hash (slotCost treeSlots) treeKinds := by
  intro f P t m
  rw [romWorld_hash_eq]
  unfold Qrom.hashQ
  split
  · exact (isWeightBound_query _ _).mono
      ((slotCost_le_one treeSlots _).trans (by cases f <;> exact le_rfl))
  · exact isWeightBound_pure _ _ _

/-- **B1's calls at the KIM-PRF's keyed slots**: none. B1 asks the PRF port for the parameter,
the chain starts and the randomizer bases; its own queries are chain steps, leaves, nodes and
message digests. -/
theorem prfRed_onChallenge :
    QueryCostAtMost (prfPre romWorld) (sumCost (slotCost prfSlots)) 0 ∧
      (∀ s r, QueryCostAtMost (prfSigner romWorld s r) (sumCost (slotCost prfSlots)) 0) ∧
      ∀ pk F s, QueryCostAtMost (prfPost romWorld pk F s) (sumCost (slotCost prfSlots)) 0 :=
  ⟨(cost_prfPre prfSlots_kinds).mono (by decide),
    fun s r ↦ (cost_prfSigner prfSlots_kinds s r).mono (by decide),
    fun pk F s ↦ (cost_prfPost prfSlots_kinds pk F s).mono (by decide)⟩

/-- **B2's calls at the EncTCR$ tweaks**: none in the setup; per signing request its own
grinding, at most `2 · 2^32` digests (at tweaks already sent to the challenger); two in the
output (the forged bottom digest and the top digest of the forged bottom root). -/
theorem encRed_onChallenge :
    (∀ P, QueryCostAtMost (encPre romWorld P) (sumCost (slotCost msgSlots)) 0) ∧
      (∀ P s r, QueryCostAtMost (encSign romWorld P s r) (sumCost (slotCost msgSlots))
        (2 * randomizerAttemptLimit)) ∧
      ∀ P s0 F s, QueryCostAtMost (encPost romWorld P s0 F s) (sumCost (slotCost msgSlots)) 2 :=
  ⟨fun P ↦ (cost_encPre msgSlots_kinds (slotCost_coinsFree _) P).mono (by decide),
    fun P s r ↦ (cost_encSign msgSlots_kinds (slotCost_coinsFree _) P s r).mono (by decide),
    fun P s0 F s ↦ (cost_encPost msgSlots_kinds P s0 F s).mono (by decide)⟩

/-- **B3's calls at the CPRE tweaks (the chain steps)**: none in the setup and the handler, which
read every chain value from the challenger; 870 in the output (the verification walks of the
bottom layer's root, and on each forged layer the forged chains and the known values walked up to
the codeword's digits). -/
theorem cpreRed_onChallenge :
    QueryCostAtMost (CpreRed.pre romWorld) (sumCost (slotCost chainSlots)) 0 ∧
      (∀ st r, QueryCostAtMost (CpreRed.handler romWorld st r) (sumCost (slotCost chainSlots))
        0) ∧
      ∀ s0 F st, QueryCostAtMost (CpreRed.post romWorld s0 F st)
        (sumCost (slotCost chainSlots)) 870 :=
  ⟨(cost_cpre_pre chainSlots_kinds (slotCost_coinsFree _)).mono (by decide),
    fun st r ↦ (cost_cpre_handler chainSlots_kinds st r).mono (by decide),
    fun s0 F st ↦ (cost_cpre_post chainSlots_kinds s0 F st).mono (by decide)⟩

/-- **B4's calls at the SM-TCR-C targets (leaves and nodes)**: none in the setup, which asks
every leaf and node as a target before the reveal, and none in the handler, which reads them
back; 293 in the output, after the reveal (the forged leaves and folds and the candidates'
digests). -/
theorem tcrRed_onChallenge :
    QueryCostAtMost (tcrPre romWorld) (sumCost (slotCost treeSlots)) 0 ∧
      (∀ s r, QueryCostAtMost (tcrSigner romWorld s r) (sumCost (slotCost treeSlots)) 0) ∧
      ∀ d F s, QueryCostAtMost (tcrPost romWorld d F s) (sumCost (slotCost treeSlots)) 293 :=
  ⟨cost_tcrPre (slotCost_coinsFree _),
    fun s r ↦ (cost_tcrSigner treeSlots_kinds s r).mono (by decide),
    fun d F s ↦ (cost_tcrPost treeSlots_kinds treeSlots_tcr d F s).mono (by decide)⟩

end Challenge

end Quantum.StdModel.Xmss

end
