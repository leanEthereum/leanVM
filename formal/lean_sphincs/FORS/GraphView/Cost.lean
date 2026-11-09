module

public import FORS.GraphView.Signer
public import FORS.GraphView.Secrets
public import FORS.GraphView.HashCalls
public import FORS.LazyRun.Cost

@[expose] public section

section

/-! The source oracle of the graph-reveal signer on a fixed answer function and coordinate
table: private draws are uniform, and hash and reveal queries are answered by the fixed view. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Seeded.finishSign digestAttemptLimit
set_option backward.isDefEq.respectTransparency false

noncomputable def fixedSource (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) :
    QueryImpl HiddenGraph.SourceSpec PMF :=
  (fun input => Cslib.Probability.PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF) +
    (fixedView f table).liftTarget PMF

end FORS.Security.GraphView

end

section

/-! Exact original honest hash costs for the graph-reveal signer. The simulation retains
ordinary message/encoding queries and represents the remaining internal work by explicit
natural-number ticks, including work performed before a failed WOTS search. -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix PrunedGraph
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.forsKey Seeded.forsOpen Seeded.treePath Seeded.otsSignFrom Seeded.signLayer
  chainWalk sequenceFin encode Seeded.treeRoot Seeded.forsNode

/-- The cost of opening one tree: the opened secret, then the sibling node at every level. -/
def treeOpenCost : Nat :=
  1 + ∑ level : Fin forsHeight, (3 * 2 ^ level.val - 1)

theorem hashCalls_treeOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (κ : FTree) (leaf : FLeaf) (seed : MasterSeed) :
    hashCalls f (Seeded.treeOpen parameter index κ leaf seed : OracleComp HashSpec TreeOpening) =
      treeOpenCost := by
  rw [Seeded.treeOpen, hashCalls_bind, Seeded.forsSecret, hashCalls_deriveKey, hashCalls_bind,
    hashCalls_sequenceFin, hashCalls_pure, Nat.add_zero, treeOpenCost]
  congr 1
  exact Finset.sum_congr rfl fun level _ =>
    hashCalls_forsNode f parameter index κ seed _ _ level.isLt.le

/-- Opening FORS costs `k` tree openings. -/
theorem hashCalls_forsOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : FTree → FLeaf) (seed : MasterSeed) :
    hashCalls f (Seeded.forsOpen parameter index leaves seed :
      OracleComp HashSpec (FTree → TreeOpening)) = forsTrees * treeOpenCost := by
  simp only [Seeded.forsOpen, hashCalls_sequenceFin, hashCalls_treeOpen_exact, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The published values of a WOTS+C signature cost `64 + 128 = 192` calls: the 64 seed derivations
of the chain starts and the 128 chain steps of a codeword. -/
theorem hashCalls_published_values (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (word : Encoding)
    (hword : TargetSum.Valid word) :
    hashCalls f (do
      let secrets ← (Seeded.otsSecrets parameter lay tree leaf seed : OracleComp HashSpec (ChainIndex → Digest))
      sequenceFin fun chain => chainWalk parameter lay tree leaf chain 0 (word chain).val (secrets chain)) = 192 := by
  simp only [hashCalls_sequenceFin, hashCalls_bind, hashCalls_otsSecrets]
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (word chain).val value :
        OracleComp HashSpec Digest) = (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (word chain).val value
      (by have := (word chain).isLt; omega)
  simp only [hwalk]
  change 64 + TargetSum.sum word = 192
  rw [show TargetSum.sum word = targetSum from hword]
  rfl

theorem hashCalls_otsSignFrom_search (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (attempts start : Nat) :
    hashCalls f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) +
        if (firstEncoding f parameter lay tree leaf message attempts start).isSome then 192 else 0 := by
  induction attempts generalizing start with
  | zero => simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding, hashCalls_pure,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  | succ attempts ih =>
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, ih]
          omega
      | some word =>
          have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
            message (BitVec.ofNat counterBits start) word he)
          have hpub := hashCalls_published_values f parameter lay tree leaf seed word hvalid
          rw [hashCalls_bind] at hpub
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, hashCalls_pure, hpub,
            Option.isSome_some, ↓reduceIte, Nat.add_zero]

/-- The cost of the authentication path of a layer: kept nodes below `keptHeight`, one derivation
per surrogate above. -/
def treePathCost (lay : Layer) : Nat :=
  ∑ level : Fin (layerHeight lay), if level.val < keptHeight lay then 258 * 2 ^ level.val - 1 else 1

theorem hashCalls_treePath_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) = treePathCost lay := by
  simp only [Seeded.treePath, hashCalls_sequenceFin, treePathCost]
  apply Finset.sum_congr rfl
  intro level _
  split
  · exact hashCalls_treeNode f parameter lay tree seed _ _
  · have hlevel : level.val < maxLayerHeight := level.isLt.trans_le (layerHeight_le lay)
    simp only [Seeded.surrogate, dite_eq_left hlevel, hashCalls_deriveKey]

/-- Folding a leaf up `levels` levels costs one call per level. -/
theorem hashCalls_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels value, hashCalls f (treeFold parameter lay tree leaf path levels value :
      OracleComp HashSpec Digest) = levels
  | 0, _ => hashCalls_pure f _
  | levels + 1, value => by
      rw [treeFold, hashCalls_bind, hashCalls_treeFold f parameter lay tree leaf path levels value]
      dsimp only
      split <;> simp only [hashCalls_tweakableHash]

theorem hashCalls_forsFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (κ : FTree) (leaf : FLeaf) (path : Fin forsHeight → Digest) :
    ∀ levels value, levels ≤ forsHeight → hashCalls f (forsFold parameter index κ leaf path levels value :
      OracleComp HashSpec Digest) = levels
  | 0, _, _ => hashCalls_pure f _
  | levels + 1, value, hlevels => by
      rw [forsFold, hashCalls_bind,
        hashCalls_forsFold f parameter index κ leaf path levels value (by omega)]
      simp only [dite_eq_left (show levels < forsHeight by omega)]
      split <;> simp only [hashCalls_tweakableHash]

/-- The cost of recovering the FORS public key from an opening: each tree's leaf and its `a` path
nodes, then `T_k`. -/
def forsRecoverCost : Nat := forsTrees * (1 + forsHeight) + 1

theorem hashCalls_forsRecover (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    hashCalls f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) =
      forsTrees * (1 + forsHeight) := by
  simp only [forsRecover, hashCalls_sequenceFin, treeRecover, hashCalls_bind, forsLeafHash,
    hashCalls_tweakableHash,
    fun κ value => hashCalls_forsFold f parameter index κ (leaves κ) (opening κ).path forsHeight value le_rfl,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem hashCalls_forsPublicKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (roots : ForsKey) :
    hashCalls f (forsPublicKey parameter index roots : OracleComp HashSpec Digest) = 1 :=
  hashCalls_tweakableHash f _ _ _

/-- Recovering a one-time leaf at a counter that encodes costs the encoding, the chains from the
revealed values to their ends, and the leaf hash: `1 + (64 * 3 - 128) + 1 = 66`. -/
theorem hashCalls_otsLeaf_of_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) (counter : Counter)
    (values : ChainIndex → Digest) (word : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some word) :
    hashCalls f (otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) = 66 := by
  have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
    message counter word hencode)
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (recoverChain parameter lay tree leaf chain (word chain) value :
        OracleComp HashSpec Digest) = chainLength - 1 - (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain _ _ value
      (by have := (word chain).isLt; omega)
  simp only [otsLeaf, hashCalls_bind, hashCalls_encode, hencode,
    hashCalls_sequenceFin, hwalk, Completeness.verification_chain_steps word hvalid,
    leafHash, hashCalls_tweakableHash, hashCalls_pure]

/-- The cost of recovering a layer's root below the top layer, which the layer above signs: the
one-time leaf and the fold up the layer's tree. The top layer's root is never recomputed. -/
def recoverCost (lay : Layer) : Nat := if lay.val = 0 then 0 else 66 + layerHeight lay

/-- Recovering a layer's root at a counter that encodes costs the one-time leaf and the fold. -/
theorem hashCalls_layerRecover_of_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (lay : Layer) (message : HashInput) (part : LayerSignature lay) (word : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message part.counter : OracleComp HashSpec (Option Encoding)) = some word) :
    hashCalls f (layerRecover parameter index lay message part : OracleComp HashSpec (Option Digest)) =
      66 + layerHeight lay := by
  rw [layerRecover, hashCalls_bind, hashCalls_otsLeaf_of_encode f _ _ _ _ _ _ _ word hencode]
  cases hvalue : evalWithAnswerFn f (otsLeaf parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) message part.counter part.chainValues : OracleComp HashSpec (Option Digest)) with
  | none => simp only [otsLeaf, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure, reduceCtorEq] at hvalue
  | some value => simp only [hashCalls_bind, hashCalls_treeFold, hashCalls_pure, Nat.add_zero]

/-- Signing a message costs the counter search, and on success the chain values and the path. -/
theorem hashCalls_signLayerWith (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index)
    (lay : Layer) (message : HashInput) :
    hashCalls f (Seeded.signLayerWith sk index lay message :
      OracleComp HashSpec (Option (LayerSignature lay))) =
      hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message encodingAttemptLimit 0) +
      if (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        message encodingAttemptLimit 0).isSome then 192 + treePathCost lay else 0 := by
  simp only [Seeded.signLayerWith, Seeded.otsSign, hashCalls_bind, hashCalls_otsSignFrom_search,
    otsSignFrom_eq_firstEncoding]
  cases firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, hashCalls_pure, hashCalls_bind, hashCalls_treePath_exact,
      Nat.add_zero]
  all_goals omega

/-- The cost of one layer of the signer on any value from below: the counter search, and on success
the chain values, the path and, below the top, the recovery of the root. -/
theorem hashCalls_layerStep (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index)
    (lay : Layer) (below : Digest) :
    hashCalls f (Seeded.layerStep sk index lay below :
      OracleComp HashSpec (Option (LayerSignature lay × Digest))) =
      hashCalls f (ReferenceChoice.search sk.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (rootPayload below) encodingAttemptLimit 0) +
      if (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (rootPayload below) encodingAttemptLimit 0).isSome then
          192 + treePathCost lay + recoverCost lay else 0 := by
  rw [Seeded.layerStep, hashCalls_bind, hashCalls_signLayerWith]
  have heval : evalWithAnswerFn f (Seeded.signLayerWith sk index lay (rootPayload below) :
      OracleComp HashSpec (Option (LayerSignature lay))) =
      (firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (rootPayload below) encodingAttemptLimit 0).map fun pair =>
          (⟨pair.1, fun chain => evalWithAnswerFn f (chainWalk sk.parameter lay (treeIndexAt index lay)
            (leafIndexAt index lay) chain 0 (pair.2 chain).val
            (derivedSecrets f sk.parameter sk.seed (lay, treeIndexAt index lay, leafIndexAt index lay, chain)) :
              OracleComp HashSpec Digest),
            evalWithAnswerFn f (Seeded.treePath sk.parameter lay (treeIndexAt index lay) sk.seed
              (leafIndexAt index lay) : OracleComp HashSpec (Fin (layerHeight lay) → Digest))⟩ :
            LayerSignature lay) := by
    simp only [Seeded.signLayerWith, evalWithAnswerFn_bind, Seeded.otsSign, otsSignFrom_eq_firstEncoding]
    cases firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (rootPayload below) encodingAttemptLimit 0 <;>
      simp only [Option.map_none, Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [heval]
  cases hs : firstEncoding f sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (rootPayload below) encodingAttemptLimit 0 with
  | none =>
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hashCalls_pure]
  | some pair =>
      obtain ⟨counter, word⟩ := pair
      have hencode := ReferenceChoice.firstEncoding_sound f sk.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (rootPayload below) encodingAttemptLimit 0 counter word hs
      simp only [Option.map_some, Option.isSome_some, ↓reduceIte, recoverCost]
      by_cases htop : lay.val = 0
      · simp only [htop, ↓reduceIte, hashCalls_pure]
        omega
      · simp only [htop, ↓reduceIte, hashCalls_bind]
        rw [hashCalls_layerRecover_of_encode f _ _ _ _ _ word hencode]
        split <;> simp only [hashCalls_pure] <;> omega

/-- The cost of the threaded sequence of computations, each started from `state` at its index and
handing the next the state of the index below it, is the cost of running them in order. -/
theorem hashCalls_sequenceThread {σ : Type} (f : QueryImpl HashSpec Id) (state : Nat → σ) :
    ∀ {n : Nat} {α : Fin n → Type} (computation : (i : Fin n) → σ → OracleComp HashSpec (Option (α i × σ))),
    (∀ (i : Fin n) (value : α i) (next : σ), i.val ≠ 0 →
      evalWithAnswerFn f (computation i (state i.val)) = some (value, next) → next = state (i.val - 1)) →
    hashCalls f (sequenceThread computation (state (n - 1))) =
      seqCost (fun i => (evalWithAnswerFn f (computation i (state i.val))).isSome)
        (fun i => hashCalls f (computation i (state i.val)))
  | 0, _, _, _ => rfl
  | n + 1, α, computation, hnext => by
      have ih := hashCalls_sequenceThread f state (α := fun i => α i.castSucc)
        (fun i => computation i.castSucc) (fun i => hnext i.castSucc)
      rw [Nat.add_sub_cancel]
      simp only [sequenceThread, hashCalls_bind, seqCost, Fin.val_last, Fin.val_castSucc]
      cases hhead : evalWithAnswerFn f (computation (Fin.last n) (state n)) with
      | none => simp only [hashCalls_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      | some pair =>
          obtain ⟨last, next⟩ := pair
          have hstate : hashCalls f (sequenceThread (α := fun i => α i.castSucc)
              (fun i => computation i.castSucc) next) =
              seqCost (fun i : Fin n => (evalWithAnswerFn f (computation i.castSucc (state i.val))).isSome)
                (fun i => hashCalls f (computation i.castSucc (state i.val))) := by
            rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn
              rfl
            · rw [hnext (Fin.last n) last next (by simp; omega) hhead]
              exact ih
          simp only [Option.isSome_some, ↓reduceIte, hashCalls_bind, hstate]
          cases evalWithAnswerFn f (sequenceThread (α := fun i => α i.castSucc)
              (fun i => computation i.castSucc) next) <;>
            simp only [hashCalls_pure, Nat.add_zero]

end FORS.Security.GraphView

end
