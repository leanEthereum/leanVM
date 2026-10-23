import SphincsFors.SecurityChainWitness

set_option backward.isDefEq.respectTransparency false

/-!
Deterministic FORS extraction for the candidate's 24 trees. An opening recovering the canonical
FORS key either exposes the canonical secrets and paths, or one of its actual oracle queries
uses a different input producing a canonical leaf, node, or key hash value. A tree has no root
hash: the key hashes the two top nodes (level `a - 1`) of every tree, so an opening that reaches
the key with the canonical key-hash input has the canonical top node on the side of its leaf, which
is classified as a tree of height `a - 1`, and the other canonical top node as its last path
element, which is compared as an input of the key hash.
Adapted from leanVM b7a107256; no collision-freeness or security assumption is used.
-/

open OracleComp OracleSpec

namespace SphincsFors.Security
open Concrete

theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

theorem ftsTopsPayload_injective {tops tops' : FtsTree → Digest × Digest}
    (h : ftsTopsPayload tops = ftsTopsPayload tops') : tops = tops' :=
  flatMap_ofFn_injective (fun pair : Digest × Digest => nodePayload pair.1 pair.2) 32
    (fun _ => by simp [nodePayload, bytesLE_length])
    (fun left right hpair => by
      obtain ⟨hfirst, hsecond⟩ := List.append_inj hpair (by rw [bytesLE_length, bytesLE_length])
      exact Prod.ext (bytesLE_injective hfirst) (bytesLE_injective hsecond)) h

namespace Fors

def extendPath (path : Fin ftsTreeHeight → Digest) (level : Nat) : Digest :=
  if hlevel : level < ftsTreeHeight then path ⟨level, hlevel⟩ else 0

def canonicalPath (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) : Digest :=
  Completeness.ftsNodeValue f parameter index tree seed level.val
    (Nat.xor (leaf.val / 2 ^ level.val) 1)

def leafValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest) : Digest :=
  evalWithAnswerFn f (ftsLeafHash parameter index tree leaf secret : OracleComp HashSpec Digest)

/-- The top node (level `a - 1`) an opening reaches on the side of its leaf. -/
def topValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest)
    (path : Fin ftsTreeHeight → Digest) : Digest :=
  evalWithAnswerFn f (ftsFold parameter index tree leaf path ftsTopLevel
    (leafValue f parameter index tree leaf secret) : OracleComp HashSpec Digest)

/-- The last path element: the top node on the other side, an input of the key hash. -/
def topSibling (path : Fin ftsTreeHeight → Digest) : Digest := path ⟨ftsTopLevel, by decide⟩

theorem merkleFold_ftsFold (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    merkleFold parameter (fun height position => .ftsNode index tree height position)
      leaf.val (extendPath path) levels value =
        (ftsFold parameter index tree leaf path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [merkleFold, ftsFold, ih]
      apply bind_congr
      intro current
      cases leaf.val.testBit levels <;> rfl

theorem canonical_top (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (leaf : FtsLeaf) :
    topValue f parameter index tree leaf (Completeness.ftsSecret f parameter index tree leaf seed)
      (canonicalPath f parameter index tree seed leaf) =
        Completeness.ftsNodeValue f parameter index tree seed ftsTopLevel
          (leaf.val / 2 ^ ftsTopLevel) := by
  rw [topValue, leafValue, ← Completeness.ftsNodeValue_zero]
  exact Completeness.eval_ftsFold_path f parameter index tree seed leaf _ _ (by decide)
    (fun _ _ _ => rfl)

/-- A selected secret differs but its leaf query produces the canonical leaf hash. -/
def LeafMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (leaf : FtsLeaf) (secret : Digest) : Prop :=
  secret ≠ Completeness.ftsSecret f parameter index tree leaf seed ∧
  leafValue f parameter index tree leaf secret =
    leafValue f parameter index tree leaf (Completeness.ftsSecret f parameter index tree leaf seed)

/-- A node query on this opening hits the canonical value at the same tree address. -/
def NodeMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (leaf : FtsLeaf) (secret : Digest)
    (path : Fin ftsTreeHeight → Digest) (level : Nat) : Prop :=
  MerkleMatch f parameter (fun height position => .ftsNode index tree height position)
    leaf.val leaf.val (extendPath path) (extendPath (canonicalPath f parameter index tree seed leaf))
    (leafValue f parameter index tree leaf secret)
    (leafValue f parameter index tree leaf (Completeness.ftsSecret f parameter index tree leaf seed)) level

/-- One tree of an opening whose two top nodes, in node order, are the canonical ones: the
opening is canonical, or its leaf query or one of its `a - 1` node queries hits a canonical value
from another input. The last path element is not hashed here; it is read off the pair. -/
theorem tree_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (leaf : FtsLeaf) (secret : Digest)
    (path : Fin ftsTreeHeight → Digest)
    (htops : ftsTopPair leaf (topValue f parameter index tree leaf secret path) (topSibling path) =
      Completeness.ftsTopsValue f parameter index seed tree) :
    (secret = Completeness.ftsSecret f parameter index tree leaf seed ∧
      path = canonicalPath f parameter index tree seed leaf) ∨
    LeafMatch f parameter index tree seed leaf secret ∨
    ∃ level, level < ftsTopLevel ∧ NodeMatch f parameter index tree seed leaf secret path level := by
  obtain ⟨htop, hsibling⟩ := (Completeness.ftsTopPair_eq_iff
    (Completeness.ftsNodeValue f parameter index tree seed ftsTopLevel) leaf _ _).mp htops
  have hfold : merkleValue f parameter (fun height position => .ftsNode index tree height position)
      leaf.val (extendPath path) (leafValue f parameter index tree leaf secret) ftsTopLevel =
    merkleValue f parameter (fun height position => .ftsNode index tree height position)
      leaf.val (extendPath (canonicalPath f parameter index tree seed leaf))
      (leafValue f parameter index tree leaf (Completeness.ftsSecret f parameter index tree leaf seed))
      ftsTopLevel := by
    simp only [merkleValue, merkleFold_ftsFold]
    exact htop.trans (canonical_top f parameter index tree seed leaf).symm
  rcases merkleFold_same_index f parameter _ leaf.val _ _ _ _ ftsTopLevel hfold with
    ⟨hleaf, hpath⟩ | hmatch
  · by_cases hsecret : secret = Completeness.ftsSecret f parameter index tree leaf seed
    · refine Or.inl ⟨hsecret, ?_⟩
      funext level
      by_cases hlevel : level.val < ftsTopLevel
      · have hp := hpath level.val hlevel
        simpa only [extendPath, dite_eq_left level.isLt] using hp
      · have hlast : level = ⟨ftsTopLevel, by decide⟩ := by
          apply Fin.ext
          have := level.isLt
          simp only [ftsTopLevel, ftsTreeHeight] at hlevel this ⊢
          omega
        rw [hlast]
        exact hsibling
    · exact Or.inr (Or.inl ⟨hsecret, hleaf⟩)
  · exact Or.inr (Or.inr hmatch)

/-- The `2 k` top nodes an opening reaches, in node order: the payload of the key hash. -/
def tops (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) : FtsTree → Digest × Digest :=
  fun tree => ftsTopPair (leaves tree)
    (topValue f parameter index tree (leaves tree) (secrets tree) (paths tree)) (topSibling (paths tree))

def canonicalTops (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) : FtsTree → Digest × Digest :=
  Completeness.ftsTopsValue f parameter index seed

/-- The key hash of the opening has another input than the canonical one and the same value. -/
def TopsMatch (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) : Prop :=
  ftsTopsPayload (tops f parameter index leaves secrets paths) ≠
    ftsTopsPayload (canonicalTops f parameter index seed) ∧
  truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
    (ftsTopsPayload (tops f parameter index leaves secrets paths)))) =
    evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest)

def Opening (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) : Prop :=
  ∀ tree, secrets tree = Completeness.ftsSecret f parameter index tree (leaves tree) seed ∧
    paths tree = canonicalPath f parameter index tree seed (leaves tree)

def Exception (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) : Prop :=
  (∃ tree, LeafMatch f parameter index tree seed (leaves tree) (secrets tree)) ∨
  (∃ tree level, level < ftsTopLevel ∧
    NodeMatch f parameter index tree seed (leaves tree) (secrets tree) (paths tree) level) ∨
  TopsMatch f parameter index seed leaves secrets paths

theorem eval_ftsRecover (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    evalWithAnswerFn f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
        (ftsTopsPayload (tops f parameter index leaves secrets paths)))) := by
  simp only [ftsRecover, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Completeness.eval_sequenceFin,
    Completeness.eval_tweakableHash]
  rfl

theorem recover_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index leaves secrets paths :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest)) :
    Opening f parameter index seed leaves secrets paths ∨
      Exception f parameter index seed leaves secrets paths := by
  classical
  by_cases hpayload : ftsTopsPayload (tops f parameter index leaves secrets paths) =
      ftsTopsPayload (canonicalTops f parameter index seed)
  · have htops := ftsTopsPayload_injective hpayload
    by_cases hopening : Opening f parameter index seed leaves secrets paths
    · exact Or.inl hopening
    · unfold Opening at hopening
      push Not at hopening
      obtain ⟨tree, htree⟩ := hopening
      rcases tree_classification f parameter index tree seed (leaves tree) (secrets tree)
        (paths tree) (congrFun htops tree) with hopen | hleaf | ⟨level, hlevel, hnode⟩
      · exact False.elim (htree hopen.1 hopen.2)
      · exact Or.inr (Or.inl ⟨tree, hleaf⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨tree, level, hlevel, hnode⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hpayload, ?_⟩))
    rwa [← eval_ftsRecover]

/-- Every selected secret is explicitly hashed during recovery. -/
theorem leafInput_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) (tree : FtsTree) :
    tweakableHashInput parameter (.ftsLeaf index tree (leaves tree)) (bytesLE 16 (secrets tree)) ∈
      queriedInputs f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) := by
  rw [ftsRecover]
  apply queriedInputs_mono_bind_left
  apply queriedInputs_sequenceFin_component f _ tree
  apply queriedInputs_mono_bind_left
  simp only [ftsLeafHash, queriedInputs_tweakableHash, List.mem_singleton]
  rfl

theorem nodeInput_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) (tree : FtsTree) (level : Nat)
    (hlevel : level < ftsTopLevel) :
    merkleInput f parameter (fun height position => .ftsNode index tree height position)
      (leaves tree).val (extendPath (paths tree))
      (leafValue f parameter index tree (leaves tree) (secrets tree)) level ∈
        queriedInputs f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) := by
  rw [ftsRecover]
  apply queriedInputs_mono_bind_left
  apply queriedInputs_sequenceFin_component f _ tree
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  rw [← merkleFold_ftsFold]
  exact merkleInput_mem f parameter _ _ _ _ _ _ hlevel

theorem topsInput_mem (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    tweakableHashInput parameter (.ftsRoots index)
      (ftsTopsPayload (tops f parameter index leaves secrets paths)) ∈
      queriedInputs f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) := by
  rw [ftsRecover]
  apply queriedInputs_mono_bind_right
  rw [queriedInputs_tweakableHash, List.mem_singleton]
  simp only [Completeness.eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rfl

/-- An exact opening queries every selected canonical secret. Whether that secret was already
disclosed, or had to be guessed, is a separate transcript-level security obligation. -/
theorem Opening.trueSecretQuery (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hopening : Opening f parameter index seed leaves secrets paths) (tree : FtsTree) :
    tweakableHashInput parameter (.ftsLeaf index tree (leaves tree))
      (bytesLE 16 (Completeness.ftsSecret f parameter index tree (leaves tree) seed)) ∈
      queriedInputs f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) := by
  simpa only [← (hopening tree).1] using leafInput_mem f parameter index leaves secrets paths tree

/-- Every exceptional branch supplies an actual queried input and a distinct canonical input
with the same truncated output. The more detailed `Exception` identifies the canonical address
and target, which is required for a quantitative security bound. -/
theorem Exception.queried_output_match (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hexception : Exception f parameter index seed leaves secrets paths) :
    ∃ input canonicalInput : HashInput,
      input ∈ queriedInputs f (ftsRecover parameter index leaves secrets paths : OracleComp HashSpec Digest) ∧
      input ≠ canonicalInput ∧ truncateHash (f input) = truncateHash (f canonicalInput) := by
  rcases hexception with ⟨tree, hne, heq⟩ | ⟨tree, level, hlevel, hnode⟩ | ⟨hne, heq⟩
  · refine ⟨tweakableHashInput parameter (.ftsLeaf index tree (leaves tree))
        (bytesLE 16 (secrets tree)),
      tweakableHashInput parameter (.ftsLeaf index tree (leaves tree))
        (bytesLE 16 (Completeness.ftsSecret f parameter index tree (leaves tree) seed)),
      leafInput_mem f parameter index leaves secrets paths tree, ?_, ?_⟩
    · intro hinput
      exact hne (bytesLE_injective (List.append_cancel_left hinput))
    · simpa only [leafValue, ftsLeafHash, Completeness.eval_tweakableHash] using heq
  · refine ⟨_, _, nodeInput_mem f parameter index leaves secrets paths tree level hlevel,
      hnode.2.1, ?_⟩
    exact hnode.2.2.trans (merkleValue_succ f parameter _ _ _ _ level)
  · refine ⟨tweakableHashInput parameter (.ftsRoots index)
        (ftsTopsPayload (tops f parameter index leaves secrets paths)),
      tweakableHashInput parameter (.ftsRoots index)
        (ftsTopsPayload (canonicalTops f parameter index seed)),
      topsInput_mem f parameter index leaves secrets paths, ?_, ?_⟩
    · exact fun hinput => hne (List.append_cancel_left hinput)
    · rw [heq, Completeness.eval_ftsKey]
      rfl

end Fors
end SphincsFors.Security
