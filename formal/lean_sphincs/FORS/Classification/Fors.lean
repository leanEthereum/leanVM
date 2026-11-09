module

public import FORS.Classification.Chain

@[expose] public section

/-!
Deterministic extraction for the FORS opening. An opening whose FORS public key (`T_k` of the
recovered roots) is the canonical one either opens every tree at its canonical secret with the
canonical path, or one of the verifier's actual queries uses a different input producing a canonical
value: a leaf (`LeafMatch`), a node at levels `1 .. a` (`NodeMatch`, the root being level `a`), or the
`T_k` input itself (`RootsMatch`, non-canonical roots compressing to the canonical key). No
collision-freeness or security assumption is used.
-/

open OracleComp OracleSpec

namespace FORS.Security

variable [Params]
open Concrete

namespace Fors

/-- The node domain of a FORS tree, read off its level and node index (outside the hashed levels, the
`T_k` address, which no fold uses). -/
def forsDomain (index : Index) (κ : FTree) (height position : Nat) : HashDomain :=
  if hheight : 0 < height ∧ height ≤ forsHeight then
    .forsNode index κ ⟨height - 1, by omega⟩ ⟨position % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  else .forsRoots index

/-- A FORS path, extended by zero. -/
def extendPath (path : Fin forsHeight → Digest) (level : Nat) : Digest :=
  if hlevel : level < forsHeight then path ⟨level, hlevel⟩ else 0

theorem merkleFold_forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) (levels : Nat) (hlevels : levels ≤ forsHeight) (value : Digest) :
    merkleFold parameter (forsDomain index κ) leaf.val (extendPath path) levels value =
      (forsFold parameter index κ leaf path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have hl : levels < forsHeight := by omega
      rw [merkleFold, forsFold, ih (by omega)]
      apply bind_congr
      intro current
      rw [dite_eq_left hl]
      have hdom : forsDomain index κ (levels + 1) (leaf.val / 2 ^ (levels + 1)) =
          .forsNode index κ ⟨levels, hl⟩ ⟨leaf.val / 2 ^ (levels + 1),
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩ := by
        rw [forsDomain, dite_eq_left ⟨by omega, by omega⟩]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt))
      rw [hdom, extendPath, dite_eq_left hl]
      cases leaf.val.testBit levels <;> rfl

section Tree

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (κ : FTree)
  (seed : MasterSeed)

/-- The canonical path of a leaf. -/
def canonicalPath (leaf : FLeaf) (level : Fin forsHeight) : Digest :=
  Completeness.forsNodeValue f parameter index κ seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)

/-- The leaf a secret hashes to. -/
def leafValue (leaf : FLeaf) (secret : Digest) : Digest :=
  evalWithAnswerFn f (forsLeafHash parameter index κ leaf secret : OracleComp HashSpec Digest)

/-- The root an opening reaches: its leaf folded through all `a` levels. -/
def recoveredRoot (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest) : Digest :=
  evalWithAnswerFn f (forsFold parameter index κ leaf path forsHeight
    (leafValue f parameter index κ leaf secret) : OracleComp HashSpec Digest)

theorem leafValue_canonical (leaf : FLeaf) :
    leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf) =
      Completeness.forsNodeValue f parameter index κ seed 0 leaf.val := by
  rw [Completeness.forsNodeValue_zero, leafValue, forsLeafHash, Completeness.eval_tweakableHash]
  rfl

theorem canonical_root (leaf : FLeaf) :
    recoveredRoot f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf)
      (canonicalPath f parameter index κ seed leaf) = Completeness.rootValue f parameter index seed κ := by
  rw [recoveredRoot, leafValue_canonical]
  have h := Completeness.eval_forsFold_path f parameter index κ seed leaf
    (canonicalPath f parameter index κ seed leaf) forsHeight le_rfl (fun _ _ _ => rfl)
  rw [Nat.div_eq_of_lt leaf.isLt] at h
  exact h

/-- A selected secret differs but its leaf query produces the canonical leaf. -/
def LeafMatch (leaf : FLeaf) (secret : Digest) : Prop :=
  secret ≠ Completeness.forsSecretValue f parameter index κ seed leaf ∧
  leafValue f parameter index κ leaf secret =
    leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf)

/-- A node query on this opening hits the canonical value at the same tree address. -/
def NodeMatch (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest) (level : Nat) : Prop :=
  MerkleMatch f parameter (forsDomain index κ) leaf.val leaf.val (extendPath path)
    (extendPath (canonicalPath f parameter index κ seed leaf))
    (leafValue f parameter index κ leaf secret)
    (leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf)) level

/-- One tree of an opening that reaches the canonical root: the opening is canonical, or its leaf
query or one of its `a` node queries hits a canonical value from another input. -/
theorem tree_classification (leaf : FLeaf) (secret : Digest) (path : Fin forsHeight → Digest)
    (hroot : recoveredRoot f parameter index κ leaf secret path = Completeness.rootValue f parameter index seed κ) :
    (secret = Completeness.forsSecretValue f parameter index κ seed leaf ∧
      path = canonicalPath f parameter index κ seed leaf) ∨
    LeafMatch f parameter index κ seed leaf secret ∨
    ∃ level, level < forsHeight ∧ NodeMatch f parameter index κ seed leaf secret path level := by
  have hfold : merkleValue f parameter (forsDomain index κ) leaf.val (extendPath path)
      (leafValue f parameter index κ leaf secret) forsHeight =
    merkleValue f parameter (forsDomain index κ) leaf.val
      (extendPath (canonicalPath f parameter index κ seed leaf))
      (leafValue f parameter index κ leaf (Completeness.forsSecretValue f parameter index κ seed leaf))
      forsHeight := by
    simp only [merkleValue, merkleFold_forsFold _ _ _ _ _ _ le_rfl]
    exact hroot.trans (canonical_root f parameter index κ seed leaf).symm
  rcases merkleFold_same_index f parameter _ leaf.val _ _ _ _ forsHeight hfold with
    ⟨hleaf, hpath⟩ | hmatch
  · by_cases hsecret : secret = Completeness.forsSecretValue f parameter index κ seed leaf
    · refine Or.inl ⟨hsecret, ?_⟩
      funext level
      simpa only [extendPath, dite_eq_left level.isLt] using hpath level.val level.isLt
    · exact Or.inr (Or.inl ⟨hsecret, hleaf⟩)
  · exact Or.inr (Or.inr hmatch)

end Tree

section Key

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The `k` roots an opening reaches: what `T_k` compresses. -/
def roots (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : ForsKey :=
  fun κ => recoveredRoot f parameter index κ (leaves κ) (opening κ).secret (opening κ).path

/-- Every selected secret and path is canonical. -/
def Opening (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  ∀ κ, (opening κ).secret = Completeness.forsSecretValue f parameter index κ seed (leaves κ) ∧
    (opening κ).path = canonicalPath f parameter index κ seed (leaves κ)

/-- Non-canonical roots whose `T_k` query produces the canonical FORS public key. -/
def RootsMatch (roots : ForsKey) : Prop :=
  roots ≠ (fun κ => Completeness.rootValue f parameter index seed κ) ∧
  evalWithAnswerFn f (forsPublicKey parameter index roots : OracleComp HashSpec Digest) =
    evalWithAnswerFn f (forsPublicKey parameter index (fun κ => Completeness.rootValue f parameter index seed κ)
      : OracleComp HashSpec Digest)

/-- The exceptional branches: a leaf match, a node match at a hashed level, or a roots match. -/
def Exception (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) : Prop :=
  (∃ κ, LeafMatch f parameter index κ seed (leaves κ) (opening κ).secret) ∨
  (∃ κ level, level < forsHeight ∧
    NodeMatch f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path level) ∨
  RootsMatch f parameter index seed (roots f parameter index leaves opening)

theorem eval_forsRecover (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    evalWithAnswerFn f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) =
      roots f parameter index leaves opening := by
  simp only [forsRecover, treeRecover, evalWithAnswerFn_bind, Completeness.eval_sequenceFin]
  rfl

/-- **Classification of a recovered FORS public key.** -/
theorem recover_classification (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hrecover : evalWithAnswerFn f (forsPublicKey parameter index
        (evalWithAnswerFn f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey))
        : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec Digest)) :
    Opening f parameter index seed leaves opening ∨ Exception f parameter index seed leaves opening := by
  classical
  by_cases hroots : roots f parameter index leaves opening = fun κ => Completeness.rootValue f parameter index seed κ
  · by_cases hopening : Opening f parameter index seed leaves opening
    · exact Or.inl hopening
    · unfold Opening at hopening
      push Not at hopening
      obtain ⟨κ, hκ⟩ := hopening
      rcases tree_classification f parameter index κ seed (leaves κ) (opening κ).secret (opening κ).path
        (congrFun hroots κ) with hopen | hleaf | ⟨level, hlevel, hnode⟩
      · exact False.elim (hκ hopen.1 hopen.2)
      · exact Or.inr (Or.inl ⟨κ, hleaf⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨κ, level, hlevel, hnode⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hroots, ?_⟩))
    rw [← eval_forsRecover, hrecover, Completeness.forsKey_eq]

/-- Every selected secret is explicitly hashed during recovery. -/
theorem leafInput_mem (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) (κ : FTree) :
    tweakableHashInput parameter (.forsLeaf index κ (leaves κ)) (bytesLE 16 (opening κ).secret) ∈
      queriedInputs f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) := by
  rw [forsRecover]
  apply queriedInputs_sequenceFin_component f _ κ
  rw [treeRecover]
  apply queriedInputs_mono_bind_left
  simp only [forsLeafHash, queriedInputs_tweakableHash, List.mem_singleton]

theorem nodeInput_mem (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) (κ : FTree) (level : Nat)
    (hlevel : level < forsHeight) :
    merkleInput f parameter (forsDomain index κ) (leaves κ).val (extendPath (opening κ).path)
      (leafValue f parameter index κ (leaves κ) (opening κ).secret) level ∈
        queriedInputs f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey) := by
  rw [forsRecover]
  apply queriedInputs_sequenceFin_component f _ κ
  rw [treeRecover]
  apply queriedInputs_mono_bind_right
  rw [← merkleFold_forsFold _ _ _ _ _ _ le_rfl]
  exact merkleInput_mem f parameter _ _ _ _ _ _ hlevel

/-- The `T_k` input over the recovered roots is hashed after recovery. -/
theorem rootsInput_mem (leaves : FTree → FLeaf) (opening : FTree → TreeOpening) :
    tweakableHashInput parameter (.forsRoots index) (rootsPayload (roots f parameter index leaves opening)) ∈
      queriedInputs f (forsRecover parameter index leaves opening >>= forsPublicKey parameter index
        : OracleComp HashSpec Digest) := by
  apply queriedInputs_mono_bind_right
  rw [eval_forsRecover]
  simp only [forsPublicKey, queriedInputs_tweakableHash, List.mem_singleton]

/-- Every exceptional branch supplies an actual queried input of the recovery of the FORS public key
and a distinct canonical input with the same truncated output. -/
theorem Exception.queried_output_match (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (hexception : Exception f parameter index seed leaves opening) :
    ∃ input canonicalInput : HashInput,
      input ∈ queriedInputs f (forsRecover parameter index leaves opening >>= forsPublicKey parameter index
        : OracleComp HashSpec Digest) ∧
      input ≠ canonicalInput ∧ truncateHash (f input) = truncateHash (f canonicalInput) := by
  rcases hexception with ⟨κ, hne, heq⟩ | ⟨κ, level, hlevel, hnode⟩ | ⟨hne, heq⟩
  · refine ⟨tweakableHashInput parameter (.forsLeaf index κ (leaves κ)) (bytesLE 16 (opening κ).secret),
      tweakableHashInput parameter (.forsLeaf index κ (leaves κ))
        (bytesLE 16 (Completeness.forsSecretValue f parameter index κ seed (leaves κ))),
      queriedInputs_mono_bind_left f _ _ (leafInput_mem f parameter index leaves opening κ), ?_, ?_⟩
    · intro hinput
      exact hne (bytesLE_injective (List.append_cancel_left hinput))
    · simpa only [leafValue, forsLeafHash, Completeness.eval_tweakableHash] using heq
  · refine ⟨_, _, queriedInputs_mono_bind_left f _ _
      (nodeInput_mem f parameter index leaves opening κ level hlevel), hnode.2.1, ?_⟩
    exact hnode.2.2.trans (merkleValue_succ f parameter _ _ _ _ level)
  · refine ⟨tweakableHashInput parameter (.forsRoots index) (rootsPayload (roots f parameter index leaves opening)),
      tweakableHashInput parameter (.forsRoots index)
        (rootsPayload fun κ => Completeness.rootValue f parameter index seed κ),
      rootsInput_mem f parameter index leaves opening, ?_, ?_⟩
    · intro hinput
      exact hne (rootsPayload_injective (List.append_cancel_left hinput))
    · simpa only [Completeness.eval_forsPublicKey] using heq

end Key

end Fors
end FORS.Security
