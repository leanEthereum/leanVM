import FORS.Scheme.Domains

/-! Finite structural positions and their exact serialized addresses, adapted from leanVM
b7a107256. The position type deliberately overapproximates the single retained subtree;
pruning selects the positions that are actually prepared. FORS positions are the leaves (the hash of
a secret) and the nodes of every tree of every instance; the root of a tree (`fnode` at the last
level) is a position that no other position and no algorithm reads. -/

namespace FORS

variable [Params]

/-- The two natural-number fields of a tree node must fit their serialized slots: 24 bits for the
level, 32 bits for the node index. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 24 ∧ nodeIdx < 2 ^ 32
  | _ => True

namespace Security

/-- A table of FORS secrets, by instance, tree and leaf. -/
abbrev ForsSecrets := Index → FTree → FLeaf → Digest

private theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (a.isLt.trans_le hn) (b.isLt.trans_le hn) h)

private theorem nat_eq_of_ofNat {w a b bound : Nat} (ha : a < bound) (hb : b < bound) (hn : bound ≤ 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b :=
  ofNat_inj_of_lt (ha.trans_le hn) (hb.trans_le hn) h

/-- No wrapping or domain ambiguity occurs at an in-range verification address: the type, the step
and the fields `hi` and `lo` determine the domain. The layer and the tree are not addressed; each has
one value. -/
theorem hashFields_injective {left right : HashDomain} (hl : HashDomain.InRange left)
    (hr : HashDomain.InRange right) (heq : hashDomainFields left = hashDomainFields right) : left = right := by
  cases left <;> cases right <;>
    simp only [hashDomainFields, tweakFields, treeFields, TweakFields.mk.injEq] at heq
  all_goals try { simp at heq; done }
  · rename_i lay tree leaf chain step lay' tree' leaf' chain' step'
    obtain ⟨_, hstep, hlayer, htree, hchain, hleaf⟩ := heq
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (tree_lt_two_pow_32 _) (tree_lt_two_pow_32 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (leaf_lt_two_pow_32 _) (leaf_lt_two_pow_32 _) hleaf)
    have he4 := fin_of_ofNat_eq (by decide) hchain
    have he5 := fin_of_ofNat_eq (by decide) hstep
    cases he1; cases he2; cases he3; cases he4; cases he5; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, hlayer, htree, _, hleaf⟩ := heq
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (tree_lt_two_pow_32 _) (tree_lt_two_pow_32 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (leaf_lt_two_pow_32 _) (leaf_lt_two_pow_32 _) hleaf)
    cases he1; cases he2; cases he3; rfl
  · rename_i lay tree level nodeIdx lay' tree' level' nodeIdx'
    obtain ⟨_, _, hlayer, htree, hlevel, hindex⟩ := heq
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (tree_lt_two_pow_32 _) (tree_lt_two_pow_32 _) htree)
    have he3 := ofNat_inj_of_lt hl.1 hr.1 hlevel
    have he4 := ofNat_inj_of_lt hl.2 hr.2 hindex
    cases he1; cases he2; cases he3; cases he4; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, hlayer, htree, _, hleaf⟩ := heq
    have he1 : lay = lay' := layerByte_ofNat_injective hlayer
    have he2 : tree = tree' := Fin.ext (ofNat_inj_of_lt (tree_lt_two_pow_32 _) (tree_lt_two_pow_32 _) htree)
    have he3 : leaf = leaf' := Fin.ext (ofNat_inj_of_lt (leaf_lt_two_pow_32 _) (leaf_lt_two_pow_32 _) hleaf)
    cases he1; cases he2; cases he3; rfl
  · rename_i index κ leaf index' κ' leaf'
    obtain ⟨_, _, _, _, hpos, hindex⟩ := heq
    have hidx : index = index' :=
      Fin.ext (ofNat_inj_of_lt (index_lt_two_pow_32 _) (index_lt_two_pow_32 _) hindex)
    have hp := nat_eq_of_ofNat (forsSlot_lt κ (leaf_lt_two_pow_18 leaf))
      (forsSlot_lt κ' (leaf_lt_two_pow_18 leaf')) (by decide) hpos
    obtain ⟨hκ, hl⟩ := forsSlot_injective hp
    subst hidx hκ
    cases Fin.ext hl; rfl
  · rename_i index κ level node index' κ' level' node'
    obtain ⟨_, _, _, _, hpos, hindex⟩ := heq
    have hidx : index = index' :=
      Fin.ext (ofNat_inj_of_lt (index_lt_two_pow_32 _) (index_lt_two_pow_32 _) hindex)
    have hp := nat_eq_of_ofNat (forsSlot_lt κ (nodePosition_lt _ node (level_lt_16 level)))
      (forsSlot_lt κ' (nodePosition_lt _ node' (level_lt_16 level'))) (by decide) hpos
    obtain ⟨hκ, hpos'⟩ := forsSlot_injective hp
    obtain ⟨hl, hn⟩ := nodePosition_injective (level_lt_16 level) (level_lt_16 level') hpos'
    subst hidx hκ
    cases Fin.ext (show level.val = level'.val by omega)
    cases Fin.ext hn; rfl
  · rename_i call call'
    obtain ⟨_, _, _, _, hcall, _⟩ := heq
    have : call.val < 2 ^ 24 := by
      have := call.isLt
      have hb : digestCalls ≤ 4 := by
        have hk : forsTrees * forsHeight ≤ 64 * 12 := Nat.mul_le_mul Params.forsTrees_le Params.forsHeight_le
        have := Params.totalHeight_le
        unfold digestCalls messageDigestBits hashOutputBits
        omega
      omega
    have : call'.val < 2 ^ 24 := by
      have := call'.isLt
      have hb : digestCalls ≤ 4 := by
        have hk : forsTrees * forsHeight ≤ 64 * 12 := Nat.mul_le_mul Params.forsTrees_le Params.forsHeight_le
        have := Params.totalHeight_le
        unfold digestCalls messageDigestBits hashOutputBits
        omega
      omega
    cases Fin.ext (ofNat_inj_of_lt (by assumption) (by assumption) hcall); rfl
/-- A structural position of the honest key. A `node` at `level` is the node of actual level
`level + 1`, the leaves being the `leaf` positions; likewise for FORS's `fnode` (over the FORS leaves
`fleaf`). -/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | fleaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | fnode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  deriving DecidableEq

instance positionFintype : Fintype Position where
  elems :=
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex × ChainIndex × ChainStep =>
      Position.chain x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex => Position.leaf x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × Fin maxLayerHeight × LeafIndex =>
      Position.node x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image fun x : Index × FTree × FLeaf => Position.fleaf x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Index × FTree × FLevel × FLeaf => Position.fnode x.1 x.2.1 x.2.2.1 x.2.2.2)
  complete := by
    intro p
    cases p <;> simp

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .fleaf index κ lf => HashDomain.forsLeaf index κ lf
  | .fnode index κ level nd => HashDomain.forsNode index κ level nd

theorem domain_inRange (p : Position) : HashDomain.InRange p.domain := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hmax := maxLayerHeight_le
      have hh := totalHeight_le_28
      show level.val + 1 < 2 ^ 24 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, leaf_lt_two_pow_32 nodeIdx⟩
  | _ => exact (trivial : True)

theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]

/-- The last chain step, the one whose answer is the chain's endpoint. -/
def lastChainStep : ChainStep := ⟨chainLength - 2, by have := (show 2 ≤ chainLength by decide); omega⟩

/-- The positions whose values the payload at this one is built from. -/
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .fleaf _ _ _ => []
  | .fnode index κ level nd =>
      if hidx : 2 * nd.val + 1 < 2 ^ forsHeight then
        if hlevel : 0 < level.val then
          [.fnode index κ ⟨level.val - 1, by omega⟩ ⟨2 * nd.val, by omega⟩,
            .fnode index κ ⟨level.val - 1, by omega⟩ ⟨2 * nd.val + 1, by omega⟩]
        else
          [.fleaf index κ ⟨2 * nd.val, by omega⟩, .fleaf index κ ⟨2 * nd.val + 1, by omega⟩]
      else []

/-! ### Depth and separated addresses

A position's children are strictly below it, and distinct positions have distinct serialized
inputs. -/

/-- A measure the payload recursion descends: a position's children are strictly below it. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .fleaf _ _ _ => 0
  | .fnode _ _ level _ => 1 + level.val

theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      have := (show 2 ≤ chainLength by decide)
      simp only [depth, lastChainStep]
      omega
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | fleaf => simp [children] at hmem
  | fnode index κ level nd =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem

theorem fields_injective {left right : Position}
    (h : hashDomainFields left.domain = hashDomainFields right.domain) : left = right :=
  domain_injective (hashFields_injective left.domain_inRange right.domain_inRange h)

theorem input_separated (parameter : PublicParameter) {left right : Position}
    (hne : left ≠ right) (leftPayload rightPayload : HashInput) :
    tweakableHashInput parameter left.domain leftPayload ≠
      tweakableHashInput parameter right.domain rightPayload := by
  intro h
  exact hne (fields_injective (tweakableInput_injective h).1)

end Position

end Security
end FORS
