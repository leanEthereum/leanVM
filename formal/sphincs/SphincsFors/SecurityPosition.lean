import SphincsFors.SecurityDomains

/-! Finite structural positions and their exact serialized addresses, adapted from leanVM
b7a107256. The position type deliberately overapproximates the single retained subtree;
pruning selects the positions that are actually prepared. -/

namespace SphincsFors

/-- The natural-number fields must fit their serialized slots: a tree level in the 24-bit `hi` and
a node index in the 32-bit `lo`; a FORS level in 4 bits and a FORS node index in 15 bits of `hi`. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 24 ∧ nodeIdx < 2 ^ 32
  | .ftsNode _ _ level nodeIdx => level < 16 ∧ nodeIdx < 2 ^ 15
  | _ => True

namespace Security

private theorem fin_of_ofNat_eq {w n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ w)
    (h : BitVec.ofNat w a.val = BitVec.ofNat w b.val) : a = b :=
  Fin.ext (ofNat_inj_of_lt (a.isLt.trans_le hn) (b.isLt.trans_le hn) h)

/-- No wrapping or domain ambiguity occurs at an in-range verification address. -/
theorem hashFields_injective {left right : HashDomain} (hl : left.InRange)
    (hr : right.InRange) (heq : hashDomainFields left = hashDomainFields right) : left = right := by
  cases left <;> cases right <;>
    simp only [hashDomainFields, tweakFields, TweakFields.mk.injEq] at heq
  all_goals try { simp at heq; done }
  · rename_i lay tree leaf chain step lay' tree' leaf' chain' step'
    obtain ⟨_, hstep, hchain, hleaf⟩ := heq
    have he1 : lay = lay' := layer_eq _ _
    have he2 : tree = tree' := treeIndex_eq _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    have he4 := fin_of_ofNat_eq (by decide) hchain
    have he5 := fin_of_ofNat_eq (by decide) hstep
    cases he1; cases he2; cases he3; cases he4; cases he5; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, _, hleaf⟩ := heq
    have he1 : lay = lay' := layer_eq _ _
    have he2 : tree = tree' := treeIndex_eq _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    cases he1; cases he2; cases he3; rfl
  · rename_i lay tree level nodeIdx lay' tree' level' nodeIdx'
    obtain ⟨_, _, hlevel, hindex⟩ := heq
    have he1 : lay = lay' := layer_eq _ _
    have he2 : tree = tree' := treeIndex_eq _ _
    have he3 := ofNat_inj_of_lt hl.1 hr.1 hlevel
    have he4 := ofNat_inj_of_lt hl.2 hr.2 hindex
    cases he1; cases he2; cases he3; cases he4; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, _, hleaf⟩ := heq
    have he1 : lay = lay' := layer_eq _ _
    have he2 : tree = tree' := treeIndex_eq _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    cases he1; cases he2; cases he3; rfl
  · rename_i index tree leaf index' tree' leaf'
    obtain ⟨_, _, hpacked, hindex⟩ := heq
    have he1 := fin_of_ofNat_eq (by decide) hindex
    have ht := tree.isLt
    have ht' := tree'.isLt
    have hf := leaf.isLt
    have hf' := leaf'.isLt
    simp only [ftsTrees, ftsTreeHeight] at ht ht' hf hf'
    have hnat := ofNat_inj_of_lt (a := tree.val + 512 * leaf.val) (b := tree'.val + 512 * leaf'.val)
      (by omega) (by omega) hpacked
    have he2 : tree = tree' := Fin.ext (by omega)
    have he3 : leaf = leaf' := Fin.ext (by omega)
    cases he1; cases he2; cases he3; rfl
  · rename_i index tree level nodeIdx index' tree' level' nodeIdx'
    obtain ⟨_, _, hpacked, hindex⟩ := heq
    have he1 := fin_of_ofNat_eq (by decide) hindex
    have ht := tree.isLt
    have ht' := tree'.isLt
    simp only [ftsTrees] at ht ht'
    obtain ⟨hlevel, hnode⟩ := hl
    obtain ⟨hlevel', hnode'⟩ := hr
    have hnat := ofNat_inj_of_lt (a := tree.val + 32 * level + 512 * nodeIdx)
      (b := tree'.val + 32 * level' + 512 * nodeIdx') (by omega) (by omega) hpacked
    have he2 : tree = tree' := Fin.ext (by omega)
    have he3 : level = level' := by omega
    have he4 : nodeIdx = nodeIdx' := by omega
    cases he1; cases he2; cases he3; cases he4; rfl
  · obtain ⟨_, _, _, hindex⟩ := heq
    have he := fin_of_ofNat_eq (by decide) hindex
    cases he; rfl
  · obtain ⟨_, _, hcall, _⟩ := heq
    have he := fin_of_ofNat_eq (by decide) hcall
    cases he; rfl

/-- A structural position of the honest key. A `node` at `level` is the node of actual level
`level + 1`, the leaves being the `leaf` positions; likewise for `ftsNode`. A FORS tree has no root
hash: the children of `ftsRoots`, the FORS key hash, are the two nodes of actual level `a - 1` of
every tree. The `ftsNode` positions of actual level `a` remain in the type, like the node indices
beyond a level's width, and no position or scheme value reads them. -/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight) (nodeIdx : FtsLeaf)
  | ftsRoots (index : Index)
  deriving DecidableEq, Fintype

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .ftsLeaf index tree leafIdx => HashDomain.ftsLeaf index tree leafIdx
  | .ftsNode index tree level nodeIdx => HashDomain.ftsNode index tree (level.val + 1) nodeIdx.val
  | .ftsRoots index => HashDomain.ftsRoots index

theorem domain_inRange (p : Position) : p.domain.InRange := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 24 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | ftsNode index tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [ftsTreeHeight] at hlevel hnode
      show level.val + 1 < 16 ∧ nodeIdx.val < 2 ^ 15
      exact ⟨by omega, by omega⟩
  | chain => exact (trivial : True)
  | leaf => exact (trivial : True)
  | ftsLeaf => exact (trivial : True)
  | ftsRoots => exact (trivial : True)

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
  | .ftsLeaf _ _ _ => []
  | .ftsNode index tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight then
        if hlevel : 0 < level.val then
          [.ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.ftsLeaf index tree ⟨2 * nodeIdx.val, by omega⟩,
            .ftsLeaf index tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsRoots index =>
      (List.finRange ftsTrees).flatMap fun tree : FtsTree =>
        [.ftsNode index tree ⟨ftsTopLevel - 1, by decide⟩ ⟨0, by decide⟩,
          .ftsNode index tree ⟨ftsTopLevel - 1, by decide⟩ ⟨1, by decide⟩]

/-! ### Depth and separated addresses

A position's children are strictly below it, and distinct positions have distinct serialized
inputs. -/

/-- A measure the payload recursion descends: a position's children are strictly below it. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .ftsLeaf _ _ _ => 0
  | .ftsNode _ _ level _ => 1 + level.val
  | .ftsRoots _ => 1 + ftsTreeHeight

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
  | ftsLeaf => simp [children] at hmem
  | ftsNode index tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsRoots =>
      simp only [children, List.mem_flatMap, List.mem_finRange, true_and] at hmem
      obtain ⟨tree, hmem⟩ := hmem
      rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
        simp [depth, ftsTopLevel, ftsTreeHeight]

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
end SphincsFors
