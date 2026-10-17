import Sphincs.SecurityDomains

/-! Finite structural positions and their exact serialized addresses, adapted from leanVM
b7a107256. The position type deliberately overapproximates the single retained subtree;
pruning selects the positions that are actually prepared. Forest positions are the chain steps,
the WOTS-key leaves, the subtree nodes, the tree leaves, the tree nodes and the key (`roots`) of
every instance. A tree leaf is the hash of the four level-2 nodes of its two subtrees and the key the
hash of the sixteen level-3 nodes of the trees: the root of a subtree (`subNode` at the last level)
and the root of a tree (`topNode` at the last level) are positions that no other position and no
algorithm reads. -/

namespace Sphincs

/-- The two natural-number fields of a tree node must fit their serialized slots: 24 bits for the
level, 32 bits for the node index. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ _ level nodeIdx => level < 2 ^ 24 ∧ nodeIdx < 2 ^ 32
  | _ => True

namespace Security

/-- A table of forest chain secrets `x_{i,0}`, by instance, tree, leaf, subtree, WOTS key and chain. -/
abbrev ForestSecrets := Index → Coord → SuperIdx → SubIdx → ChildIdx → FChain → Digest

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
    simp only [hashDomainFields, tweakFields, TweakFields.mk.injEq] at heq
  all_goals try { simp at heq; done }
  · rename_i lay tree leaf chain step lay' tree' leaf' chain' step'
    obtain ⟨_, hstep, hchain, hleaf⟩ := heq
    have he1 : lay = lay' := Subsingleton.elim (α := Fin 1) _ _
    have he2 : tree = tree' := Subsingleton.elim (α := Fin 1) _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    have he4 := fin_of_ofNat_eq (by decide) hchain
    have he5 := fin_of_ofNat_eq (by decide) hstep
    cases he1; cases he2; cases he3; cases he4; cases he5; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, _, hleaf⟩ := heq
    have he1 : lay = lay' := Subsingleton.elim (α := Fin 1) _ _
    have he2 : tree = tree' := Subsingleton.elim (α := Fin 1) _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    cases he1; cases he2; cases he3; rfl
  · rename_i lay tree level nodeIdx lay' tree' level' nodeIdx'
    obtain ⟨_, _, hlevel, hindex⟩ := heq
    have he1 : lay = lay' := Subsingleton.elim (α := Fin 1) _ _
    have he2 : tree = tree' := Subsingleton.elim (α := Fin 1) _ _
    have he3 := ofNat_inj_of_lt hl.1 hr.1 hlevel
    have he4 := ofNat_inj_of_lt hl.2 hr.2 hindex
    cases he1; cases he2; cases he3; cases he4; rfl
  · rename_i lay tree leaf lay' tree' leaf'
    obtain ⟨_, _, _, hleaf⟩ := heq
    have he1 : lay = lay' := Subsingleton.elim (α := Fin 1) _ _
    have he2 : tree = tree' := Subsingleton.elim (α := Fin 1) _ _
    have he3 := fin_of_ofNat_eq (by decide) hleaf
    cases he1; cases he2; cases he3; rfl
  · rename_i index c s j a i t index' c' s' j' a' i' t'
    obtain ⟨_, hstep, hpos, hindex⟩ := heq
    have hidx := fin_of_ofNat_eq (by decide) hindex
    have htt := fin_of_ofNat_eq (by decide) hstep
    have hp := nat_eq_of_ofNat (chainSlot_lt c s j a i) (chainSlot_lt c' s' j' a' i') (by decide) hpos
    obtain ⟨hc, hs, hj, ha, hi⟩ := chainSlot_injective hp
    subst hidx hc hs hj ha hi htt; rfl
  · rename_i index c s j a index' c' s' j' a'
    obtain ⟨_, _, hpos, hindex⟩ := heq
    have hidx := fin_of_ofNat_eq (by decide) hindex
    have hp := nat_eq_of_ofNat (childSlot_lt c s j a) (childSlot_lt c' s' j' a') (by decide) hpos
    obtain ⟨hsub, ha⟩ := childSlot_inj hp
    obtain ⟨hc, hs, hj⟩ := subSlot_inj hsub
    subst hidx hc hs hj ha; rfl
  · rename_i index c s j level node index' c' s' j' level' node'
    obtain ⟨_, _, hpos, hindex⟩ := heq
    have hidx := fin_of_ofNat_eq (by decide) hindex
    have hl := level.isLt; have hl' := level'.isLt
    have hn := node.isLt; have hn' := node'.isLt
    simp only [subHeight] at hl hl' hn hn'
    have h1 := subSlot_lt c s j; have h2 := subSlot_lt c' s' j'
    have hp := nat_eq_of_ofNat (bound := 8192) (by omega) (by omega) (by decide) hpos
    have hslot : subSlot c s j = subSlot c' s' j' := by omega
    have hnode : node = node' := Fin.ext (by omega)
    have hlv : level = level' := Fin.ext (by omega)
    obtain ⟨hc, hs, hj⟩ := subSlot_inj hslot
    subst hidx hc hs hj hnode hlv; rfl
  · rename_i index c s index' c' s'
    obtain ⟨_, _, hpos, hindex⟩ := heq
    have hidx := fin_of_ofNat_eq (by decide) hindex
    have := c.isLt; have := s.isLt; have := c'.isLt; have := s'.isLt
    simp only [forestCoords, topHeight] at *
    have hp := nat_eq_of_ofNat (bound := 136) (by omega) (by omega) (by decide) hpos
    have hc : c = c' := Fin.ext (by omega)
    have hs : s = s' := Fin.ext (by omega)
    subst hidx hc hs; rfl
  · rename_i index c level node index' c' level' node'
    obtain ⟨_, _, hpos, hindex⟩ := heq
    have hidx := fin_of_ofNat_eq (by decide) hindex
    have := c.isLt; have := node.isLt; have := c'.isLt; have := node'.isLt
    have := level.isLt; have := level'.isLt
    simp only [forestCoords, topHeight] at *
    have hp := nat_eq_of_ofNat (bound := 1024) (by omega) (by omega) (by decide) hpos
    have hc : c = c' := Fin.ext (by omega)
    have hn : node = node' := Fin.ext (by omega)
    have hl : level = level' := Fin.ext (by omega)
    subst hidx hc hn hl; rfl
  · obtain ⟨_, _, _, hindex⟩ := heq
    have he := fin_of_ofNat_eq (by decide) hindex
    cases he; rfl
  · rfl
/-- A structural position of the honest key. A `node` at `level` is the node of actual level
`level + 1`, the leaves being the `leaf` positions; likewise for the forest's `subNode` (over the
WOTS-key leaves `childLeaf`) and `topNode` (over the tree leaves `superChild`). -/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | fchain (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
  | childLeaf (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
  | subNode (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (level : Fin subHeight) (node : ChildIdx)
  | superChild (index : Index) (c : Coord) (s : SuperIdx)
  | topNode (index : Index) (c : Coord) (level : Fin topHeight) (node : SuperIdx)
  | roots (index : Index)
  deriving DecidableEq

instance positionFintype : Fintype Position where
  elems :=
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex × ChainIndex × ChainStep =>
      Position.chain x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × LeafIndex => Position.leaf x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Layer × TreeIndex × Fin maxLayerHeight × LeafIndex =>
      Position.node x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image fun x : Index × Coord × SuperIdx × SubIdx × ChildIdx × FChain × FStep =>
      Position.fchain x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2) ∪
    (Finset.univ.image fun x : Index × Coord × SuperIdx × SubIdx × ChildIdx =>
      Position.childLeaf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∪
    (Finset.univ.image fun x : Index × Coord × SuperIdx × SubIdx × Fin subHeight × ChildIdx =>
      Position.subNode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) ∪
    (Finset.univ.image fun x : Index × Coord × SuperIdx => Position.superChild x.1 x.2.1 x.2.2) ∪
    (Finset.univ.image fun x : Index × Coord × Fin topHeight × SuperIdx =>
      Position.topNode x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
    (Finset.univ.image fun x : Index => Position.roots x)
  complete := by
    intro p
    cases p <;> simp

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .fchain index c s j a i t => HashDomain.fchain index c s j a i t
  | .childLeaf index c s j a => HashDomain.childLeaf index c s j a
  | .subNode index c s j level nd => HashDomain.subNode index c s j level nd
  | .superChild index c s => HashDomain.superChild index c s
  | .topNode index c level nd => HashDomain.topNode index c level nd
  | .roots index => HashDomain.roots index

theorem domain_inRange (p : Position) : HashDomain.InRange p.domain := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 24 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | _ => exact (trivial : True)

theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]

/-- The last chain step, the one whose answer is the chain's endpoint. -/
def lastChainStep : ChainStep := ⟨chainLength - 2, by have := (show 2 ≤ chainLength by decide); omega⟩

/-- The last forest chain step, onto the chain top. -/
def lastForestStep : FStep := ⟨chainTop - 1, by decide⟩

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
  | .fchain index c s j a i t =>
      if h : 0 < t.val then [.fchain index c s j a i ⟨t.val - 1, by omega⟩] else []
  | .childLeaf index c s j a =>
      List.ofFn fun i : FChain => .fchain index c s j a i lastForestStep
  | .subNode index c s j level nd =>
      if hidx : 2 * nd.val + 1 < 2 ^ subHeight then
        if hlevel : 0 < level.val then
          [.subNode index c s j ⟨level.val - 1, by omega⟩ ⟨2 * nd.val, by omega⟩,
            .subNode index c s j ⟨level.val - 1, by omega⟩ ⟨2 * nd.val + 1, by omega⟩]
        else
          [.childLeaf index c s j ⟨2 * nd.val, by omega⟩,
            .childLeaf index c s j ⟨2 * nd.val + 1, by omega⟩]
      else []
  | .superChild index c s =>
      [.subNode index c s 0 ⟨subHeight - 2, by decide⟩ ⟨0, by decide⟩,
        .subNode index c s 0 ⟨subHeight - 2, by decide⟩ ⟨1, by decide⟩,
        .subNode index c s 1 ⟨subHeight - 2, by decide⟩ ⟨0, by decide⟩,
        .subNode index c s 1 ⟨subHeight - 2, by decide⟩ ⟨1, by decide⟩]
  | .topNode index c level nd =>
      if hidx : 2 * nd.val + 1 < 2 ^ topHeight then
        if hlevel : 0 < level.val then
          [.topNode index c ⟨level.val - 1, by omega⟩ ⟨2 * nd.val, by omega⟩,
            .topNode index c ⟨level.val - 1, by omega⟩ ⟨2 * nd.val + 1, by omega⟩]
        else
          [.superChild index c ⟨2 * nd.val, by omega⟩,
            .superChild index c ⟨2 * nd.val + 1, by omega⟩]
      else []
  | .roots index =>
      (List.finRange forestCoords).flatMap fun c : Coord =>
        [.topNode index c ⟨topHeight - 2, by decide⟩ ⟨0, by decide⟩,
          .topNode index c ⟨topHeight - 2, by decide⟩ ⟨1, by decide⟩]

/-! ### Depth and separated addresses

A position's children are strictly below it, and distinct positions have distinct serialized
inputs. -/

/-- A measure the payload recursion descends: a position's children are strictly below it. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .fchain _ _ _ _ _ _ t => t.val
  | .childLeaf _ _ _ _ _ => chainTop
  | .subNode _ _ _ _ level _ => chainTop + 1 + level.val
  | .superChild _ _ _ => chainTop + 1 + subHeight
  | .topNode _ _ level _ => chainTop + 2 + subHeight + level.val
  | .roots _ => chainTop + 2 + subHeight + topHeight

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
  | fchain index c s j a i t =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | childLeaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨i, hmem⟩ := hmem
      subst hmem
      simp [depth, lastForestStep, chainTop]
  | subNode index c s j level nd =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | superChild =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h <;> subst h <;> simp [depth, subHeight]
  | topNode index c level nd =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | roots =>
      simp only [children, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hmem
      obtain ⟨c, -, h | h⟩ := hmem <;> subst h <;> simp [depth, topHeight]

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
end Sphincs
