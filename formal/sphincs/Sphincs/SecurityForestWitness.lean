import Sphincs.SecurityChainWitness

/-!
Deterministic extraction for the forest opening, the analogue of `SecurityForsWitness`. An opening
that recovers the canonical forest key either opens every needed chain at its canonical value with
canonical sub-tree and top-tree paths, or one of the verifier's actual queries uses a different input
producing a canonical value: a forest chain step (`ChainMatch`), a child leaf, a sub-tree node, a
super-child, a top-tree node or the roots hash. No collision-freeness or security assumption is used.

A tree has no root hash. The roots hash takes the two level-3 nodes of every top tree and the
super-child the two level-2 nodes of each of its sub-trees: the opening gives one of the two by
folding and the other as its last path element. An opening whose sixteen level-3 nodes are the
canonical ones (else `RootsMatch`) has, in every tree, the canonical last path element and a fold of
3 levels that reaches a canonical node, which is classified as a fold to a root was; likewise for the
four level-2 nodes of a super-child (`SuperMatch`) and the folds of 2 levels below them.
-/

open OracleComp OracleSpec

namespace Sphincs.Security
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

theorem rootsPayload_injective {tops tops' : Coord → Digest × Digest}
    (h : rootsPayload tops = rootsPayload tops') : tops = tops' :=
  flatMap_ofFn_injective (fun pair : Digest × Digest => nodePayload pair.1 pair.2) 32
    (fun pair => by simp [nodePayload, bytesLE_length])
    (fun _ _ hpair => Prod.ext (nodePayload_injective hpair).1 (nodePayload_injective hpair).2) h

theorem superPayload_injective {tops tops' : SubIdx → Digest × Digest}
    (h : superPayload tops = superPayload tops') : tops = tops' := by
  obtain ⟨h0, h1⟩ := List.append_inj h (by simp [nodePayload, bytesLE_length])
  funext j
  fin_cases j
  · exact Prod.ext (nodePayload_injective h0).1 (nodePayload_injective h0).2
  · exact Prod.ext (nodePayload_injective h1).1 (nodePayload_injective h1).2

theorem childPayload_injective {ends ends' : FChain → Digest}
    (h : childPayload ends = childPayload ends') : ends = ends' :=
  flatMap_ofFn_injective (bytesLE 16) 16 (bytesLE_length 16) (fun _ _ => bytesLE_injective) h

namespace Forest

/-! ### Forest chains -/

section Chain

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (c : Coord)
  (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (secret : Digest)

/-- The honest forest chain value at a position. -/
def honestChain (position : Nat) : Digest :=
  evalWithAnswerFn f (forestWalk parameter index c s j a i 0 position secret)

/-- What the walk has reached after `steps` steps from `start`. -/
def walkValue (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (forestWalk parameter index c s j a i start steps value)

theorem honestChain_succ (position : Nat) (hposition : position < chainTop) :
    honestChain f parameter index c s j a i secret (position + 1)
      = truncateHash (f (tweakableHashInput parameter (.fchain index c s j a i ⟨position, hposition⟩)
          ((bytesLE 16) (honestChain f parameter index c s j a i secret position)))) := by
  simp only [honestChain, forestWalk, evalWithAnswerFn_bind, Nat.zero_add, dif_pos hposition,
    Completeness.eval_tweakableHash]

theorem walkValue_succ (start : Nat) (value : Digest) (steps : Nat) (hrange : start + steps < chainTop) :
    walkValue f parameter index c s j a i start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter (.fchain index c s j a i ⟨start + steps, hrange⟩)
          ((bytesLE 16) (walkValue f parameter index c s j a i start value steps)))) := by
  simp only [walkValue, forestWalk, evalWithAnswerFn_bind, dif_pos hrange, Completeness.eval_tweakableHash]

/-- A hit at a forest chain step: something other than the honest value at `position` hashing to
the honest value at `position + 1`. -/
def ChainHit (position : Nat) (hposition : position < chainTop) (payload : Digest) : Prop :=
  payload ≠ honestChain f parameter index c s j a i secret position
    ∧ truncateHash (f (tweakableHashInput parameter (.fchain index c s j a i ⟨position, hposition⟩)
        ((bytesLE 16) payload))) = honestChain f parameter index c s j a i secret (position + 1)

theorem forestWalk_extract_above (start : Nat) (value : Digest) (steps cutoff : Nat)
    (hrange : start + steps ≤ chainTop) (hcutoff : cutoff ≤ steps)
    (hwalk : walkValue f parameter index c s j a i start value steps
      = honestChain f parameter index c s j a i secret (start + steps)) :
    walkValue f parameter index c s j a i start value cutoff
        = honestChain f parameter index c s j a i secret (start + cutoff)
      ∨ ∃ (offset : Nat) (hoffset : start + offset < chainTop),
          cutoff ≤ offset ∧ offset < steps ∧
          ChainHit f parameter index c s j a i secret (start + offset) hoffset
            (walkValue f parameter index c s j a i start value offset) := by
  induction steps with
  | zero =>
      have : cutoff = 0 := by omega
      subst cutoff
      exact Or.inl hwalk
  | succ steps ih =>
      by_cases heq : cutoff = steps + 1
      · subst cutoff
        exact Or.inl hwalk
      have hlt : start + steps < chainTop := by omega
      by_cases hagree : walkValue f parameter index c s j a i start value steps
          = honestChain f parameter index c s j a i secret (start + steps)
      · rcases ih (by omega) (by omega) hagree with hvalue | ⟨offset, hoffset, hcut, ho, hhit⟩
        · exact Or.inl hvalue
        · exact Or.inr ⟨offset, hoffset, hcut, by omega, hhit⟩
      · refine Or.inr ⟨steps, hlt, by omega, by omega, hagree, ?_⟩
        rw [← walkValue_succ f parameter index c s j a i start value steps hlt, hwalk,
          show start + (steps + 1) = start + steps + 1 by omega]

theorem forestWalk_query_mem (start steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps) (hrange : start + offset < chainTop) :
    tweakableHashInput parameter (.fchain index c s j a i ⟨start + offset, hrange⟩)
        ((bytesLE 16) (walkValue f parameter index c s j a i start value offset))
      ∈ queriedInputs f (forestWalk parameter index c s j a i start steps value) := by
  induction steps generalizing offset with
  | zero => omega
  | succ steps ih =>
      rw [forestWalk]
      split_ifs with hstep
      · rw [queriedInputs_bind]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hoffset with hlt | heq
        · exact List.mem_append_left _ (ih offset hlt hrange)
        · subst offset
          apply List.mem_append_right _
          simp only [walkValue, queriedInputs_tweakableHash, List.mem_singleton]
      · rw [queriedInputs_bind]
        apply List.mem_append_left
        exact ih offset (by omega) hrange

end Chain

/-! ### Canonical values -/

section Canonical

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

theorem chainValueOf_eq_honest (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (pos : Nat) :
    Completeness.chainValueOf f parameter index c s j a i seed pos =
      honestChain f parameter index c s j a i (Completeness.forestSecret f parameter index c s j a i seed) pos :=
  rfl

/-- The node domain of a sub-tree, read off its level and node index. -/
def subDomain (c : Coord) (s : SuperIdx) (j : SubIdx) (height position : Nat) : HashDomain :=
  if hheight : 0 < height ∧ height ≤ subHeight then
    .subNode index c s j ⟨height - 1, by omega⟩ ⟨position % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  else .roots index

/-- The node domain of a coordinate's top tree. -/
def topDomain (c : Coord) (height position : Nat) : HashDomain :=
  if hheight : 0 < height ∧ height ≤ topHeight then
    .topNode index c ⟨height - 1, by omega⟩ ⟨position % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  else .roots index

/-- A sub-tree path, extended by zero. -/
def subPathExt (path : Fin subHeight → Digest) (level : Nat) : Digest :=
  if hlevel : level < subHeight then path ⟨level, hlevel⟩ else 0

/-- A top-tree path, extended by zero. -/
def topPathExt (path : Fin topHeight → Digest) (level : Nat) : Digest :=
  if hlevel : level < topHeight then path ⟨level, hlevel⟩ else 0

theorem merkleFold_subFold (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
    (path : Fin subHeight → Digest) (levels : Nat) (hlevels : levels ≤ subHeight) (value : Digest) :
    merkleFold parameter (subDomain index c s j) a.val (subPathExt path) levels value =
      (subFold parameter index c s j a path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have hl : levels < subHeight := by omega
      rw [merkleFold, subFold, ih (by omega)]
      apply bind_congr
      intro current
      rw [dif_pos hl]
      have hdom : subDomain index c s j (levels + 1) (a.val / 2 ^ (levels + 1)) =
          .subNode index c s j ⟨levels, hl⟩ ⟨a.val / 2 ^ (levels + 1),
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩ := by
        rw [subDomain, dif_pos ⟨by omega, by omega⟩]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt))
      rw [hdom, subPathExt, dif_pos hl]
      cases a.val.testBit levels <;> rfl

theorem merkleFold_topFold (c : Coord) (s : SuperIdx) (path : Fin topHeight → Digest) (levels : Nat)
    (hlevels : levels ≤ topHeight) (value : Digest) :
    merkleFold parameter (topDomain index c) s.val (topPathExt path) levels value =
      (topFold parameter index c s path levels value : OracleComp HashSpec Digest) := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      have hl : levels < topHeight := by omega
      rw [merkleFold, topFold, ih (by omega)]
      apply bind_congr
      intro current
      rw [dif_pos hl]
      have hdom : topDomain index c (levels + 1) (s.val / 2 ^ (levels + 1)) =
          .topNode index c ⟨levels, hl⟩ ⟨s.val / 2 ^ (levels + 1),
            Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt⟩ := by
        rw [topDomain, dif_pos ⟨by omega, by omega⟩]
        congr 1
        exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt))
      rw [hdom, topPathExt, dif_pos hl]
      cases s.val.testBit levels <;> rfl

/-- The canonical sub-tree path of a child. -/
def canonicalSubPath (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (level : Fin subHeight) :
    Digest :=
  Completeness.subNodeValue f parameter index c s j seed level.val (Nat.xor (a.val / 2 ^ level.val) 1)

/-- The canonical top-tree path of a super-child. -/
def canonicalTopPath (c : Coord) (s : SuperIdx) (level : Fin topHeight) : Digest :=
  Completeness.topNodeValue f parameter index c seed level.val (Nat.xor (s.val / 2 ^ level.val) 1)

/-- The canonical level-3 nodes of every coordinate, the inputs of the forest key. -/
def canonicalRoots : Coord → Digest × Digest :=
  fun c => Completeness.topTopsValue f parameter index c seed

/-- Folding the canonical child leaf through the canonical path reaches the canonical nodes. -/
theorem canonical_sub_node (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (levels : Nat)
    (hlevels : levels ≤ subHeight) :
    merkleValue f parameter (subDomain index c s j) a.val
        (subPathExt (canonicalSubPath f parameter index seed c s j a))
        (Completeness.childLeafValue f parameter index c s j seed a) levels =
      Completeness.subNodeValue f parameter index c s j seed levels (a.val / 2 ^ levels) := by
  rw [merkleValue, merkleFold_subFold _ _ _ _ _ _ _ _ hlevels, ← Completeness.subNodeValue_zero,
    Completeness.eval_subFold_path f parameter index c s j seed a _ _ hlevels (fun _ _ _ => rfl)]

/-- Folding the canonical super-child through the canonical top path reaches the canonical nodes. -/
theorem canonical_top_node (c : Coord) (s : SuperIdx) (levels : Nat) (hlevels : levels ≤ topHeight) :
    merkleValue f parameter (topDomain index c) s.val (topPathExt (canonicalTopPath f parameter index seed c s))
        (Completeness.superValue f parameter index c seed s) levels =
      Completeness.topNodeValue f parameter index c seed levels (s.val / 2 ^ levels) := by
  rw [merkleValue, merkleFold_topFold _ _ _ _ _ _ hlevels, ← Completeness.topNodeValue_zero,
    Completeness.eval_topFold_path f parameter index c seed s _ _ hlevels (fun _ _ _ => rfl)]

theorem superValue_eq (c : Coord) (s : SuperIdx) :
    Completeness.superValue f parameter index c seed s =
      truncateHash (f (tweakableHashInput parameter (.superChild index c s)
        (superPayload (Completeness.subTopsValue f parameter index c seed s)))) :=
  Completeness.superValue_eq f parameter index c seed s

theorem forestKey_eq :
    evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter (.roots index)
        (rootsPayload (canonicalRoots f parameter index seed)))) :=
  Completeness.forestKey_eq f parameter index seed

end Canonical

/-! ### The values an opening reaches -/

section Opening

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

/-- The chain tops an opening of sub-tree `j` reaches. -/
def opEnds (c : Coord) (mark : CoordMark) (j : SubIdx) (values : FChain → Digest) : FChain → Digest :=
  fun i => walkValue f parameter index c mark.super j (mark.child j) i
    (chainTop - (lut (mark.word j) i).val) (values i) (lut (mark.word j) i).val

/-- The child leaf an opening reaches. -/
def opLeaf (c : Coord) (mark : CoordMark) (j : SubIdx) (values : FChain → Digest) : Digest :=
  truncateHash (f (tweakableHashInput parameter (.childLeaf index c mark.super j (mark.child j))
    (childPayload (opEnds f parameter index c mark j values))))

/-- The level-2 node of sub-tree `j` that an opening reaches by folding 2 levels. -/
def opSubNode (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening) : Digest :=
  merkleValue f parameter (subDomain index c mark.super j) (mark.child j).val (subPathExt opening.path)
    (opLeaf f parameter index c mark j opening.values) (subHeight - 1)

/-- The two level-2 nodes of sub-tree `j` that an opening gives: the one it reaches and its last
path element, in index order. -/
def opSubTops (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening) : Digest × Digest :=
  orderTops ((mark.child j).val.testBit (subHeight - 1)) (opSubNode f parameter index c mark j opening)
    (opening.path subTopLevel)

/-- The super-child an opening reaches. -/
def opSuper (c : Coord) (mark : CoordMark) (opening : CoordOpening) : Digest :=
  truncateHash (f (tweakableHashInput parameter (.superChild index c mark.super)
    (superPayload fun j => opSubTops f parameter index c mark j (opening.sub j))))

/-- The level-3 node of a coordinate that an opening reaches by folding 3 levels. -/
def opTopNode (c : Coord) (mark : CoordMark) (opening : CoordOpening) : Digest :=
  merkleValue f parameter (topDomain index c) mark.super.val (topPathExt opening.top)
    (opSuper f parameter index c mark opening) (topHeight - 1)

/-- The two level-3 nodes of a coordinate that an opening gives: the one it reaches and its last top
path element, in index order. -/
def opTops (c : Coord) (mark : CoordMark) (opening : CoordOpening) : Digest × Digest :=
  orderTops (mark.super.val.testBit (topHeight - 1)) (opTopNode f parameter index c mark opening)
    (opening.top topTopLevel)

/-- The level-3 nodes of every coordinate that an opening gives, the inputs of the roots hash. -/
def roots (marks : Coord → CoordMark) (opening : Coord → CoordOpening) : Coord → Digest × Digest :=
  fun c => opTops f parameter index c (marks c) (opening c)

theorem eval_childRecover (c : Coord) (mark : CoordMark) (j : SubIdx) (values : FChain → Digest) :
    evalWithAnswerFn f (childRecover parameter index c mark.super j (mark.child j) (lut (mark.word j)) values
      : OracleComp HashSpec Digest) = opLeaf f parameter index c mark j values := by
  simp only [childRecover, childLeafHash, forestRecoverChain, evalWithAnswerFn_bind,
    Completeness.eval_sequenceFin, Completeness.eval_tweakableHash]
  rfl

/-- The level-2 node the verifier's fold reaches in sub-tree `j`. -/
theorem eval_subNode (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening) :
    evalWithAnswerFn f (subFold parameter index c mark.super j (mark.child j) opening.path (subHeight - 1)
      (evalWithAnswerFn f (childRecover parameter index c mark.super j (mark.child j) (lut (mark.word j))
        opening.values : OracleComp HashSpec Digest)) : OracleComp HashSpec Digest) =
      opSubNode f parameter index c mark j opening := by
  rw [eval_childRecover, opSubNode, merkleValue, merkleFold_subFold _ _ _ _ _ _ _ _ (by decide)]

/-- The pair of level-2 nodes the verifier computes in sub-tree `j`. -/
theorem eval_subTops (c : Coord) (mark : CoordMark) (opening : CoordOpening) (j : SubIdx) :
    evalWithAnswerFn f (do
      let leaf ← childRecover parameter index c mark.super j (mark.child j) (lut (mark.word j))
        (opening.sub j).values
      let node ← subFold parameter index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1) leaf
      return orderTops ((mark.child j).val.testBit (subHeight - 1)) node ((opening.sub j).path subTopLevel)
      : OracleComp HashSpec (Digest × Digest)) =
      opSubTops f parameter index c mark j (opening.sub j) := by
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_subNode]
  rfl

/-- The super-child the verifier computes. -/
theorem eval_superHash (c : Coord) (mark : CoordMark) (opening : CoordOpening) :
    evalWithAnswerFn f (superHash parameter index c mark.super
      (fun j => opSubTops f parameter index c mark j (opening.sub j)) : OracleComp HashSpec Digest) =
      opSuper f parameter index c mark opening := by
  rw [superHash, Completeness.eval_tweakableHash, opSuper]

theorem eval_coordRecover (c : Coord) (mark : CoordMark) (opening : CoordOpening) :
    evalWithAnswerFn f (coordRecover parameter index c mark opening : OracleComp HashSpec (Digest × Digest)) =
      opTops f parameter index c mark opening := by
  simp only [coordRecover, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Completeness.eval_sequenceFin,
    eval_subNode]
  rw [opTops, opTopNode, merkleValue, merkleFold_topFold _ _ _ _ _ _ (by decide), ← eval_superHash]
  rfl

theorem eval_forestRecover (marks : Coord → CoordMark) (opening : Coord → CoordOpening) :
    evalWithAnswerFn f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) =
      truncateHash (f (tweakableHashInput parameter (.roots index)
        (rootsPayload (roots f parameter index marks opening)))) := by
  simp only [forestRecover, evalWithAnswerFn_bind, Completeness.eval_sequenceFin, eval_coordRecover,
    Completeness.eval_tweakableHash]
  rfl

end Opening

/-! ### Exceptions -/

section Exceptions

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- An opened chain of sub-tree `j` walks into its canonical chain through a step whose input differs
from the canonical value. -/
def ChainMatch (c : Coord) (mark : CoordMark) (j : SubIdx) (values : FChain → Digest) (i : FChain) : Prop :=
  ∃ (offset : Nat) (hoffset : chainTop - (lut (mark.word j) i).val + offset < chainTop),
    offset < (lut (mark.word j) i).val ∧
    ChainHit f parameter index c mark.super j (mark.child j) i
      (Completeness.forestSecret f parameter index c mark.super j (mark.child j) i seed)
      (chainTop - (lut (mark.word j) i).val + offset) hoffset
      (walkValue f parameter index c mark.super j (mark.child j) i
        (chainTop - (lut (mark.word j) i).val) (values i) offset)

/-- The chain tops differ from the canonical ones but the child leaf hashes to the canonical leaf. -/
def ChildLeafMatch (c : Coord) (mark : CoordMark) (j : SubIdx) (values : FChain → Digest) : Prop :=
  opEnds f parameter index c mark j values ≠
      Completeness.childEnds f parameter index c mark.super j seed (mark.child j) ∧
    opLeaf f parameter index c mark j values =
      Completeness.childLeafValue f parameter index c mark.super j seed (mark.child j)

/-- A sub-tree node query hits the canonical value at the same address. -/
def SubNodeMatch (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening) (level : Nat) : Prop :=
  MerkleMatch f parameter (subDomain index c mark.super j) (mark.child j).val (mark.child j).val
    (subPathExt opening.path)
    (subPathExt (canonicalSubPath f parameter index seed c mark.super j (mark.child j)))
    (opLeaf f parameter index c mark j opening.values)
    (Completeness.childLeafValue f parameter index c mark.super j seed (mark.child j)) level

/-- The four level-2 nodes differ from the canonical ones but hash to the canonical super-child. -/
def SuperMatch (c : Coord) (mark : CoordMark) (opening : CoordOpening) : Prop :=
  superPayload (fun j => opSubTops f parameter index c mark j (opening.sub j)) ≠
    superPayload (Completeness.subTopsValue f parameter index c seed mark.super) ∧
  opSuper f parameter index c mark opening = Completeness.superValue f parameter index c seed mark.super

/-- A top-tree node query hits the canonical value at the same address. -/
def TopNodeMatch (c : Coord) (mark : CoordMark) (opening : CoordOpening) (level : Nat) : Prop :=
  MerkleMatch f parameter (topDomain index c) mark.super.val mark.super.val (topPathExt opening.top)
    (topPathExt (canonicalTopPath f parameter index seed c mark.super))
    (opSuper f parameter index c mark opening)
    (Completeness.superValue f parameter index c seed mark.super) level

/-- The sixteen level-3 nodes differ from the canonical ones but hash to the forest key. -/
def RootsMatch (marks : Coord → CoordMark) (opening : Coord → CoordOpening) : Prop :=
  rootsPayload (roots f parameter index marks opening) ≠ rootsPayload (canonicalRoots f parameter index seed) ∧
  truncateHash (f (tweakableHashInput parameter (.roots index)
    (rootsPayload (roots f parameter index marks opening)))) =
    evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest)

/-- Every needed chain value, sub-tree path and top path is canonical. -/
def Opening (marks : Coord → CoordMark) (opening : Coord → CoordOpening) : Prop :=
  ∀ c, (∀ j i, ((opening c).sub j).values i =
      Completeness.chainValueOf f parameter index c (marks c).super j ((marks c).child j) i seed
        (chainTop - (lut ((marks c).word j) i).val)) ∧
    (∀ j, ((opening c).sub j).path = canonicalSubPath f parameter index seed c (marks c).super j ((marks c).child j)) ∧
    (opening c).top = canonicalTopPath f parameter index seed c (marks c).super

/-- The exceptional branches. A node match is at a hashed level: sub-tree levels 1 and 2, top-tree
levels 1 to 3. -/
def Exception (marks : Coord → CoordMark) (opening : Coord → CoordOpening) : Prop :=
  (∃ c j i, ChainMatch f parameter index seed c (marks c) j ((opening c).sub j).values i) ∨
  (∃ c j, ChildLeafMatch f parameter index seed c (marks c) j ((opening c).sub j).values) ∨
  (∃ c j level, level < subHeight - 1 ∧
    SubNodeMatch f parameter index seed c (marks c) j ((opening c).sub j) level) ∨
  (∃ c, SuperMatch f parameter index seed c (marks c) (opening c)) ∨
  (∃ c level, level < topHeight - 1 ∧ TopNodeMatch f parameter index seed c (marks c) (opening c) level) ∨
  RootsMatch f parameter index seed marks opening

/-- A sub-tree whose two level-2 nodes are canonical: its last path element is the canonical one,
and its fold of 2 levels reaches a canonical node, so the child leaf and the path below are canonical
or a node query matches. -/
theorem sub_fold_classification (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening)
    (htops : opSubTops f parameter index c mark j opening =
      Completeness.subTopsValue f parameter index c seed mark.super j) :
    (opLeaf f parameter index c mark j opening.values =
        Completeness.childLeafValue f parameter index c mark.super j seed (mark.child j) ∧
      opening.path = canonicalSubPath f parameter index seed c mark.super j (mark.child j)) ∨
    ∃ level, level < subHeight - 1 ∧ SubNodeMatch f parameter index seed c mark j opening level := by
  have hrange : (mark.child j).val / 2 ^ (subHeight - 1) < 2 := by
    have := (mark.child j).isLt
    simp only [subHeight] at this ⊢
    omega
  obtain ⟨hnode, hlast⟩ := (Completeness.orderTops_eq_iff
    (fun node => Completeness.subNodeValue f parameter index c mark.super j seed (subHeight - 1) node)
    (mark.child j).val (subHeight - 1) hrange _ _).mp htops
  have hfold : merkleValue f parameter (subDomain index c mark.super j) (mark.child j).val
      (subPathExt opening.path) (opLeaf f parameter index c mark j opening.values) (subHeight - 1) =
    merkleValue f parameter (subDomain index c mark.super j) (mark.child j).val
      (subPathExt (canonicalSubPath f parameter index seed c mark.super j (mark.child j)))
      (Completeness.childLeafValue f parameter index c mark.super j seed (mark.child j)) (subHeight - 1) :=
    hnode.trans (canonical_sub_node f parameter index seed c mark.super j (mark.child j) _ (by decide)).symm
  rcases merkleFold_same_index f parameter _ (mark.child j).val _ _ _ _ (subHeight - 1) hfold with
    ⟨hleaf, hpath⟩ | ⟨level, hlevel, hmatch⟩
  · refine Or.inl ⟨hleaf, ?_⟩
    funext level
    by_cases hlow : level.val < subHeight - 1
    · have hp := hpath level.val hlow
      simpa only [subPathExt, dif_pos level.isLt] using hp
    · have hlevel : level = subTopLevel := by
        apply Fin.ext
        have := level.isLt
        simp only [subTopLevel]
        omega
      rw [hlevel]
      exact hlast
  · exact Or.inr ⟨level, hlevel, hmatch⟩

/-- A coordinate whose two level-3 nodes are canonical: its last top path element is the canonical
one, and its fold of 3 levels reaches a canonical node, so the super-child and the top path below are
canonical or a node query matches. -/
theorem top_fold_classification (c : Coord) (mark : CoordMark) (opening : CoordOpening)
    (htops : opTops f parameter index c mark opening = Completeness.topTopsValue f parameter index c seed) :
    (opSuper f parameter index c mark opening = Completeness.superValue f parameter index c seed mark.super ∧
      opening.top = canonicalTopPath f parameter index seed c mark.super) ∨
    ∃ level, level < topHeight - 1 ∧ TopNodeMatch f parameter index seed c mark opening level := by
  have hrange : mark.super.val / 2 ^ (topHeight - 1) < 2 := by
    have := mark.super.isLt
    simp only [topHeight] at this ⊢
    omega
  obtain ⟨hnode, hlast⟩ := (Completeness.orderTops_eq_iff
    (fun node => Completeness.topNodeValue f parameter index c seed (topHeight - 1) node)
    mark.super.val (topHeight - 1) hrange _ _).mp htops
  have hfold : merkleValue f parameter (topDomain index c) mark.super.val (topPathExt opening.top)
      (opSuper f parameter index c mark opening) (topHeight - 1) =
    merkleValue f parameter (topDomain index c) mark.super.val
      (topPathExt (canonicalTopPath f parameter index seed c mark.super))
      (Completeness.superValue f parameter index c seed mark.super) (topHeight - 1) :=
    hnode.trans (canonical_top_node f parameter index seed c mark.super _ (by decide)).symm
  rcases merkleFold_same_index f parameter _ mark.super.val _ _ _ _ (topHeight - 1) hfold with
    ⟨hsuper, hpath⟩ | ⟨level, hlevel, hmatch⟩
  · refine Or.inl ⟨hsuper, ?_⟩
    funext level
    by_cases hlow : level.val < topHeight - 1
    · have hp := hpath level.val hlow
      simpa only [topPathExt, dif_pos level.isLt] using hp
    · have hlevel : level = topTopLevel := by
        apply Fin.ext
        have := level.isLt
        simp only [topTopLevel]
        omega
      rw [hlevel]
      exact hlast
  · exact Or.inr ⟨level, hlevel, hmatch⟩

/-- One sub-tree: canonical, or an exception at the chains, the child leaf or a node. -/
theorem sub_classification (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening)
    (htops : opSubTops f parameter index c mark j opening =
      Completeness.subTopsValue f parameter index c seed mark.super j) :
    ((∀ i, opening.values i = Completeness.chainValueOf f parameter index c mark.super j (mark.child j) i seed
        (chainTop - (lut (mark.word j) i).val)) ∧
      opening.path = canonicalSubPath f parameter index seed c mark.super j (mark.child j)) ∨
    (∃ i, ChainMatch f parameter index seed c mark j opening.values i) ∨
    ChildLeafMatch f parameter index seed c mark j opening.values ∨
    ∃ level, level < subHeight - 1 ∧ SubNodeMatch f parameter index seed c mark j opening level := by
  classical
  rcases sub_fold_classification f parameter index seed c mark j opening htops with
    ⟨hleaf, hpath'⟩ | ⟨level, hlevel, hmatch⟩
  · by_cases hends : opEnds f parameter index c mark j opening.values =
        Completeness.childEnds f parameter index c mark.super j seed (mark.child j)
    · by_cases hall : ∀ i, opening.values i = Completeness.chainValueOf f parameter index c mark.super j
          (mark.child j) i seed (chainTop - (lut (mark.word j) i).val)
      · exact Or.inl ⟨hall, hpath'⟩
      · push Not at hall
        obtain ⟨i, hi⟩ := hall
        refine Or.inr (Or.inl ⟨i, ?_⟩)
        have hd : (lut (mark.word j) i).val ≤ chainTop := Nat.le_of_lt_succ (lut (mark.word j) i).isLt
        have hwalk : walkValue f parameter index c mark.super j (mark.child j) i
            (chainTop - (lut (mark.word j) i).val) (opening.values i) (lut (mark.word j) i).val =
          honestChain f parameter index c mark.super j (mark.child j) i
            (Completeness.forestSecret f parameter index c mark.super j (mark.child j) i seed)
            (chainTop - (lut (mark.word j) i).val + (lut (mark.word j) i).val) := by
          rw [Nat.sub_add_cancel hd]
          exact congrFun hends i
        rcases forestWalk_extract_above f parameter index c mark.super j (mark.child j) i
            (Completeness.forestSecret f parameter index c mark.super j (mark.child j) i seed)
            (chainTop - (lut (mark.word j) i).val) (opening.values i) (lut (mark.word j) i).val 0
            (by omega) (Nat.zero_le _) hwalk with h0 | ⟨offset, hoffset, _, hlt, hhit⟩
        · exact False.elim (hi (by simpa only [walkValue, forestWalk, evalWithAnswerFn_pure,
            Nat.add_zero, chainValueOf_eq_honest] using h0))
        · exact ⟨offset, hoffset, hlt, hhit⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hends, hleaf⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨level, hlevel, hmatch⟩))

/-- One coordinate: canonical, or an exception. -/
theorem coord_classification (c : Coord) (mark : CoordMark) (opening : CoordOpening)
    (htops : opTops f parameter index c mark opening = Completeness.topTopsValue f parameter index c seed) :
    ((∀ j i, (opening.sub j).values i = Completeness.chainValueOf f parameter index c mark.super j
        (mark.child j) i seed (chainTop - (lut (mark.word j) i).val)) ∧
      (∀ j, (opening.sub j).path = canonicalSubPath f parameter index seed c mark.super j (mark.child j)) ∧
      opening.top = canonicalTopPath f parameter index seed c mark.super) ∨
    (∃ j i, ChainMatch f parameter index seed c mark j (opening.sub j).values i) ∨
    (∃ j, ChildLeafMatch f parameter index seed c mark j (opening.sub j).values) ∨
    (∃ j level, level < subHeight - 1 ∧ SubNodeMatch f parameter index seed c mark j (opening.sub j) level) ∨
    SuperMatch f parameter index seed c mark opening ∨
    ∃ level, level < topHeight - 1 ∧ TopNodeMatch f parameter index seed c mark opening level := by
  classical
  rcases top_fold_classification f parameter index seed c mark opening htops with
    ⟨hsuper, hpath'⟩ | ⟨level, hlevel, hmatch⟩
  · by_cases hpayload : superPayload (fun j => opSubTops f parameter index c mark j (opening.sub j)) =
        superPayload (Completeness.subTopsValue f parameter index c seed mark.super)
    · have hj : ∀ j : SubIdx, opSubTops f parameter index c mark j (opening.sub j) =
          Completeness.subTopsValue f parameter index c seed mark.super j :=
        fun j => congrFun (superPayload_injective hpayload) j
      by_cases hall : ∀ j, ((∀ i, (opening.sub j).values i = Completeness.chainValueOf f parameter index c
          mark.super j (mark.child j) i seed (chainTop - (lut (mark.word j) i).val)) ∧
          (opening.sub j).path = canonicalSubPath f parameter index seed c mark.super j (mark.child j))
      · exact Or.inl ⟨fun j => (hall j).1, fun j => (hall j).2, hpath'⟩
      · push Not at hall
        obtain ⟨j, hjbad⟩ := hall
        rcases sub_classification f parameter index seed c mark j (opening.sub j) (hj j) with
          hok | ⟨i, hchain⟩ | hleaf | ⟨level, hlevel, hnode⟩
        · exact False.elim (hjbad hok.1 hok.2)
        · exact Or.inr (Or.inl ⟨j, i, hchain⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨j, hleaf⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, level, hlevel, hnode⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpayload, hsuper⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨level, hlevel, hmatch⟩))))

/-- **Forest extraction.** An opening that recovers the canonical forest key is canonical or has an
exceptional branch. -/
theorem recover_classification (marks : Coord → CoordMark) (opening : Coord → CoordOpening)
    (hrecover : evalWithAnswerFn f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest)) :
    Opening f parameter index seed marks opening ∨ Exception f parameter index seed marks opening := by
  classical
  by_cases hpayload : rootsPayload (roots f parameter index marks opening) =
      rootsPayload (canonicalRoots f parameter index seed)
  · have hroots := rootsPayload_injective hpayload
    by_cases hopening : Opening f parameter index seed marks opening
    · exact Or.inl hopening
    · unfold Opening at hopening
      push Not at hopening
      obtain ⟨c, hc⟩ := hopening
      have htops : opTops f parameter index c (marks c) (opening c) =
          Completeness.topTopsValue f parameter index c seed := congrFun hroots c
      rcases coord_classification f parameter index seed c (marks c) (opening c) htops with
        hok | ⟨j, i, hchain⟩ | ⟨j, hleaf⟩ | ⟨j, level, hlevel, hnode⟩ | hsuper | ⟨level, hlevel, htop⟩
      · exact False.elim (hc hok.1 hok.2.1 hok.2.2)
      · exact Or.inr (Or.inl ⟨c, j, i, hchain⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨c, j, hleaf⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, j, level, hlevel, hnode⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hsuper⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, level, hlevel, htop⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hpayload, ?_⟩)))))
    rwa [← eval_forestRecover]

end Exceptions

/-! ### The inputs the verifier queries -/

section Inputs

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
  (marks : Coord → CoordMark) (opening : Coord → CoordOpening)

theorem coordInput_mem (c : Coord) {input : HashInput}
    (h : input ∈ queriedInputs f (coordRecover parameter index c (marks c) (opening c)
      : OracleComp HashSpec (Digest × Digest))) :
    input ∈ queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  rw [forestRecover]
  apply queriedInputs_mono_bind_left
  exact queriedInputs_sequenceFin_component f _ c h

theorem subInput_mem (c : Coord) (j : SubIdx) {input : HashInput}
    (h : input ∈ queriedInputs f (do
      let leaf ← childRecover parameter index c (marks c).super j ((marks c).child j) (lut ((marks c).word j))
        ((opening c).sub j).values
      let node ← subFold parameter index c (marks c).super j ((marks c).child j) ((opening c).sub j).path
        (subHeight - 1) leaf
      return orderTops (((marks c).child j).val.testBit (subHeight - 1)) node (((opening c).sub j).path subTopLevel)
        : OracleComp HashSpec (Digest × Digest))) :
    input ∈ queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply coordInput_mem f parameter index marks opening c
  rw [coordRecover]
  apply queriedInputs_mono_bind_left
  exact queriedInputs_sequenceFin_component f _ j h

/-- Every step of every opened chain is queried. -/
theorem chainInput_mem (c : Coord) (j : SubIdx) (i : FChain) (offset : Nat)
    (hoffset : offset < (lut ((marks c).word j) i).val)
    (hrange : chainTop - (lut ((marks c).word j) i).val + offset < chainTop) :
    tweakableHashInput parameter (.fchain index c (marks c).super j ((marks c).child j) i
        ⟨chainTop - (lut ((marks c).word j) i).val + offset, hrange⟩)
      ((bytesLE 16) (walkValue f parameter index c (marks c).super j ((marks c).child j) i
        (chainTop - (lut ((marks c).word j) i).val) (((opening c).sub j).values i) offset)) ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply subInput_mem f parameter index marks opening c j
  apply queriedInputs_mono_bind_left
  rw [childRecover]
  apply queriedInputs_mono_bind_left
  apply queriedInputs_sequenceFin_component f _ i
  exact forestWalk_query_mem f parameter index c _ j _ i _ _ _ offset hoffset hrange

/-- The child leaf of every opened sub-tree is queried. -/
theorem childLeafInput_mem (c : Coord) (j : SubIdx) :
    tweakableHashInput parameter (.childLeaf index c (marks c).super j ((marks c).child j))
        (childPayload (opEnds f parameter index c (marks c) j ((opening c).sub j).values)) ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply subInput_mem f parameter index marks opening c j
  apply queriedInputs_mono_bind_left
  rw [childRecover]
  apply queriedInputs_mono_bind_right
  simp only [childLeafHash, queriedInputs_tweakableHash, List.mem_singleton,
    Completeness.eval_sequenceFin]
  rfl

/-- Every sub-tree node input of the 2 folded levels is queried. -/
theorem subNodeInput_mem (c : Coord) (j : SubIdx) (level : Nat) (hlevel : level < subHeight - 1) :
    merkleInput f parameter (subDomain index c (marks c).super j) ((marks c).child j).val
      (subPathExt ((opening c).sub j).path) (opLeaf f parameter index c (marks c) j ((opening c).sub j).values) level ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply subInput_mem f parameter index marks opening c j
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  rw [eval_childRecover, ← merkleFold_subFold _ _ _ _ _ _ _ _ (by decide)]
  exact merkleInput_mem f parameter _ _ _ _ _ _ hlevel

/-- The super-child input of every coordinate is queried. -/
theorem superInput_mem (c : Coord) :
    tweakableHashInput parameter (.superChild index c (marks c).super)
        (superPayload fun j => opSubTops f parameter index c (marks c) j ((opening c).sub j)) ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply coordInput_mem f parameter index marks opening c
  rw [coordRecover]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  rw [superHash, queriedInputs_tweakableHash, List.mem_singleton]
  simp only [Completeness.eval_sequenceFin, eval_subTops]

/-- Every top-tree node input of the 3 folded levels is queried. -/
theorem topNodeInput_mem (c : Coord) (level : Nat) (hlevel : level < topHeight - 1) :
    merkleInput f parameter (topDomain index c) (marks c).super.val (topPathExt (opening c).top)
      (opSuper f parameter index c (marks c) (opening c)) level ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  apply coordInput_mem f parameter index marks opening c
  rw [coordRecover]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  simp only [Completeness.eval_sequenceFin, eval_subTops, eval_superHash]
  rw [← merkleFold_topFold _ _ _ _ _ _ (by decide)]
  exact merkleInput_mem f parameter _ _ _ _ _ _ hlevel

theorem rootsInput_mem :
    tweakableHashInput parameter (.roots index) (rootsPayload (roots f parameter index marks opening)) ∈
      queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) := by
  rw [forestRecover]
  apply queriedInputs_mono_bind_right
  rw [queriedInputs_tweakableHash, List.mem_singleton]
  simp only [Completeness.eval_sequenceFin, eval_coordRecover]
  rfl

end Inputs

/-- Every exceptional branch supplies an actual queried input and a distinct canonical input with
the same truncated output. -/
theorem Exception.queried_output_match (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (marks : Coord → CoordMark) (opening : Coord → CoordOpening)
    (hexception : Exception f parameter index seed marks opening) :
    ∃ input canonicalInput : HashInput,
      input ∈ queriedInputs f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) ∧
      input ≠ canonicalInput ∧ truncateHash (f input) = truncateHash (f canonicalInput) := by
  rcases hexception with ⟨c, j, i, offset, hoffset, hlt, hne, heq⟩ | ⟨c, j, hne, heq⟩ |
      ⟨c, j, level, hlevel, hnode⟩ | ⟨c, hne, heq⟩ | ⟨c, level, hlevel, hnode⟩ | ⟨hne, heq⟩
  · refine ⟨_, tweakableHashInput parameter (.fchain index c (marks c).super j ((marks c).child j) i
        ⟨chainTop - (lut ((marks c).word j) i).val + offset, hoffset⟩)
        ((bytesLE 16) (honestChain f parameter index c (marks c).super j ((marks c).child j) i
          (Completeness.forestSecret f parameter index c (marks c).super j ((marks c).child j) i seed)
          (chainTop - (lut ((marks c).word j) i).val + offset))),
      chainInput_mem f parameter index marks opening c j i offset hlt hoffset, ?_, ?_⟩
    · intro hinput
      exact hne (bytesLE_injective (List.append_cancel_left hinput))
    · rw [heq, honestChain_succ]
  · refine ⟨_, tweakableHashInput parameter (.childLeaf index c (marks c).super j ((marks c).child j))
        (childPayload (Completeness.childEnds f parameter index c (marks c).super j seed ((marks c).child j))),
      childLeafInput_mem f parameter index marks opening c j, ?_, ?_⟩
    · intro hinput
      exact hne (childPayload_injective (List.append_cancel_left hinput))
    · exact heq
  · refine ⟨_, _, subNodeInput_mem f parameter index marks opening c j level hlevel, hnode.2.1, ?_⟩
    exact hnode.2.2.trans (merkleValue_succ f parameter _ _ _ _ level)
  · refine ⟨_, tweakableHashInput parameter (.superChild index c (marks c).super)
        (superPayload (Completeness.subTopsValue f parameter index c seed (marks c).super)),
      superInput_mem f parameter index marks opening c, ?_, ?_⟩
    · exact fun hinput => hne (List.append_cancel_left hinput)
    · rw [← superValue_eq]
      exact heq
  · refine ⟨_, _, topNodeInput_mem f parameter index marks opening c level hlevel, hnode.2.1, ?_⟩
    exact hnode.2.2.trans (merkleValue_succ f parameter _ _ _ _ level)
  · refine ⟨_, tweakableHashInput parameter (.roots index) (rootsPayload (canonicalRoots f parameter index seed)),
      rootsInput_mem f parameter index marks opening, ?_, ?_⟩
    · exact fun hinput => hne (List.append_cancel_left hinput)
    · rw [heq, forestKey_eq]

end Forest
end Sphincs.Security
