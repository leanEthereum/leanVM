import XmssSecurity.Proof.IdealStatement

namespace XmssSecurity.Merkle

/-- Ascend `steps` levels, starting at `position`, using the supplied authentication path. -/
def ascend {α β : Type} (nodeHash : Nat → α → β → α) (path : Nat → β) :
    Nat → Nat → α → α
  | _, 0, leaf => leaf
  | position, steps + 1, leaf =>
      nodeHash (position + steps) (ascend nodeHash path position steps leaf)
        (path (position + steps))

def SamePathSegment {β : Type} (leftPath rightPath : Nat → β)
    (position steps : Nat) : Prop :=
  ∀ offset, offset < steps → leftPath (position + offset) = rightPath (position + offset)

def HasNodeCollision {α β : Type} (nodeHash : Nat → α → β → α)
    (leftPath rightPath : Nat → β) (position steps : Nat) (left right : α) : Prop :=
  ∃ offset, offset < steps ∧
    (ascend nodeHash leftPath position offset left, leftPath (position + offset)) ≠
      (ascend nodeHash rightPath position offset right, rightPath (position + offset)) ∧
    nodeHash (position + offset) (ascend nodeHash leftPath position offset left)
        (leftPath (position + offset)) =
      nodeHash (position + offset) (ascend nodeHash rightPath position offset right)
        (rightPath (position + offset))

/-- Equal Merkle roots imply identical leaves and paths, or an explicit collision at one level. -/
theorem samePath_or_hasNodeCollision {α β : Type} (nodeHash : Nat → α → β → α)
    (leftPath rightPath : Nat → β) (position steps : Nat) (left right : α)
    (hroot : ascend nodeHash leftPath position steps left =
      ascend nodeHash rightPath position steps right) :
    (left = right ∧ SamePathSegment leftPath rightPath position steps) ∨
      HasNodeCollision nodeHash leftPath rightPath position steps left right := by
  induction steps with
  | zero =>
      left
      exact ⟨by simpa [ascend] using hroot, by simp [SamePathSegment]⟩
  | succ steps ih =>
      let leftInput :=
        (ascend nodeHash leftPath position steps left, leftPath (position + steps))
      let rightInput :=
        (ascend nodeHash rightPath position steps right, rightPath (position + steps))
      by_cases hinput : leftInput = rightInput
      · have hmid : ascend nodeHash leftPath position steps left =
            ascend nodeHash rightPath position steps right := congrArg Prod.fst hinput
        have hsibling : leftPath (position + steps) = rightPath (position + steps) :=
          congrArg Prod.snd hinput
        rcases ih hmid with ⟨hleaf, hpath⟩ | hcollision
        · left
          refine ⟨hleaf, ?_⟩
          intro offset hoffset
          by_cases hlt : offset < steps
          · exact hpath offset hlt
          · have heq : offset = steps := by omega
            simpa [heq] using hsibling
        · right
          obtain ⟨offset, hoffset, hne, heq⟩ := hcollision
          exact ⟨offset, Nat.lt_succ_of_lt hoffset, hne, heq⟩
      · right
        exact ⟨steps, Nat.lt_succ_self steps, hinput, by simpa [leftInput, rightInput, ascend] using hroot⟩

def IsXmssPathCollisionAt {α β : Type} (nodeHash : Nat → α → β → α)
    (leftPath rightPath : Nat → β) (left right : α) (level : Fin treeHeight) : Prop :=
  (ascend nodeHash leftPath 0 level.val left, leftPath level.val) ≠
    (ascend nodeHash rightPath 0 level.val right, rightPath level.val) ∧
  nodeHash level.val (ascend nodeHash leftPath 0 level.val left) (leftPath level.val) =
    nodeHash level.val (ascend nodeHash rightPath 0 level.val right) (rightPath level.val)

def HasXmssPathCollision {α β : Type} (nodeHash : Nat → α → β → α)
    (leftPath rightPath : Nat → β) (left right : α) : Prop :=
  ∃ level, IsXmssPathCollisionAt nodeHash leftPath rightPath left right level

/-- An alternative XMSS authentication path reaching the same root is identical or collides at one of 32 levels. -/
theorem sameXmssPath_or_hasCollision {α β : Type} (nodeHash : Nat → α → β → α)
    (leftPath rightPath : Nat → β) (left right : α)
    (hroot : ascend nodeHash leftPath 0 treeHeight left =
      ascend nodeHash rightPath 0 treeHeight right) :
    (left = right ∧ SamePathSegment leftPath rightPath 0 treeHeight) ∨
      HasXmssPathCollision nodeHash leftPath rightPath left right := by
  rcases samePath_or_hasNodeCollision nodeHash leftPath rightPath 0 treeHeight left right hroot with
    hsame | ⟨level, hlevel, hne, heq⟩
  · exact Or.inl hsame
  · refine Or.inr ⟨⟨level, hlevel⟩, ?_, ?_⟩
    · simpa using hne
    · simpa using heq

end XmssSecurity.Merkle
