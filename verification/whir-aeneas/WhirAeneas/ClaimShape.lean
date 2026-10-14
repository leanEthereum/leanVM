import Whir.SuccinctPointWeight

namespace WhirAeneas.ClaimShape
open Whir

/-- The enclosing dyadic block checked by source StackClaim::support.
For a strided claim this includes slots not selected by the claim. -/
def blockEnd : RingPCSGame.PointClaim → Nat
  | .point offset point _ => offset + 2 ^ point.size
  | .strided offset _ stride point _ => offset + 2 ^ (stride + point.size)

def blockFits (committed : Nat) (claim : RingPCSGame.PointClaim) : Prop :=
  blockEnd claim ≤ committed

/-- Dimension-first execution of the actual model's shape plus the source's
occupied-block restriction. The first branch avoids huge powers for malformed
machine metadata; its connection to Shape is proved below. -/
def checkOccupied (n committed : Nat) : RingPCSGame.PointClaim → Bool
  | .point offset point _ =>
      if point.size ≤ n then
        decide (offset % 2 ^ point.size = 0 ∧ offset + 2 ^ point.size ≤ committed)
      else false
  | .strided offset slot stride point _ =>
      if stride + point.size ≤ n then
        decide (offset % 2 ^ (stride + point.size) = 0 ∧
          offset + 2 ^ (stride + point.size) ≤ committed ∧ slot < 2 ^ stride)
      else false

instance (committed : Nat) (claim : RingPCSGame.PointClaim) :
    Decidable (blockFits committed claim) := inferInstanceAs (Decidable (_ ≤ _))

theorem checkOccupied_true_iff (n committed : Nat) (claim : RingPCSGame.PointClaim)
    (hcomm : committed ≤ 2 ^ n) :
    checkOccupied n committed claim = true ↔
      SuccinctPointWeight.Shape n claim ∧ blockFits committed claim := by
  cases claim with
  | point offset point value =>
    rw [SuccinctPointWeight.Shape.point_iff]
    unfold checkOccupied blockFits blockEnd
    by_cases hd : point.size ≤ n
    · simp only [hd, ite_true, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨⟨True.intro, h.1, h.2.trans hcomm⟩, h.2⟩
      · intro h
        exact ⟨h.1.2.1, h.2⟩
    · simp [hd]
  | strided offset slot stride point value =>
    rw [SuccinctPointWeight.Shape.strided_iff]
    unfold checkOccupied blockFits blockEnd
    by_cases hd : stride + point.size ≤ n
    · simp only [hd, ite_true, decide_eq_true_eq]
      constructor
      · intro h
        exact ⟨⟨True.intro, h.1, h.2.1.trans hcomm, h.2.2⟩, h.2.1⟩
      · intro h
        exact ⟨h.1.2.1, h.2, h.1.2.2.2⟩
    · simp [hd]

private theorem bool_ext_true (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem checkOccupied_eq (n committed : Nat) (claim : RingPCSGame.PointClaim)
    (hcomm : committed ≤ 2 ^ n) :
    checkOccupied n committed claim =
      (SuccinctPointWeight.check n claim && decide (blockFits committed claim)) := by
  apply bool_ext_true
  simpa only [Bool.and_eq_true, decide_eq_true_eq, SuccinctPointWeight.check_iff] using
    checkOccupied_true_iff n committed claim hcomm

theorem checkOccupied_full_cube (n : Nat) (claim : RingPCSGame.PointClaim) :
    checkOccupied n (2 ^ n) claim = SuccinctPointWeight.check n claim := by
  apply bool_ext_true
  rw [checkOccupied_true_iff n (2 ^ n) claim (Nat.le_refl _),
    SuccinctPointWeight.check_iff]
  constructor
  · exact fun h => h.1
  · intro h
    cases claim with
    | point offset point value => exact ⟨h, h.2⟩
    | strided offset slot stride point value => exact ⟨h, h.2.1⟩

end WhirAeneas.ClaimShape
