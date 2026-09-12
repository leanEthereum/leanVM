import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.BoundaryHashCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundaryHashAtLeast signDigestLoop

theorem boundaryHashAtLeast_lift_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, BoundaryHashAtLeast parameter (liftM (computation i)) (cost i)) :
    BoundaryHashAtLeast parameter (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact boundaryHashAtLeast_zero _ _
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind, ← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_ftsNode (traceParameter parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    BoundaryHashAtLeast traceParameter
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest))
      (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact boundaryHashAtLeast_tweakableHash traceParameter parameter
        (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) (digestBytes (secret (ftsLeafOfNat nodeIdx)))
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro right
      exact boundaryHashAtLeast_tweakableHash _ _ _ _

theorem boundaryHashAtLeast_ftsOpen (traceParameter parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) :
    BoundaryHashAtLeast traceParameter (liftM (ftsOpen parameter index leaves secret : OracleComp HashSpec _))
      (∑ _tree : FtsTree, ∑ level : Fin ftsTreeHeight, (2 ^ (level.val + 1) - 1)) := by
  unfold ftsOpen
  apply boundaryHashAtLeast_lift_sequenceFin
  intro tree
  apply boundaryHashAtLeast_lift_sequenceFin
  intro level
  exact boundaryHashAtLeast_ftsNode _ _ _ _ _ _ _

theorem boundaryHashAtLeast_signAttempt (parameter : PublicParameter) (key : SecretKey)
    (message : Message) (randomness : Randomness) :
    BoundaryHashAtLeast parameter (liftM (signAttempt key message randomness : OracleComp HashSpec _)) 1 := by
  unfold signAttempt messageDigest
  rw [liftM_bind, liftM_bind, bind_assoc]
  apply boundaryHashAtLeast_bind _ _ _ 1 0 (boundaryHashAtLeast_hash _ _)
  intro output
  exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_signDigestLoop_bind {α : Type} (parameter : PublicParameter)
    (key : SecretKey) (message : Message) (cost attempts : Nat)
    (next : Option (Randomness × Index × (IndexGroup → FtsLeaf)) → OracleComp OracleWorld α)
    (hnext : ∀ selected, BoundaryHashAtLeast parameter (next (some selected)) cost) :
    BoundaryHashAtLeast parameter (signDigestLoop attempts key message >>= next) (min attempts cost) := by
  induction attempts with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ attempts ih =>
      rw [signDigestLoop, bind_assoc, ← Nat.zero_add (min (attempts + 1) cost)]
      apply boundaryHashAtLeast_bind _ _ _ 0 _ (boundaryHashAtLeast_zero _ _)
      intro randomness
      rw [bind_assoc]
      apply BoundaryHashAtLeast.mono (a := 1 + min attempts cost) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ 1 _ (boundaryHashAtLeast_signAttempt _ _ _ _)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected =>
          simp only [pure_bind]
          exact BoundaryHashAtLeast.mono (hnext _) (min_le_right _ _)

theorem boundaryHashAtLeast_sign (parameter : PublicParameter) (key : SecretKey) (message : Message) :
    BoundaryHashAtLeast parameter (sign key message) 28504 := by
  rw [sign_eq]
  apply BoundaryHashAtLeast.mono (a := min digestAttemptLimit 28504) ?_ (by decide)
  apply boundaryHashAtLeast_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  apply boundaryHashAtLeast_bind _ _ _ 28504 0
  · exact BoundaryHashAtLeast.mono (boundaryHashAtLeast_ftsOpen _ _ _ _ _) (by decide)
  · intro path
    exact boundaryHashAtLeast_zero _ _

end SphincsSecurity.Concrete
