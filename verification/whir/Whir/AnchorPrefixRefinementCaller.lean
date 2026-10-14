import Whir.AnchorPrefixRefinement

/-! The anchored source caller refines the actual family, point claims, and final immutable occupied-prefix anchor batch. -/
namespace Whir.AnchorPrefixRefinement
open Concrete Protocol CausalGame AnchoredHeaderCodec AnchoredPhysicalAnchor

private def batchStep (lambda : E) (s : Claim × E) (claim : Claim) : Claim × E :=
  (⟨weightGlue s.1.weight claim.weight s.2, s.1.value+s.2*claim.value⟩, s.2*lambda)

private lemma batch_power (lambda : E) (claims : List Claim) (s : Claim × E) :
    (claims.foldl (batchStep lambda) s).2 = s.2*lambda^claims.length := by
  induction claims generalizing s with
  | nil => simp
  | cons a tail ih => simp only [List.foldl_cons, ih, batchStep, List.length_cons, pow_succ]; ring

lemma batchClaims_push (width : Nat) (claims : Array Claim) (claim : Claim) (lambda : E) :
    batchClaims width (claims.push claim) lambda =
      ⟨weightGlue (batchClaims width claims lambda).weight claim.weight (lambda^claims.size),
        (batchClaims width claims lambda).value+lambda^claims.size*claim.value⟩ := by
  have form (a : Array Claim) : batchClaims width a lambda =
      (a.toList.foldl (batchStep lambda) (⟨tab width fun _ => 0,0⟩,1)).1 := by
    unfold batchClaims
    simp only [Array.forIn_pure_yield_eq_foldl, pure_bind, Array.foldl_toList]
    rfl
  simp only [form, Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil, batchStep]
  have power := batch_power lambda claims.toList (⟨tab width fun _ => 0,0⟩,1)
  simp only [one_mul, Array.length_toList] at power
  rw [power]

noncomputable def anchoredClaims {m : Nat} (c : Config) (record : Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) : Array Claim :=
  (RingPCSGame.transformedClaims (2^c.logN) family points seed).push
    ⟨CommitmentAnchor.weight c record.shape.lanes record.point.toArray, record.value⟩

lemma initialClaim_dense {m : Nat} (c : Config) (record : Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) :
    AnchoredPhysicalAnchor.initialClaim record family points seed lambda =
      (batchClaims (2^c.logN) (anchoredClaims c record family points seed) lambda).value := by
  rw [anchoredClaims, batchClaims_push]
  simp only [AnchoredPhysicalAnchor.initialClaim]
  rw [WHIRNativeArithmetic.initialClaim_eq_batch_value (2^c.logN)]
  simp [RingPCSGame.transformedClaims, Nat.add_comm]

lemma callerAt_dense {m : Nat} (c : Config) (record : Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E)
    (valid : record.Valid) (hN : record.shape.logN = c.logN)
    (hB : record.shape.logBatch = c.folds[0]!)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (x : Array E) (hx : x.size = c.logN) :
    callerAt record family points seed lambda x =
      Concrete.mle (batchClaims (2^c.logN) (anchoredClaims c record family points seed) lambda).weight x := by
  rw [anchoredClaims, batchClaims_push]
  rw [AccumulatedTerminalAlgebra.mle_weightGlue _ _ _ _
    (by simp [hx]) (by simp [CommitmentAnchor.weight])]
  rw [callerAt, anchorAt_dense c record.shape record.point.toArray x hN hB
    ⟨by have := valid.1.2.2.2.2.1; omega, valid.1.2.2.2.2.2⟩ valid.1.1
    (by simpa using valid.2.2) (hx.trans hN.symm)]
  have old := SuccinctRingGroups.sourceStackWeightAt_eq_batch_mle family points seed lambda x
    (by simpa [hx] using familyShape) (by simpa [hx] using pointShapes)
  rw [old]
  simp only [RingPCSGame.transformedClaims, Array.size_append, Array.size_map]
  simp [hx, Nat.add_comm]

/-- The native terminal equality now includes the actual supported anchor, with the same final batching power as its retained value. -/
theorem sourceVerify_refines {m : Nat} (record : Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (seed : RingPCSGame.Prefix) (lambda : E) (c : Config) (ch : Challenges)
    (proof : Opening) (root : Oracle)
    (valid : record.Valid) (hN : record.shape.logN = c.logN)
    (hB : record.shape.logBatch = c.folds[0]!)
    (familyShape : SuccinctRingWeight.FamilyShape c.logN family)
    (pointShapes : ∀ i : Fin points.size, SuccinctPointWeight.Shape c.logN points[i])
    (weightShape : shapeValid c record.shape.lanes
      (batchClaims (2^c.logN) (anchoredClaims c record family points seed) lambda).weight = true)
    (rootShape : oracleValid root (2^(c.logN-c.folds[0]!+c.rates[0]!)) record.shape.lanes = true)
    (roots : WHIRNativeArithmetic.RootShapes c proof)
    (authenticated : WHIRNativeArithmetic.AuthenticatedRows c ch proof root)
    (success : AnchoredPhysicalAnchor.sourceVerify record family points seed lambda c ch proof = .ok ()) :
    Protocol.verify c ch record.shape.lanes root
      (batchClaims (2^c.logN) (anchoredClaims c record family points seed) lambda).weight
      (batchClaims (2^c.logN) (anchoredClaims c record family points seed) lambda).value proof = .ok () := by
  have refined := WHIRNativeArithmetic.nativeVerify_refines c ch record.shape.lanes
    (AnchoredPhysicalAnchor.initialClaim record family points seed lambda)
    (callerAt record family points seed lambda) proof _ root weightShape rootShape roots authenticated
    (callerAt_dense c record family points seed lambda valid hN hB familyShape pointShapes) success
  rwa [initialClaim_dense] at refined

#print axioms initialClaim_dense
#print axioms callerAt_dense
#print axioms sourceVerify_refines

end Whir.AnchorPrefixRefinement
