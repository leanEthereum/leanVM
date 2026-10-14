import Whir.WHIRNativeErasure

namespace Whir.WHIRNativeErasure
open Concrete Protocol WHIRPhysicalErasure WHIRNativeArithmetic

/-- Proof-only restoration changes present ghost oracles, never their presence or any physical payload. The table is indexed by the next code level. -/
def restoreOracles (proof : Opening) (lookup : Nat → Oracle) : Opening :=
  {proof with levels := Array.ofFn fun i : Fin proof.levels.size =>
    {proof.levels[i] with nextOracle := proof.levels[i].nextOracle.map fun _ => lookup (i.val + 1)}}

theorem eraseOracles_restore (proof : Opening) (lookup : Nat → Oracle) :
    eraseOracles (restoreOracles proof lookup) = eraseOracles proof := by
  cases proof with
  | mk initial levels residual tailMessages =>
    simp only [restoreOracles, eraseOracles, Array.map_ofFn, Function.comp_def, eraseLevel,
      Option.map_map]
    congr 1
    apply Array.ext
    · simp
    · intro i hi hj
      simp [eraseLevel]

theorem nativeVerify_restored (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E)
    (callerAt : Array E → E) (proof : Opening) (lookup : Nat → Oracle) :
    nativeVerify c ch lanes initialClaim callerAt (restoreOracles proof lookup) =
      nativeVerify c ch lanes initialClaim callerAt proof := by
  rw [← nativeVerify_erased c ch lanes initialClaim callerAt (restoreOracles proof lookup),
    eraseOracles_restore, nativeVerify_erased]

theorem sourceVerify_restored {m : Nat} (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (lanes : Nat) (proof : Opening) (lookup : Nat → Oracle) :
    sourceVerify family points seed lambda c ch lanes (restoreOracles proof lookup) =
      sourceVerify family points seed lambda c ch lanes proof :=
  nativeVerify_restored c ch lanes (initialClaim family points seed lambda)
    (SuccinctRingGroups.sourceStackWeightAt family points seed lambda) proof lookup

end Whir.WHIRNativeErasure
