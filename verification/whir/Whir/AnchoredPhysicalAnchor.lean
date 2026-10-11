import Whir.AnchorPrefixRefinementArith
import Whir.WHIRNativeArithmetic

/-! Source hand-port of 32c `anchor.rs::anchor_eq_at` and `stack_open::OpeningWeight`. The prefix recurrence never allocates a cube or evaluates the full equality product for missing lanes. Its dense semantic refinement is a separate mathematical theorem, not an evaluator argument accepted by the executable verifier. -/
namespace Whir.AnchoredPhysicalAnchor
open Concrete Protocol AnchoredHeaderCodec

abbrev PrefixState := AnchorPrefixRefinementArith.PrefixStateWith E

def prefixStep (shape : Shape) (r x : Array E) (j : Nat) (s : PrefixState) : PrefixState :=
  AnchorPrefixRefinementArith.prefixStepWith AnchorPrefixRefinementArith.native shape
    (fun i => r[i]!) (fun i => x[i]!) j s

def anchorAt (shape : Shape) (r x : Array E) : E :=
  AnchorPrefixRefinementArith.anchorAtWith AnchorPrefixRefinementArith.native shape r.size
    (fun i => r[i]!) (fun i => x[i]!)

theorem native_factor (r x : E) : E.add (E.add r x) E.one = 1+r+x := by
  change (r+x)+(1 : E) = 1+r+x
  ring

theorem native_eq_factor (acc r x : E) :
    E.add (E.mul acc (E.add r x)) acc = acc*(1+r+x) := by
  change acc*(r+x)+acc = acc*(1+r+x)
  ring

/-- Normalized equality product notation for the operational source fold. -/
theorem anchorAt_unfold (shape : Shape) (r x : Array E) :
    anchorAt shape r x =
      if shape.lanes = 2^shape.logBatch then
        (List.range r.size).foldl (fun (acc : E) j => acc*((1 : E)+r[j]!+x[j]!)) (1 : E)
      else
        (List.range (shape.logN-shape.logBatch)).foldl
          (fun (acc : E) j => acc*((1 : E)+r[j]!+x[j]!)) (1 : E) *
        ((List.range shape.logBatch).foldl (fun s j => prefixStep shape r x j s) {}).partial := by
  unfold anchorAt AnchorPrefixRefinementArith.anchorAtWith AnchorPrefixRefinementArith.eqEvalWith
  simp only [AnchorPrefixRefinementArith.native, native_eq_factor]
  simp only [← FieldModel.E_one_def]
  rfl

def initialClaim {m : Nat} (record : Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E) : E :=
  WHIRNativeArithmetic.initialClaim family points seed lambda + lambda^(points.size+1)*record.value

def callerAt {m : Nat} (record : Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E) (x : Array E) : E :=
  SuccinctRingGroups.sourceStackWeightAt family points seed lambda x +
    lambda^(points.size+1)*anchorAt record.shape record.point.toArray x

/-- The family takes power zero, existing point claims powers 1..points.size, and the retained anchor the final power. No additional random point, transcript reset or full-cube PointClaim is substituted. -/
def sourceVerify {m : Nat} (record : Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (seed : RingPCSGame.Prefix) (lambda : E)
    (c : Config) (ch : Challenges) (proof : Opening) : Except String Unit :=
  WHIRNativeArithmetic.nativeVerify c ch record.shape.lanes (initialClaim record family points seed lambda)
    (callerAt record family points seed lambda) proof

end Whir.AnchoredPhysicalAnchor
