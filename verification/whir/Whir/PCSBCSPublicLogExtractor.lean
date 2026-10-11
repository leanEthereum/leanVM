import Whir.PCSBCSSourcePrimitiveRootBudget
import Whir.PCSBCSPublicRootExtractor

/-! The executable public-log extractor scans the actual chronological inputs,
selects the first matching CV/height/full-image/occupied address, and runs the
real full-root Gao decoder once. It does not extract unrelated root tables.
Source acceptance and the finite-game failure bound remain separate obligations. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicLogExtractor
open Concrete Protocol FiatShamirGame DuplexFraming DuplexPublicSimulator
open PCSBCSMerkleRootCache PCSBCSSourceRootReferences

variable (p : ParameterBounds.Profile) (Q : Nat)
    (layout : PublicLog → Node → WHIRCallerClaims.CallerLayout)
    (savedAt : PublicLog → Node → AnchoredHeaderCodec.Record)
    (entry : PublicLog → Node → FramedHistory)
    (answers : PublicLog → Node → FiatShamirGame.Coordinate → Digest32)
    (headers : PublicLog → Node → AnchoredHeaderRoots.Public)
    (target : AnchoredHeaderCodec.Record)

def selectPrefix : PublicLog → Option PublicLog
  | [] => none
  | (input,_) :: queryPrefix =>
    match selectPrefix queryPrefix with
    | some captured => some captured
    | none =>
      if (PCSBCSSourcePrimitiveRootBudget.references p Q layout savedAt entry answers headers
          queryPrefix input).any (fun ref => decide
            (cacheKey ref.root ref.shape = cacheKey target.root (initialShape target.shape))) then
        some queryPrefix
      else none

/-- Later primitive queries cannot replace the already captured prefix or
supply new preimages to the initial word extraction. -/
theorem selectPrefix_preserves (log captured : PublicLog) (input : Node) (digest : Digest32)
    (known : selectPrefix p Q layout savedAt entry answers headers target log = some captured) :
    selectPrefix p Q layout savedAt entry answers headers target ((input,digest)::log) =
      some captured := by
  simp only [selectPrefix,known]

def extract {m : Nat} (lanes : Nat) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (anchorPoint : Array E) (anchorValue : E)
    (log : PublicLog) : Option (CausalGame.Witness (ParameterBounds.config p) lanes) := do
  let captured ← selectPrefix p Q layout savedAt entry answers headers target log
  PCSBCSPublicRootExtractor.extract p lanes family points anchorPoint anchorValue captured target

/-- Every actual returned word explains every original claim and the anchor.
No collision assumption or final success-probability premise is used here. -/
theorem output_explains {m : Nat} (lanes : Nat) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (anchorPoint : Array E) (anchorValue : E)
    (log : PublicLog) (w : CausalGame.Witness (ParameterBounds.config p) lanes)
    (returned : extract p Q layout savedAt entry answers headers target lanes family points
      anchorPoint anchorValue log = some w) :
    ∃ captured, selectPrefix p Q layout savedAt entry answers headers target log = some captured ∧
      PCSRewindSource.ExplainsOriginal (ParameterBounds.config p) lanes
        (freeze captured target.root (initialShape target.shape)).raw
        family points anchorPoint anchorValue w := by
  obtain ⟨captured,selected,decoded⟩ := Option.bind_eq_some_iff.mp returned
  exact ⟨captured,selected,PCSBCSPublicRootExtractor.output_explains p lanes family points
    anchorPoint anchorValue captured target w decoded⟩

#print axioms selectPrefix_preserves
#print axioms output_explains
end Whir.PCSBCSPublicLogExtractor
