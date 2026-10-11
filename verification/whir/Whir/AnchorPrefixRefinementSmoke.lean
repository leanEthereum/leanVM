import Whir.AnchoredPhysicalAnchor
import Whir.CommitmentAnchor

/-! Executable source DP compared with the existing dense encoder, including nonzero high coordinates and the full-cube branch. -/
namespace Whir.AnchorPrefixRefinementSmoke
open Concrete Protocol AnchoredPhysicalAnchor AnchoredHeaderCodec

def config : Config := ⟨5, #[3], #[1], #[1], #[0]⟩
def shape (lanes : Nat) : Shape := ⟨5, 3, 1, lanes⟩
def point (salt : Nat) : Array E := Array.ofFn fun j : Fin 5 =>
  ⟨UInt64.ofNat (salt+3*j.val), UInt64.ofNat (salt+j.val+7), 11⟩

def smoke : IO Unit := do
  for lanes in [1, 3, 8] do
    let actual := anchorAt (shape lanes) (point 7) (point 23)
    let dense := Concrete.mle (CommitmentAnchor.weight config lanes (point 7)) (point 23)
    unless actual == dense do
      throw (IO.userError s!"anchor source DP differs from dense occupied weight: lanes={lanes}")
    let symbolic := AnchorPrefixRefinementArith.anchorAtWith AnchorPrefixRefinementArith.rows
      (shape lanes) 5 (fun j => .constant ((point 7)[j]!)) (fun j => .constant ((point 23)[j]!))
    unless symbolic.eval == actual do
      throw (IO.userError s!"shared Rows arithmetic differs from Native: lanes={lanes}")
    IO.println s!"anchor source Native/Rows DP = dense occupied weight: lanes={lanes}, logN=5, logBatch=3"

end Whir.AnchorPrefixRefinementSmoke

def main : IO Unit := Whir.AnchorPrefixRefinementSmoke.smoke
