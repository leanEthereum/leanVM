import XmssSecurity.Proof.IdealStatement

/-! The WOTS chain walk: the first-order form of the statement's monadic `chainWalk`, used by the proof's pure cache replays and extraction arguments. -/

namespace XmssSecurity.Wots

/-- Walk `steps` edges of a domain-separated hash chain starting at `position`. -/
def walk {α : Type} (step : Nat → α → α) : Nat → Nat → α → α
  | _, 0, value => value
  | position, steps + 1, value => step (position + steps) (walk step position steps value)

end XmssSecurity.Wots
