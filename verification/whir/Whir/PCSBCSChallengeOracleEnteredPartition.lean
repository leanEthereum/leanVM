import Whir.PCSBCSChallengeOracleEntries

/-! Whole packets for every admitted live caller prefix at the public boundary.
The same physical source block belongs to at most one packet; all remaining
observer and simulator keys stay in the garbage summand. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Whir.PCSBCSChallengeOracle.EnteredPacket
open Concrete Protocol CausalGame CausalProbability WHIRHistory PCSBCSRounds
open FiatShamirGame DuplexModeGame DuplexFraming RawOracleCoupling

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}

abbrev Block (packet : EnteredPacket p Q iv boundary) :=
  Fin (blocks (rawWidth packet.2.coord))

def encode (block : Sigma (Block (p := p) (Q := Q) (iv := iv) (boundary := boundary))) :
    PublicCompressionCouplingMixed.Key Q := .inr (block.1.2.2.key block.2)

/-- Equal continuation keys force equal whole packets, even if their caller
prefix data was selected adaptively and differs between honest invocations. -/
theorem encode_injective : Function.Injective
    (encode (p := p) (Q := Q) (iv := iv) (boundary := boundary)) := by
  intro a b same
  rcases a with ⟨a,ai⟩
  rcases b with ⟨b,bi⟩
  have keys : a.2.2.key ai = b.2.2.key bi := Sum.inr.inj same
  have coordinates := constructionKey_injective Q iv (a.2.2.valid ai) (b.2.2.valid bi)
    (a.2.2.pathBound ai) (b.2.2.pathBound bi) keys
  have history := congrArg FiatShamirGame.Coordinate.history coordinates
  dsimp only [SourcePacket.coordinate,WHIRCallerPrefix.outputKeyFrom] at history
  have firstCoordinates : a.2.2.coordinate a.2.firstBlock = b.2.2.coordinate b.2.firstBlock := by
    change FiatShamirGame.Coordinate.mk _ (.output 0) = FiatShamirGame.Coordinate.mk _ (.output 0)
    exact congrArg (fun h => FiatShamirGame.Coordinate.mk h (.output 0)) history
  have castKey (x y : FiatShamirGame.Coordinate) (hx : pathCost x ≤ Q) (hy : pathCost y ≤ Q)
      (equal : x = y) : constructionKey Q iv x hx = constructionKey Q iv y hy := by
    cases equal
    rfl
  have firstKeys : a.firstKey = b.firstKey :=
    castKey _ _ (a.2.2.pathBound a.2.firstBlock) (b.2.2.pathBound b.2.firstBlock) firstCoordinates
  have packetsSame : a = b := firstKey_injective firstKeys
  cases packetsSame
  have indexSame := (SourcePacket.distinct_history_keys a.2.2 a.2.2 ai bi keys).2
  have blocksSame : ai = bi := Fin.ext indexSame
  cases blocksSame
  rfl

noncomputable instance : DecidableEq (EnteredPacket p Q iv boundary) := Classical.decEq _

noncomputable def partition :
    Partition (PublicCompressionCouplingMixed.Key Q) (EnteredPacket p Q iv boundary) Block :=
  partitionOfInjection encode encode_injective

theorem recognize_block (packet : EnteredPacket p Q iv boundary) (block : Block packet) :
    (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).recognize
      (.inr (packet.2.2.key block)) = some ⟨packet,block⟩ :=
  (partition (p := p) (Q := Q) (iv := iv) (boundary := boundary)).recognize_encode ⟨packet,block⟩

#print axioms encode_injective
#print axioms recognize_block
end Whir.PCSBCSChallengeOracle.EnteredPacket
