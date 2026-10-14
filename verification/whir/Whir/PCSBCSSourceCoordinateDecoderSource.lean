import Whir.PCSBCSSourceCoordinateDecoder
import Whir.PCSBCSChallengeOracleSource

/-! The source boundary is explicit: admitted normalized frames and terminals,
a fixed PARAM_IV, a live caller entry and the source machine's `Represents`
and successful guarded squeeze. No universal Lean/Rust equality is asserted. -/
namespace Whir.PCSBCSSourceCoordinateDecoder
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator

/-- Canonical source syntax is additional to supermode completeness. A foreign
chosen-CV compression tree is not silently declared a duplex source history. -/
def SourceShape (iv : Digest32) (ns : List Node) (q : Coordinate) : Prop :=
  Complete ns ∧ Anchored iv ns ∧ DuplexEncoding.Admissible q ∧ rawPlan ns = DuplexEncoding.plan q

theorem decode_of_sourceShape {Q : Nat} {iv : Digest32} {ns : List Node}
    {key : RawKey Q} {q : Coordinate} (shape : SourceShape iv ns q)
    (extracted : extract ns = some (expandKey key)) : decode iv key = some q := by
  obtain ⟨complete,anchored,valid,plan⟩ := shape
  have canonical := extract_anchored iv ns complete anchored
  rw [plan] at canonical
  have same : expandKey key = modeKey iv q := Option.some.inj (extracted.symm.trans canonical)
  exact (decode_iff iv key q).mpr ⟨valid,same⟩

theorem coordinateTree_sourceShape (c : Compression) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) : SourceShape iv (coordinateTree c iv q) q :=
  ⟨coordinateTree_complete c iv q valid.1, coordinateTree_anchored c iv q valid,
    valid, coordinateTree_plan c iv q⟩

/-- Completeness from ordinary functional collision-free public records. The
source-shape premise is syntactic; public links are independently witnessed by
actual compression records, not by a history reconstruction oracle. -/
theorem recover_from_publicBody {Q : Nat} {iv : Digest32} {log : PublicLog}
    {input : Node} {rest : List Node} {q : Coordinate}
    (functional : Functional log) (clean : ¬OutputCollision log)
    (fresh : lookup log input = none) (terminal : isTerminal input)
    (body : PublicBody log input.cv rest) (shape : SourceShape iv (input::rest) q)
    (budget : log.length+1 ≤ Q) : recover Q iv log input = some q := by
  have tree := recognized_complete functional clean terminal body
  obtain ⟨key,found,extracted⟩ := privateKey_of_recognized fresh tree budget
  simp only [recover,found,Option.bind_some]
  exact decode_of_sourceShape shape extracted

/-- Entry is a variable, including its data-valued domain, statement and frames;
this is not a decoder specialized to one caller prefix. -/
theorem decode_sourcePacket {p : ParameterBounds.Profile} {Q : Nat}
    {entry : FramedHistory}
    {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : PCSBCSChallengeOracle.SourcePacket p Q seedIV entry q)
    (block : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q))) :
    decode seedIV (packet.key block) = some (packet.coordinate block) :=
  decode_constructionKey Q seedIV (packet.coordinate block) (packet.valid block) (packet.pathBound block)

/-- Source packet recovery from an actual public log, for every admitted entry.
The recognized tree and public-log budget are genuine endpoint conditions. -/
theorem recover_sourcePacket {p : ParameterBounds.Profile} {Q : Nat}
    {entry : FramedHistory}
    {q : CausalProbability.Coordinate (ParameterBounds.config p)}
    (packet : PCSBCSChallengeOracle.SourcePacket p Q seedIV entry q)
    (block : Fin (PCSBCSChallengeOracle.blocks (PCSBCSRounds.rawWidth q)))
    (c : Compression) (log : PublicLog) (input : Node)
    (fresh : lookup log input = none)
    (tree : recognized log input = some (coordinateTree c seedIV (packet.coordinate block)))
    (budget : log.length+1 ≤ Q) :
    recover Q seedIV log input = some (packet.coordinate block) :=
  recover_of_coordinateTree c (packet.coordinate block) (packet.valid block) fresh tree budget

#print axioms decode_of_sourceShape
#print axioms recover_from_publicBody
#print axioms decode_sourcePacket
#print axioms recover_sourcePacket
end Whir.PCSBCSSourceCoordinateDecoder
