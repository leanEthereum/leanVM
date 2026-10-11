import Whir.PublicCompressionCouplingCache

/-! Actual mixed coordinates identify their public primitive node. The seed
case keeps the full chosen node; the terminal case retains the complete raw key
and its actual seed-tree witness. This is independent of output-collision or
observer restrictions. -/
namespace Whir.PublicCompressionCouplingRecognition
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator
open PublicCompressionCouplingMixed

inductive CoordinateWitness (Q : Nat) (seed : Seed) (input : Node) : Key Q → Prop where
  | fallback : CoordinateWitness Q seed input (.inl input)
  | terminal (key : RawKey Q) (rest : List Node)
      (complete : Complete (input::rest))
      (tree : Tree (compressionOf seed) input.cv rest)
      (extracted : extract (input::rest) = some (expandKey key)) :
      CoordinateWitness Q seed input (.inr key)

 theorem CoordinateWitness.node_unique {Q : Nat} {seed : Seed} {a b : Node} {key : Key Q}
    (left : CoordinateWitness Q seed a key) (right : CoordinateWitness Q seed b key) : a=b := by
  cases left with
  | fallback => cases right; rfl
  | terminal raw rest complete tree extracted =>
    cases right with
    | terminal raw' rest' complete' tree' extracted' =>
      exact (complete_key_unique complete complete' tree tree'
        (extracted.trans extracted'.symm)).1

 theorem privateKey_coordinateWitness {Q : Nat} {log : PublicLog} {input : Node}
    {key : RawKey Q} (seed : Seed) (auth : NonterminalAuthentic seed log)
    (found : privateKey Q log input = some key) :
    CoordinateWitness Q seed input (.inr key) := by
  obtain ⟨rest,complete,tree,extracted⟩ := privateKey_seed_tree seed auth found
  exact CoordinateWitness.terminal key rest complete tree extracted

 theorem plan_prefix_evaluate (c : Compression) (iv : Digest32) (coordinate : Coordinate) :
    evalPlan c iv (DuplexEncoding.plan coordinate).dropLast =
      evalHistory c iv coordinate.history := by
  change evalPlan c iv
    ((([(ByteCodec.pairBytes (coordinate.history.domain,coordinate.history.statement),
      UInt64.ofNat (2^56))] ++ coordinate.history.frames.flatMap DuplexEncoding.framePlan) ++
      [DuplexEncoding.terminalPlan coordinate.terminal]).dropLast) = _
  rw [List.dropLast_concat]
  change evalPlan c (seed c iv coordinate.history.domain coordinate.history.statement).cv
    (coordinate.history.frames.flatMap DuplexEncoding.framePlan) = _
  exact framesPlan_evaluate c _ _

 theorem construction_coordinateWitness (Q : Nat) (seedTable : Seed) (iv : Digest32)
    (coordinate : Coordinate) (valid : DuplexEncoding.Admissible coordinate)
    (budget : pathCost coordinate ≤ Q) :
    CoordinateWitness Q seedTable
      (terminalNode (evalHistory (compressionOf seedTable) iv coordinate.history) coordinate.terminal)
      (.inr (constructionKey Q iv coordinate budget)) := by
  let c := compressionOf seedTable
  let traced := traceHistory c iv coordinate.history
  have stateEq := traceHistory_cv c iv coordinate.history
  apply CoordinateWitness.terminal (constructionKey Q iv coordinate budget) traced.nodes
  · simpa only [coordinateTree,stateEq] using coordinateTree_complete c iv coordinate valid.1
  · cases terminalEq : coordinate.terminal <;>
      simpa only [terminalEq,terminalNode,stateEq] using
        (traceHistory_valid c iv coordinate.history valid.1).1
  · simpa only [coordinateTree,stateEq,expand_constructionKey] using
      coordinateTree_key c iv coordinate valid

/-- A public record carries its actually consumed mixed coordinate. A repeated
record carries the same old coordinate, not a new private RO request. -/
def Witnessed (Q : Nat) (seed : Seed) (cache : Key Q → Option Digest32)
    (log : PublicLog) : Prop :=
  ∀ input answer, (input,answer) ∈ log →
    ∃ key, CoordinateWitness Q seed input key ∧ cache key = some answer

/-- Cache answer injectivity plus actual coordinate witnesses yields the
simulator's public no-output-collision fact, including recognized RO terminals. -/
 theorem Witnessed.no_outputCollision {Q : Nat} {seed : Seed} {cache : Key Q → Option Digest32}
    {log : PublicLog} (witnessed : Witnessed Q seed cache log)
    (injective : ∀ a b d, cache a = some d → cache b = some d → a=b) :
    ¬OutputCollision log := by
  rintro ⟨a,b,d,ha,hb,different⟩
  obtain ⟨ka,left,hitA⟩ := witnessed a d ha
  obtain ⟨kb,right,hitB⟩ := witnessed b d hb
  have keys := injective ka kb d hitA hitB
  subst kb
  exact different (CoordinateWitness.node_unique left right)

#print axioms CoordinateWitness.node_unique
#print axioms Witnessed.no_outputCollision
end Whir.PublicCompressionCouplingRecognition
